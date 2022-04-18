use if_chain::if_chain;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Arc;
use tracing_core::span::{Attributes, Id};
use tracing_core::subscriber::Subscriber;
use tracing_subscriber::layer::Context;
use tracing_subscriber::registry::ExtensionsMut;
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::registry::SpanData;

mod channel;
pub use channel::Updates;

pub mod data;

pub use data::Consequences;
use data::Listeners;

/// A causality graph, rooted at a given [`Id`].
pub struct Trace {
    root: Id,
    adj: HashMap<Id, Consequences>,
}

impl Trace {
    /// The `Id` of the root span of this trace.
    pub fn root(&self) -> Id {
        self.root.to_owned()
    }

    /// The consequences of the given `id`.
    pub fn consequences(&self, id: &Id) -> Option<&Consequences> {
        self.adj.get(id)
    }

    /// Update [`Trace`] with the given [`Update`].
    pub fn apply(&mut self, update: Update) {
        match update {
            Update::Direct { cause, consequence } => {
                self.adj
                    .entry(cause)
                    .or_insert_with(Consequences::new)
                    .add_direct(consequence);
            }
            Update::Indirect { cause, consequence } => {
                self.adj
                    .entry(cause)
                    .or_insert_with(Consequences::new)
                    .add_indirect(consequence);
            }
            Update::Drop {
                id,
                direct_cause,
                indirect_causes,
            } => {
                let _ = self.adj.remove(&id);

                if let Some(direct_cause) = direct_cause {
                    if let Some(consequences) = self.adj.get_mut(&direct_cause) {
                        consequences.remove_direct(&id);
                    }
                }

                for indirect_cause in indirect_causes {
                    if let Some(consequences) = self.adj.get_mut(&indirect_cause) {
                        consequences.remove_direct(&id);
                    }
                }
            }
        }
    }
}

fn get_or_init_with<'a, T, F>(extensions: &'a mut ExtensionsMut<'_>, f: F) -> &'a mut T
where
    T: 'static + Send + Sync,
    F: FnOnce() -> T,
{
    if extensions.get_mut::<T>().is_none() {
        extensions.insert::<T>(f());
    }
    extensions.get_mut::<T>().unwrap()
}

/// Query the casual relationships of spans.
///
/// ## Example
/// ```
/// use tracing_causality::Causality;
/// use tracing_subscriber::{prelude::*, registry::Registry};
///
/// fn main() {
///     let subscriber = Registry::default().with(Layer);
///     let (subscriber, causality) = tracing_causality::for_subscriber(subscriber);
///     subscriber.init()
/// }
/// ```
pub struct Causality<S>
where
    S: for<'span> LookupSpan<'span> + Send + Sync,
{
    subscriber: Arc<dyn for<'span> LookupSpan<'span, Data = <S as LookupSpan<'span>>::Data> + Send + Sync>,
    _type: PhantomData<S>,
}

/// Produce a `Causality` from a given subscriber.
/// ## Example
/// ```
/// use tracing_causality::Causality;
/// use tracing_subscriber::{prelude::*, registry::Registry};
///
/// fn main() {
///     let subscriber = Registry::default().with(Layer);
///     let (subscriber, causality) = tracing_causality::for_subscriber(subscriber);
///     subscriber.init()
/// }
/// ```
pub fn for_subscriber<S>(subscriber: S)
  -> (Arc<dyn Subscriber + Send + Sync + 'static>, Causality<S>)
where
    S: Subscriber + for<'span> LookupSpan<'span> + Send + Sync + 'static,
{
    let subscriber: Arc<S> = Arc::new(subscriber);
    let causality = Causality::from_subscriber(subscriber.clone());
    (subscriber, causality)
}

impl<S> Causality<S>
where
    S: for<'span> LookupSpan<'span> + Send + Sync + 'static,
{
    fn from_subscriber(
        subscriber: Arc<S>,
    ) -> Causality<S> {
        Causality { 
          subscriber,
          _type: PhantomData,
        }
    }

    /// Produce a causality graph of the given `id`.
    ///
    /// Returns both a [`Trace`] rooted at `id`, and a stream of updates
    /// that affect the produced trace, but occured after the invocation of this
    /// method.
    pub fn trace(&self, id: &Id, update_capacity: usize) -> Option<(Trace, Updates)> {
        let (sender, updates) = channel::bounded(update_capacity);
        let mut trace = Trace {
            root: id.to_owned(),
            adj: HashMap::default(),
        };
        let mut queue = vec![id.to_owned()];
        while let Some(id) = queue.pop() {
            if_chain! {
                if let Some(span) = self.subscriber.span_data(&id);
                let mut extensions = span.extensions_mut();
                if let Some(consequences) = extensions.get_mut::<Consequences>();
                then {
                    let consequences = consequences.to_owned();
                    queue.extend(consequences.direct.iter().cloned());
                    trace.adj.insert(id, consequences);
                    // add the listener
                    get_or_init_with::<Listeners, _>(
                        &mut extensions,
                        Listeners::new
                    ).push(sender.to_owned());
                }
            }
        }
        Some((trace, updates))
    }
}

/// An update that should be applied to a [`Trace`].
#[derive(Clone)]
pub enum Update {
    /// Announces that `consequence` **directly** follows from `cause`.
    Direct { cause: Id, consequence: Id },
    /// Announces that `consequence` **indirectly** follows from `cause`.
    Indirect { cause: Id, consequence: Id },
    /// Announces that the span with `id` was dropped, and thus is no longer an
    /// extant consequence of `direct_cause` or `indirect_causes`.
    Drop {
        id: Id,
        direct_cause: Option<Id>,
        indirect_causes: Vec<Id>,
    },
}

/// A [tracing-subscriber layer] for monitoring the causal relationships between
/// tracing spans.
///
/// [tracing-subscriber layer]: tracing_subscriber::layer::Layer
pub struct Layer;

impl<S> tracing_subscriber::layer::Layer<S> for Layer
where
    S: Subscriber + for<'span> LookupSpan<'span> + Send + Sync,
{
    fn on_new_span(&self, _: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id).expect("Span not found, this is a bug");
        span.extensions_mut().insert(Consequences::new());

        if let Some(direct_cause) = span.parent() {
            let id = id.to_owned();
            let mut extensions = direct_cause.extensions_mut();

            // 1. notify listeners, if any, that `id` was dropped
            if let Some(listeners) = extensions.get_mut::<Listeners>() {
                channel::Sender::broadcast(
                    listeners,
                    Update::Direct {
                        cause: direct_cause.id(),
                        consequence: id.clone(),
                    },
                );
            }

            // 2. register that `cause` directly lead to `consequence`.
            if let Some(consequences) = extensions.get_mut::<Consequences>() {
                consequences.direct.insert(id);
            } else {
                extensions.insert(Consequences::with_direct(id));
            }
        }
    }

    fn on_follows_from(&self, consequence: &Id, cause: &Id, ctx: Context<'_, S>) {
        use data::IndirectCauses;
        let cause_id = cause;
        let consequence_id = consequence;
        let cause = ctx.span(cause).expect("Span not found, this is a bug");
        let consequence = ctx
            .span(consequence)
            .expect("Span not found, this is a bug");
        let mut cause_data = cause.extensions_mut();
        let mut consequence_data = consequence.extensions_mut();

        // 1. insert `consequence` as an indirect consequence of `cause`
        if let Some(consequences) = cause_data.get_mut::<Consequences>() {
            consequences.indirect.insert(consequence_id.to_owned());
        }

        // 2. insert `cause` as an indirect cause of `consequence`
        if let Some(follows_from) = consequence_data.get_mut::<IndirectCauses>() {
            follows_from.add_cause(cause_id.to_owned());
        } else {
            consequence_data.insert(IndirectCauses::with_cause(cause_id.to_owned()));
        }

        // 3. notify listeners, if any, that `cause` indirectly lead to `consequence`
        if let Some(listeners) = consequence_data.get_mut::<Listeners>() {
            channel::Sender::broadcast(
                listeners,
                Update::Indirect {
                    cause: cause_id.clone(),
                    consequence: consequence_id.clone(),
                },
            );
        }
    }

    fn on_close(&self, id: Id, ctx: Context<'_, S>) {
        use data::IndirectCauses;
        let span = ctx.span(&id).expect("Span not found, this is a bug");
        let mut extensions = span.extensions_mut();

        let mut indirect_causes = Vec::new();

        // 1. delete `id` as a consequence from each of its indirect causes
        if let Some(follows_from) = extensions.get_mut::<IndirectCauses>() {
            indirect_causes.extend(follows_from.causes.iter().cloned());

            for cause_id in &follows_from.causes {
                if let Some(cause) = ctx.span(cause_id) {
                    let mut extensions = cause.extensions_mut();
                    if let Some(consequences) = extensions.get_mut::<Consequences>() {
                        consequences.remove_indirect(&id);
                    }
                }
            }
        }

        let direct_cause = span.parent();

        // 2. delete `id` as a direct consequence of its parent
        if let Some(parent) = &direct_cause {
            if let Some(consequences) = parent.extensions_mut().get_mut::<Consequences>() {
                consequences.remove_direct(&id);
            }
        }

        // 3. notify listeners, if any, that `id` was dropped
        if let Some(listeners) = extensions.get_mut::<Listeners>() {
            channel::Sender::broadcast(
                listeners,
                Update::Drop {
                    id,
                    direct_cause: direct_cause.map(|c| c.id()),
                    indirect_causes: indirect_causes,
                },
            );
        }
    }
}
