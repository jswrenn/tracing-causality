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
///     let subscriber = Registry::default().with(tracing_causality::Layer);
///     let (subscriber, causality) = tracing_causality::for_subscriber(subscriber);
///     subscriber.init()
/// }
/// ```
pub struct Causality<S>
where
    S: for<'span> LookupSpan<'span>,
{
    subscriber:
        Arc<dyn for<'span> LookupSpan<'span, Data = <S as LookupSpan<'span>>::Data>>,
    _type: PhantomData<S>,
}

/// Produce a `Causality` from a given subscriber.
/// ## Example
/// ```
/// use tracing_causality::Causality;
/// use tracing_subscriber::{prelude::*, registry::Registry};
///
/// fn main() {
///     let subscriber = Registry::default().with(tracing_causality::Layer);
///     let (subscriber, causality) = tracing_causality::for_subscriber(subscriber);
///     subscriber.init()
/// }
/// ```
pub fn for_subscriber<S>(
    subscriber: S,
) -> (Arc<dyn Subscriber + 'static>, Causality<S>)
where
    S: Subscriber + for<'span> LookupSpan<'span>  + 'static,
{
    let subscriber: Arc<S> = Arc::new(subscriber);
    let causality = Causality::from_subscriber(subscriber.clone());
    (subscriber, causality)
}

impl<S> Causality<S>
where
    S: for<'span> LookupSpan<'span> + 'static,
{
    fn from_subscriber(subscriber: Arc<S>) -> Causality<S> {
        Causality {
            subscriber,
            _type: PhantomData,
        }
    }

    pub fn into_subscriber(
        &self,
    ) -> Arc<dyn for<'span> LookupSpan<'span, Data = <S as LookupSpan<'span>>::Data>>
    {
        self.subscriber.clone()
    }

    /// Produce a causality graph of the given `id`.
    ///
    /// Returns both a [`Trace`] rooted at `id`, and a stream of updates
    /// that affect the produced trace, but occurred after the invocation of this
    /// method.
    pub fn trace(&self, id: &Id, update_capacity: usize) -> Option<(Trace, Updates)> {
        let (sender, updates) = channel::bounded(id.clone(), update_capacity);
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
                    ).insert(sender.to_owned());
                }
            }
        }
        Some((trace, updates))
    }
}

// XXX(jswrenn): invoking `as_ref` ICEs rustc :'(
// impl<S> AsRef<dyn for<'span> LookupSpan<'span, Data = <S as LookupSpan<'span>>::Data> + Send + Sync> for Causality<S>
// where
//     S: for<'span> LookupSpan<'span> + Send + Sync + 'static,
// {
//     fn as_ref(&self) -> &(dyn for<'span> LookupSpan<'span, Data = <S as LookupSpan<'span>>::Data> + Send + Sync + 'static) {
//         self.subscriber.as_ref()
//     }
// }

/// An update that should be applied to a [`Trace`].
#[derive(Clone, Debug, PartialEq, Eq)]
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

impl Layer {
    /// Record that a span `follows_from` itself.
    pub(crate) fn on_follows_self<S>(&self, span_id: &Id, ctx: Context<'_, S>)
    where
        S: Subscriber + for<'span> LookupSpan<'span>,
    {
        use data::IndirectCauses;
        let span = ctx.span(span_id).expect("Span not found, this is a bug");
        let mut span_data = span.extensions_mut();

        // 1. insert `consequence` as an indirect consequence of `cause`
        if let Some(consequences) = span_data.get_mut::<Consequences>() {
            consequences.indirect.insert(span_id.to_owned());
        } else {
            span_data.insert(Consequences::with_indirect(span_id.to_owned()));
        }

        // 2. insert `cause` as an indirect cause of `consequence`
        if let Some(follows_from) = span_data.get_mut::<IndirectCauses>() {
            follows_from.add_cause(span_id.to_owned());
        } else {
            span_data.insert(IndirectCauses::with_cause(span_id.to_owned()));
        }

        if let Some(listeners) = span_data.get_mut::<Listeners>() {
            // 3. notify causes's listeners that it indirectly lead to `consequence`
            channel::Sender::broadcast(
                listeners,
                Update::Indirect {
                    cause: span_id.clone(),
                    consequence: span_id.clone(),
                },
            );
        }
    }
}

impl<S> tracing_subscriber::layer::Layer<S> for Layer
where
    S: Subscriber + for<'span> LookupSpan<'span>,
{
    fn on_new_span(&self, _: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let span = ctx.span(id).expect("Span not found, this is a bug");

        if let Some(direct_cause) = span.parent() {
            let mut cause_extensions = direct_cause.extensions_mut();
            let id = id.to_owned();
            // 1. notify listeners, if any, that `id` was is a consequence
            if let Some(listeners) = cause_extensions.get_mut::<Listeners>() {
                channel::Sender::broadcast(
                    listeners,
                    Update::Direct {
                        cause: direct_cause.id(),
                        consequence: id.clone(),
                    },
                );
            }

            // 2. register that `cause` directly lead to `consequence`.
            if let Some(consequences) = cause_extensions.get_mut::<Consequences>() {
                consequences.direct.insert(id);
            } else {
                cause_extensions.insert(Consequences::with_direct(id));
            }
        }
    }

    fn on_follows_from(&self, consequence_id: &Id, cause_id: &Id, ctx: Context<'_, S>) {
        use data::IndirectCauses;

        if cause_id == consequence_id {
            return self.on_follows_self(consequence_id, ctx);
        }

        let cause = ctx.span(cause_id).expect("Span not found, this is a bug");
        let consequence = ctx
            .span(consequence_id)
            .expect("Span not found, this is a bug");
        let mut cause_data = cause.extensions_mut();
        let mut consequence_data = consequence.extensions_mut();

        // 1. insert `consequence` as an indirect consequence of `cause`
        if let Some(consequences) = cause_data.get_mut::<Consequences>() {
            consequences.indirect.insert(consequence_id.to_owned());
        } else {
            cause_data.insert(Consequences::with_indirect(consequence_id.to_owned()));
        }

        // 2. insert `cause` as an indirect cause of `consequence`
        if let Some(follows_from) = consequence_data.get_mut::<IndirectCauses>() {
            follows_from.add_cause(cause_id.to_owned());
        } else {
            consequence_data.insert(IndirectCauses::with_cause(cause_id.to_owned()));
        }

        if let Some(listeners) = cause_data.get_mut::<Listeners>() {
            // 3. notify causes's listeners that it indirectly lead to `consequence`
            channel::Sender::broadcast(
                listeners,
                Update::Indirect {
                    cause: cause_id.clone(),
                    consequence: consequence_id.clone(),
                },
            );
            // 4. copy cause's listeners onto `consequence`
            crate::get_or_init_with::<Listeners, _>(&mut consequence_data, Listeners::new)
                .extend(listeners.iter().cloned());
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
                if cause_id == &id {
                    continue;
                }
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
            let mut parent_extensions = parent.extensions_mut();
            if let Some(consequences) = parent_extensions.get_mut::<Consequences>() {
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
                    indirect_causes,
                },
            );
        }
    }
}

#[cfg(test)]
mod test_util {
    use crate::{channel, Causality, Consequences};
    use tracing::{Id, Span};
    use tracing_subscriber::registry::LookupSpan;
    use tracing_subscriber::registry::SpanData;

    impl<S> Causality<S>
    where
        S: for<'span> LookupSpan<'span> + 'static,
    {
        pub(crate) fn updates_for(&self, span: &Span) -> channel::Updates {
            use crate::data::Listeners;
            let id = span.id().expect(&format!("span {:?} is not enabled", span));
            let data = self
                .subscriber
                .span_data(&id)
                .expect(&format!("span {:?} is not open", &id));
            let mut extensions = data.extensions_mut();
            let (sender, updates) = channel::bounded(id, 100);
            crate::get_or_init_with::<Listeners, _>(&mut extensions, Listeners::new).insert(sender);
            updates
        }

        pub(crate) fn direct_cause_of(&self, span: &Span) -> Option<Id> {
            let id = span.id().expect(&format!("span {:?} is not enabled", span));
            self.subscriber
                .span_data(&id)
                .expect(&format!("span {:?} is not open", id))
                .parent()
                .cloned()
        }

        pub(crate) fn assert_lacks_consequences(&self, span: &Span) {
            let id = span.id().expect(&format!("span {:?} is not enabled", span));
            assert_eq!(
                None,
                self.subscriber
                    .span_data(&id)
                    .expect(&format!("span {:?} is not open", &id))
                    .extensions()
                    .get::<Consequences>(),
                "span {:?} should lack {:?}",
                span,
                std::any::type_name::<Consequences>(),
            );
        }

        pub(crate) fn consequences_of(&self, span: &Span) -> Consequences {
            let id = span.id().expect(&format!("span {:?} is not enabled", span));
            self.subscriber
                .span_data(&id)
                .expect(&format!("span {:?} is not open", &id))
                .extensions()
                .get::<Consequences>()
                .expect(&format!(
                    "span {:?} lacks {:?}",
                    id,
                    std::any::type_name::<Consequences>()
                ))
                .clone()
        }
    }
}

#[cfg(test)]
mod test_layer {
    use tracing::trace_span;
    use tracing_subscriber::{prelude::*, registry::Registry};

    /// Tests the causality layer with on a trace involving a root without
    /// consequences.
    #[test]
    fn root() {
        let subscriber = Registry::default().with(crate::Layer);
        let (subscriber, causality) = crate::for_subscriber(subscriber);
        let _subscriber = subscriber.set_default();

        let root = trace_span!("root");
        let updates = causality.updates_for(&root);

        assert_eq!(
            causality.direct_cause_of(&root),
            None,
            "span `root` should not have any parent"
        );

        causality.assert_lacks_consequences(&root);

        let root_id = root.id().unwrap();
        drop(root);

        assert_eq!(
            updates.next(),
            Some(crate::Update::Drop {
                id: root_id,
                direct_cause: None,
                indirect_causes: vec![],
            }),
            "listeners on Span `root` should have been updated",
        );
    }

    /// Tests the causality layer on a trace involving a root with a single
    /// direct consequence.
    #[test]
    fn direct_consequence() {
        let subscriber = Registry::default().with(crate::Layer);
        let (subscriber, causality) = crate::for_subscriber(subscriber);
        let _subscriber = subscriber.set_default();

        let root = trace_span!("root");
        let root_id = root.id().unwrap();
        let root_updates = causality.updates_for(&root);

        causality.assert_lacks_consequences(&root);

        assert!(root_updates.is_empty());

        let consequence = root.in_scope(|| trace_span!("consequence"));
        let consequence_id = consequence.id().unwrap();
        let consequence_updates = causality.updates_for(&consequence);

        assert_eq!(
            root_updates.next(),
            Some(crate::Update::Direct {
                cause: root.id().unwrap(),
                consequence: consequence.id().unwrap(),
            }),
            "listeners on Span `root` should have been updated",
        );

        assert!(root_updates.is_empty());

        causality.assert_lacks_consequences(&consequence);

        assert_eq!(
            causality.direct_cause_of(&consequence),
            root.id(),
            "`consequence` should be the direct consequence of `root`"
        );

        assert_eq!(
            causality.consequences_of(&root),
            crate::Consequences::with_direct(consequence.id().unwrap()),
            "`consequence` should be the direct consequence of `root`"
        );

        drop(root);

        // `consequence` is still extant, so `root` isn't actually closed
        assert!(root_updates.is_empty());
        assert!(consequence_updates.is_empty());

        drop(consequence);

        // `consequence` is closed, because there are no other spans with the same id
        assert_eq!(
            consequence_updates.next(),
            Some(crate::Update::Drop {
                id: consequence_id.clone(),
                direct_cause: Some(root_id.clone()),
                indirect_causes: vec![],
            }),
            "listeners on Span `consequences` should have been updated",
        );

        // and, with `consequences` gone, `root` is actually closed, too
        assert_eq!(
            root_updates.next(),
            Some(crate::Update::Drop {
                id: root_id,
                direct_cause: None,
                indirect_causes: vec![],
            }),
            "listeners on Span `root` should have been updated",
        );

        assert!(root_updates.is_empty());
        assert!(consequence_updates.is_empty());
    }

    /// Tests the causality layer on a trace involving a root with a single
    /// indirect consequence.
    #[test]
    fn indirect_consequence() {
        let subscriber = Registry::default().with(crate::Layer);
        let (subscriber, causality) = crate::for_subscriber(subscriber);
        let _subscriber = subscriber.set_default();

        let a = trace_span!("a");
        let a_id = a.id().unwrap();
        let a_updates = causality.updates_for(&a);

        let b = trace_span!("b");
        let b_id = b.id().unwrap();
        let b_updates = causality.updates_for(&b);

        assert!(a_updates.is_empty());
        assert!(b_updates.is_empty());

        b.follows_from(&a_id);

        assert!(causality.consequences_of(&a).contains_indirect(&b_id));

        assert!(b_updates.is_empty());
        assert_eq!(
            a_updates.next(),
            Some(crate::Update::Indirect {
                cause: a_id.clone(),
                consequence: b_id.clone(),
            }),
            "listeners should have been updated that `b` indirectly follows from `a`",
        );
        assert!(a_updates.is_empty());

        drop(b);

        assert_eq!(
            a_updates.next(),
            Some(crate::Update::Drop {
                id: b_id.clone(),
                direct_cause: None,
                indirect_causes: vec![a_id],
            }),
            "listeners on `a` should have been notified that that `b` was dropped",
        );
    }

    /// Tests the causality layer on a trace involving a root with itself as an
    /// indirect consequence.
    #[test]
    fn cyclic_indirect_consequence() {
        let subscriber = Registry::default().with(crate::Layer);
        let (subscriber, causality) = crate::for_subscriber(subscriber);
        let _subscriber = subscriber.set_default();

        let a = trace_span!("a");
        let a_id = a.id().unwrap();
        let a_updates = causality.updates_for(&a);

        assert!(a_updates.is_empty());

        a.follows_from(&a);

        assert!(causality.consequences_of(&a).contains_indirect(&a_id));

        assert_eq!(
            a_updates.next(),
            Some(crate::Update::Indirect {
                cause: a_id.clone(),
                consequence: a_id.clone(),
            }),
            "listeners should have been updated that `a` indirectly follows from `a`",
        );

        assert!(a_updates.is_empty());

        drop(a);

        assert_eq!(
            a_updates.next(),
            Some(crate::Update::Drop {
                id: a_id.clone(),
                direct_cause: None,
                indirect_causes: vec![a_id],
            }),
            "listeners on `a` should have been notified that that `b` was dropped",
        );
    }
}
