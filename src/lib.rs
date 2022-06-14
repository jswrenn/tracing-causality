use std::collections::HashMap;
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

    /// The consequences of the `root` span of this trace.
    pub fn root_consequences(&self) -> &Consequences {
        self.adj.get(&self.root).unwrap()
    }

    /// The consequences of the given `id`.
    pub fn consequences(&self, id: &Id) -> Option<&Consequences> {
        self.adj.get(id)
    }

    /// Update [`Trace`] with the given [`Update`].
    pub fn apply(&mut self, update: Update) {
        match update {
            Update::OpenDirect { cause, consequence } => {
                self.adj
                    .entry(cause)
                    .or_insert_with(Consequences::none)
                    .add_direct(consequence);
            }
            Update::NewIndirect { cause, consequence } => {
                self.adj
                    .entry(cause)
                    .or_insert_with(Consequences::none)
                    .add_indirect(consequence);
            }
            Update::CloseDirect { id, direct_cause } => {
                let _ = self.adj.remove(&id);

                if let Some(direct_cause) = direct_cause {
                    if let Some(consequences) = self.adj.get_mut(&direct_cause) {
                        consequences.remove_direct(&id);
                    }
                }
            }
            Update::CloseIndirect {
                id,
                indirect_causes,
            } => {
                let _ = self.adj.remove(&id);

                for indirect_cause in indirect_causes {
                    if let Some(consequences) = self.adj.get_mut(&indirect_cause) {
                        consequences.remove_direct(&id);
                    }
                }
            }
            Update::CloseCyclic {
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

    /// A breadth-first traversal of [`Trace`].
    pub fn iter(&self) -> impl Iterator<Item = (Id, &Consequences)> {
        let mut queue = vec![(self.root.clone())];
        std::iter::from_fn(move || {
            let id = queue.pop()?;
            let consequences = self.consequences(&id)?;
            queue.extend(consequences.iter_direct());
            Some((id, consequences))
        })
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

/// Produces the full causality graph for the span corresponding to a given
/// `id`.
///
/// Returns both a [`Trace`] rooted at `id`, and a stream of updates
/// that affect the produced trace, but occurred after the invocation of this
/// method. If the span has already been closed, this function produces `None`.
///
/// ```
/// use std::sync::Arc;
/// use tracing_core::Subscriber;
/// use tracing_causality as causality;
/// use tracing_subscriber::{prelude::*, registry::Registry};
///
/// fn main() {
///     let subscriber: Arc<dyn Subscriber + Send + Sync > =
///         Arc::new(Registry::default().with(causality::Layer));
///     subscriber.clone().init();
///     let subscriber: Arc<dyn Subscriber> = subscriber;
///     let subscriber = subscriber.downcast_ref::<Registry>().unwrap();
///
///     let a = tracing::trace_span!("a");
///     let a_id = a.id().unwrap();
///
///     let b = a.in_scope(|| tracing::trace_span!("b"));
///     let b_id = b.id().unwrap();
///
///     let (trace, updates) = causality::trace(subscriber, &a_id, 1).unwrap();
///     assert!(trace.consequences(&a_id).unwrap().contains_direct(&b_id));
///
///     let c = b.in_scope(|| tracing::trace_span!("c"));
///     let c_id = c.id().unwrap();
///     
///     assert_eq!(
///         updates.next(),
///         Some(causality::Update::OpenDirect {
///             cause: b_id,
///             consequence: c_id,
///         })
///     );
/// }
/// ```
pub fn trace<S>(s: &S, id: &Id, update_capacity: usize) -> Option<(Trace, Updates)>
where
    S: for<'span> LookupSpan<'span> + ?Sized,
{
    let (sender, updates) = channel::bounded(id.clone(), update_capacity);
    let mut trace = Trace {
        root: id.to_owned(),
        adj: HashMap::default(),
    };
    let mut queue = vec![id.to_owned()];
    while let Some(id) = queue.pop() {
        if let Some(span) = s.span_data(&id) {
            let mut extensions = span.extensions_mut();
            // add the update listener
            get_or_init_with::<Listeners, _>(&mut extensions, Listeners::new)
                .insert(sender.clone());
            if let Some(consequences) = extensions.get_mut::<Consequences>() {
                let direct_consequences = consequences.clone();
                // add any further consequences to the traversal queue
                queue.extend(direct_consequences.direct.iter().cloned());
                // and to the trace
                trace.adj.insert(id, direct_consequences);
            }
        } else {
            // the span has already been closed; do nothing
        }
    }
    Some((trace, updates))
}

/// Produces the immediate consequences of the span corresponding to the given
/// `id`, or `None` if that span has already been closed.
///
/// ```
/// use std::sync::Arc;
/// use tracing_core::Subscriber;
/// use tracing_causality::{self as causality, Consequences};
/// use tracing_subscriber::{prelude::*, registry::Registry};
///
/// fn main() {
///     let subscriber: Arc<dyn Subscriber + Send + Sync > =
///         Arc::new(Registry::default().with(causality::Layer));
///     subscriber.clone().init();
///     let subscriber: Arc<dyn Subscriber> = subscriber;
///     let registry = subscriber.downcast_ref::<Registry>().unwrap();
///
///     let a = tracing::trace_span!("a");
///     let a_id = a.id().unwrap();
///
///     assert_eq!(
///         causality::consequences(registry, &a_id),
///         Some(Consequences::none())
///     );
///
///     let b = a.in_scope(|| tracing::trace_span!("b"));
///     let b_id = b.id().unwrap();
///
///     assert_eq!(
///         causality::consequences(registry, &a_id),
///         Some(Consequences::with_direct(b_id))
///     );
///
///     drop(b);
///
///     assert_eq!(
///         causality::consequences(registry, &a_id),
///         Some(Consequences::none())
///     );
///
///     drop(a);
///
///     assert_eq!(
///         causality::consequences(registry, &a_id),
///         None
///     );
/// }
/// ```
pub fn consequences<S>(subscriber: &S, span: &Id) -> Option<Consequences>
where
    S: for<'span> LookupSpan<'span> + ?Sized,
{
    Some(
        subscriber
            .span_data(span)?
            .extensions()
            .get::<Consequences>()
            .cloned()
            .unwrap_or_else(Consequences::default),
    )
}

/// An update that should be applied to a [`Trace`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Update {
    /// Announces that `consequence` **directly** follows from `cause`.
    ///
    /// # Example
    /// ```
    /// use std::sync::Arc;
    /// use tracing::Subscriber;
    /// use tracing_causality::{self as causality, Update};
    /// use tracing_subscriber::{prelude::*, registry::Registry};
    ///
    /// fn main() {
    ///     let subscriber: Arc<dyn Subscriber + Send + Sync> =
    ///         Arc::new(Registry::default().with(causality::Layer));
    ///     let _guard = subscriber.clone().set_default();
    ///     let subscriber: Arc<dyn Subscriber> = subscriber;
    ///     let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    ///     let cause = tracing::trace_span!("cause");
    ///     let cause_id = cause.id().unwrap();
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id, 1024).unwrap();
    ///
    ///     let consequence = cause.in_scope(|| tracing::trace_span!("consequence"));
    ///     let consequence_id = consequence.id().unwrap();
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::OpenDirect {
    ///             cause: cause_id.clone(),
    ///             consequence: consequence_id.clone(),
    ///         }],
    ///         "The listeners on `cause` should be notified that it has a \
    ///         direct `consequence`."
    ///     );
    /// }
    /// ```
    OpenDirect { cause: Id, consequence: Id },

    /// Announces that `consequence` **indirectly** follows from `cause`.
    ///
    /// # Example
    /// ```
    /// use std::sync::Arc;
    /// use tracing::Subscriber;
    /// use tracing_causality::{self as causality, Update};
    /// use tracing_subscriber::{prelude::*, registry::Registry};
    ///
    /// fn main() {
    ///     let subscriber: Arc<dyn Subscriber + Send + Sync> =
    ///         Arc::new(Registry::default().with(causality::Layer));
    ///     let _guard = subscriber.clone().set_default();
    ///     let subscriber: Arc<dyn Subscriber> = subscriber;
    ///     let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    ///     let cause = tracing::trace_span!("cause");
    ///     let cause_id = cause.id().unwrap();
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id, 1024).unwrap();
    ///
    ///     let consequence = tracing::trace_span!("consequence");
    ///     let consequence_id = consequence.id().unwrap();
    ///     
    ///     consequence.follows_from(&cause_id);
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::NewIndirect {
    ///             cause: cause_id.clone(),
    ///             consequence: consequence_id.clone(),
    ///         }],
    ///         "The listeners on `cause` should be notified that it has a \
    ///         indirect `consequence`."
    ///     );
    /// }
    /// ```
    NewIndirect { cause: Id, consequence: Id },

    /// Announces that a direct consequence of a `Span` within [`Trace`] was
    /// closed, and is thus no longer an extant consequence of `direct_cause`.
    ///
    /// # Example
    /// ```
    /// use std::sync::Arc;
    /// use tracing::Subscriber;
    /// use tracing_causality::{self as causality, Update};
    /// use tracing_subscriber::{prelude::*, registry::Registry};
    ///
    /// fn main() {
    ///     let subscriber: Arc<dyn Subscriber + Send + Sync> =
    ///         Arc::new(Registry::default().with(causality::Layer));
    ///     let _guard = subscriber.clone().set_default();
    ///     let subscriber: Arc<dyn Subscriber> = subscriber;
    ///     let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    ///     let cause = tracing::trace_span!("cause");
    ///     let cause_id = cause.id().unwrap();
    ///
    ///     let consequence = cause.in_scope(|| tracing::trace_span!("consequence"));
    ///     let consequence_id = consequence.id().unwrap();
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id, 1024).unwrap();
    ///
    ///     drop(consequence);
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::CloseDirect {
    ///             id: consequence_id.clone(),
    ///             direct_cause: Some(cause_id),
    ///         }],
    ///         "The listeners on `cause` should be notified that
    ///         `consequence` was closed."
    ///     );
    /// }
    /// ```
    CloseDirect { id: Id, direct_cause: Option<Id> },

    /// Announces that an indirect consequence of a `Span` within [`Trace`] was
    /// closed, and is thus no longer an extant consequence of `indirect_causes`.
    ///
    /// # Example
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, Update};
    /// use tracing_subscriber::{prelude::*, registry::Registry};
    ///
    /// fn main() {
    ///     let subscriber: Arc<dyn Subscriber + Send + Sync> =
    ///         Arc::new(Registry::default().with(causality::Layer));
    ///     let _guard = subscriber.clone().set_default();
    ///     let subscriber: Arc<dyn Subscriber> = subscriber;
    ///     let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    ///     let cause = tracing::trace_span!("cause");
    ///     let cause_id = cause.id().unwrap();
    ///
    ///     let consequence = tracing::trace_span!("consequence");
    ///     let consequence_id = consequence.id().unwrap();
    ///
    ///     consequence.follows_from(&cause_id);
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id, 1024).unwrap();
    ///
    ///     drop(consequence);
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::CloseIndirect {
    ///             id: consequence_id.clone(),
    ///             indirect_causes: vec![cause_id],
    ///         }],
    ///         "The listeners on `cause` should be notified that
    ///         `consequence` was closed."
    ///     );
    /// }
    /// ```
    CloseIndirect { id: Id, indirect_causes: Vec<Id> },

    /// Announces that a self-cycling consequence of a `Span` within [`Trace`]
    /// was closed, and is thus no longer an extant consequence of
    /// `direct_cause` or `indirect_cause`.
    ///
    /// # Example
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, Update};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// fn main() {
    ///     let subscriber: Arc<dyn Subscriber + Send + Sync> =
    ///         Arc::new(Registry::default().with(causality::Layer));
    ///     let _guard = subscriber.clone().set_default();
    ///     let subscriber: Arc<dyn Subscriber> = subscriber;
    ///     let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    ///     let cause = tracing::trace_span!("cause");
    ///     let cause_id = cause.id().unwrap();
    ///
    ///     let consequence = cause.clone();
    ///     let consequence_id = consequence.id().unwrap();
    ///
    ///     consequence.follows_from(&cause_id);
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id, 1024).unwrap();
    ///
    ///     drop([cause, consequence]);
    ///
    ///     assert_eq!(
    ///         cause_updates.into_iter().collect::<Vec<_>>(),
    ///         vec![Update::CloseCyclic {
    ///             id: consequence_id.clone(),
    ///             direct_cause: None,
    ///             indirect_causes: vec![cause_id.clone()],
    ///         }],
    ///         "The listeners on `cause` should be notified that
    ///         `consequence` was closed."
    ///     );
    /// }
    /// ```
    CloseCyclic {
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
                Update::NewIndirect {
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
        let span = ctx.span(id).expect(
            "The `id` provided to 
            `tracing_causality::Layer::on_new_span` did not correspond to an
            opened `Span` for the underlying subscriber. This span may have \
            already been closed, or been assigned by a different subscriber, \
            or there may be a bug in the subscriber underlying this layer.",
        );

        if let Some(direct_cause) = span.parent() {
            let mut cause_extensions = direct_cause.extensions_mut();
            let id = id.to_owned();

            if let Some(listeners) = cause_extensions.get_mut::<Listeners>() {
                // 1. notify listeners, if any, that `id` is a consequence
                channel::Sender::broadcast(
                    listeners,
                    Update::OpenDirect {
                        cause: direct_cause.id(),
                        consequence: id.clone(),
                    },
                );

                // 2. copy cause's listeners onto `consequence`
                crate::get_or_init_with::<Listeners, _>(&mut span.extensions_mut(), Listeners::new)
                    .extend(listeners.iter().cloned());
            }

            // 3. register that `cause` directly lead to `consequence`.
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

        let cause = ctx.span(cause_id).expect(
            "The `cause_id` provided to 
            `tracing_causality::Layer::on_follows_from` did not correspond to \
            an opened `Span` for the underlying subscriber. This span may have \
            already been closed, or been assigned by a different subscriber, \
            or there may be a bug in the subscriber underlying this layer.",
        );

        let consequence = ctx.span(consequence_id).expect(
            "The `consequence_id` provided to 
            `tracing_causality::Layer::on_follows_from` did not correspond to \
            an opened `Span` for the underlying subscriber. This span may have \
            already been closed, or been assigned by a different subscriber, \
            or there may be a bug in the subscriber underlying this layer.",
        );

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
                Update::NewIndirect {
                    cause: cause_id.clone(),
                    consequence: consequence_id.clone(),
                },
            );
        }
    }

    fn on_close(&self, id: Id, ctx: Context<'_, S>) {
        use data::IndirectCauses;
        let span = ctx.span(&id).expect(
            "The `id` provided to 
            `tracing_causality::Layer::close` did not correspond to an opened \
            `Span` for the underlying subscriber. This span have \
            already been closed, or been assigned by a different subscriber, \
            or there may be a bug in the subscriber underlying this layer.",
        );

        let mut extensions = span.extensions_mut();

        // `None` if this span is not its own immediate indirect cause,
        // otherwise `Some(indirect_causes)`.
        let mut is_cyclic = None;

        // 1. delete `id` as a consequence from each of its indirect causes
        if let Some(follows_from) = extensions.remove::<IndirectCauses>() {
            let indirect_causes: Vec<Id> = follows_from.causes.into_iter().collect();

            let drop_update = Update::CloseIndirect {
                id: id.clone(),
                indirect_causes: indirect_causes.clone(),
            };

            for cause_id in &indirect_causes {
                if cause_id == &id {
                    is_cyclic = Some(indirect_causes.clone());
                    continue;
                } else if let Some(cause) = ctx.span(cause_id) {
                    let mut extensions = cause.extensions_mut();

                    if let Some(consequences) = extensions.get_mut::<Consequences>() {
                        consequences.remove_indirect(&id);
                    }

                    if let Some(listeners) = extensions.get_mut::<Listeners>() {
                        channel::Sender::broadcast(listeners, drop_update.clone());
                    }
                } else {
                    // `cause_id` corresponds to a `Span` that has already been
                    // closed. TODO: investigate this case by throwing a panic
                    // here, and writing unit tests that trigger it.
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
            let update = if let Some(indirect_causes) = is_cyclic {
                Update::CloseCyclic {
                    id: id.clone(),
                    direct_cause: direct_cause.map(|c| c.id()),
                    indirect_causes,
                }
            } else {
                Update::CloseDirect {
                    id,
                    direct_cause: direct_cause.map(|c| c.id()),
                }
            };
            channel::Sender::broadcast(listeners, update);
        }
    }
}

#[cfg(test)]
mod test_util {
    use crate::{channel, Consequences};
    use tracing::{Id, Span};
    use tracing_subscriber::registry::LookupSpan;
    use tracing_subscriber::registry::SpanData;

    pub(crate) fn updates_for<S>(s: &S, span: &Span) -> channel::Updates
    where
        S: for<'span> LookupSpan<'span> + ?Sized,
    {
        use crate::data::Listeners;
        let id = span.id().expect(&format!("span {:?} is not enabled", span));
        let data = s
            .span_data(&id)
            .expect(&format!("span {:?} is not open", &id));
        let mut extensions = data.extensions_mut();
        let (sender, updates) = channel::bounded(id, 100);
        crate::get_or_init_with::<Listeners, _>(&mut extensions, Listeners::new).insert(sender);
        updates
    }

    pub(crate) fn direct_cause_of<S>(s: &S, span: &Span) -> Option<Id>
    where
        S: for<'span> LookupSpan<'span> + ?Sized,
    {
        let id = span.id().expect(&format!("span {:?} is not enabled", span));
        s.span_data(&id)
            .expect(&format!("span {:?} is not open", id))
            .parent()
            .cloned()
    }

    pub(crate) fn assert_lacks_consequences<S>(s: &S, span: &Span)
    where
        S: for<'span> LookupSpan<'span> + ?Sized,
    {
        let id = span.id().expect(&format!("span {:?} is not enabled", span));
        assert_eq!(
            None,
            s.span_data(&id)
                .expect(&format!("span {:?} is not open", &id))
                .extensions()
                .get::<Consequences>(),
            "span {:?} should lack {:?}",
            span,
            std::any::type_name::<Consequences>(),
        );
    }

    pub(crate) fn consequences_of<S>(s: &S, span: &Span) -> Consequences
    where
        S: for<'span> LookupSpan<'span> + ?Sized,
    {
        let id = span.id().expect(&format!("span {:?} is not enabled", span));
        s.span_data(&id)
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

#[cfg(test)]
mod test {
    use crate::{self as causality, Consequences, Update, Updates};
    use std::sync::Arc;
    use tracing_core::Subscriber;
    use tracing_subscriber::registry::{LookupSpan, SpanData};
    use tracing_subscriber::{prelude::*, registry::Registry};

    mod trace {
        use crate::{self as causality, Consequences, Update, Updates};
        use std::sync::Arc;
        use tracing_core::Subscriber;
        use tracing_subscriber::registry::{LookupSpan, SpanData};
        use tracing_subscriber::{prelude::*, registry::Registry};

        #[test]
        fn should_install_listener() {
            let subscriber: Arc<dyn Subscriber + Send + Sync> =
                Arc::new(Registry::default().with(causality::Layer));
            let _guard = subscriber.clone().set_default();
            let subscriber: Arc<dyn Subscriber> = subscriber;
            let registry = subscriber.downcast_ref::<Registry>().unwrap();

            let a = tracing::trace_span!("a");
            let a_id = a.id().unwrap();

            assert!(registry
                .span_data(&a_id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            let (_trace, _updates) = causality::trace(registry, &a_id, 1024).unwrap();

            // after `trace`, there should be 1 listener on `a`
            assert_eq!(
                registry
                    .span_data(&a_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                1
            );
        }

        #[test]
        fn should_copy_listener() {
            let subscriber: Arc<dyn Subscriber + Send + Sync> =
                Arc::new(Registry::default().with(causality::Layer));
            let _guard = subscriber.clone().set_default();
            let subscriber: Arc<dyn Subscriber> = subscriber;
            let registry = subscriber.downcast_ref::<Registry>().unwrap();

            let a = tracing::trace_span!("a");
            let a_id = a.id().unwrap();

            let b = a.in_scope(|| tracing::trace_span!("b"));
            let b_id = b.id().unwrap();

            assert!(registry
                .span_data(&a_id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            assert!(registry
                .span_data(&b_id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            let (_trace, _updates) = causality::trace(registry, &a_id, 1024).unwrap();

            // after `trace`, there should be 1 listener on `a`
            assert_eq!(
                registry
                    .span_data(&a_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                1
            );

            // after `trace`, there should be 1 listener on `b`
            assert_eq!(
                registry
                    .span_data(&b_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                1
            );
        }

        #[test]
        fn should_not_overwrite_listeners() {
            let subscriber: Arc<dyn Subscriber + Send + Sync> =
                Arc::new(Registry::default().with(causality::Layer));
            let _guard = subscriber.clone().set_default();
            let subscriber: Arc<dyn Subscriber> = subscriber;
            let registry = subscriber.downcast_ref::<Registry>().unwrap();

            let a = tracing::trace_span!("a");
            let a_id = a.id().unwrap();

            let b = a.in_scope(|| tracing::trace_span!("b"));
            let b_id = b.id().unwrap();

            assert!(registry
                .span_data(&a_id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            assert!(registry
                .span_data(&b_id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            // trace `b`
            let (_trace, _updates) = causality::trace(registry, &b_id, 1024).unwrap();

            // after `trace`, there should be 0 listeners on `a`
            assert!(registry
                .span_data(&a_id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            // after `trace`, there should be 1 listener on `b`
            assert_eq!(
                registry
                    .span_data(&b_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                1
            );

            // trace `a`
            let (_trace, _updates) = causality::trace(registry, &a_id, 1024).unwrap();

            // after `trace`, there should be 1 listener on `a`
            assert_eq!(
                registry
                    .span_data(&a_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                1
            );

            // after `trace`, there should be 2 listeners on `b`
            assert_eq!(
                registry
                    .span_data(&b_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                2
            );
        }
    }

    mod layer {
        mod on_new_span {
            use crate::test::*;

            /// If the span's parent has listeners, those listeners should be notified
            /// that the parent has a new consequence.
            #[test]
            fn should_notify_listeners() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let a = tracing::trace_span!("a");
                let a_id = a.id().unwrap();

                // prior to `trace`, there are no listeners on `a`
                assert!(registry
                    .span_data(&a_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .is_none());

                let (_trace, updates) = causality::trace(registry, &a_id, 1024).unwrap();

                // after `trace`, there should be 1 listener on `a`
                assert_eq!(
                    registry
                        .span_data(&a_id)
                        .unwrap()
                        .extensions()
                        .get::<crate::Listeners>()
                        .expect("there should be listeners on this span")
                        .len(),
                    1
                );

                let b = a.in_scope(|| tracing::trace_span!("b"));
                let b_id = b.id().unwrap();

                assert_eq!(
                    updates.next(),
                    Some(Update::OpenDirect {
                        cause: a_id,
                        consequence: b_id,
                    })
                );

                assert!(updates.is_empty());
            }

            /// If the parent of a new span has update listeners, those listeners should
            /// be copied to the new span.
            #[test]
            fn should_copy_listeners() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let a = tracing::trace_span!("a");
                let a_id = a.id().unwrap();

                let (_trace, _updates) = causality::trace(registry, &a_id, 1024).unwrap();

                let b = a.in_scope(|| tracing::trace_span!("b"));
                let b_id = b.id().unwrap();

                let (_trace, _updates) = causality::trace(registry, &b_id, 1024).unwrap();

                let a_listeners = registry
                    .span_data(&a_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on span `a`")
                    .clone();

                let b_listeners = registry
                    .span_data(&b_id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on span `b`")
                    .clone();

                dbg!(&a_listeners);
                dbg!(&b_listeners);

                assert!(
                    b_listeners.is_superset(&a_listeners),
                    "the listeners on `a` should have been copied to `b`"
                );

                assert_ne!(
                    b_listeners,
                    a_listeners,
                    "the listeners of `b` should not have been simply replaced the listeners on `a`"
                );
            }

            /// If the new span as a parent, the new span should be recorded as a direct
            /// consequence of the parent.
            #[test]
            fn should_record_consequence() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let a = tracing::trace_span!("a");
                let a_id = a.id().unwrap();

                let a_consequences = causality::consequences(registry, &a_id)
                    .expect("span `a` should not have been closed yet");

                assert_eq!(
                    a_consequences,
                    Consequences::default(),
                    "span `a` should not have any consequences"
                );

                let b = a.in_scope(|| tracing::trace_span!("b"));
                let b_id = b.id().unwrap();

                let a_consequences = causality::consequences(registry, &a_id)
                    .expect("span `a` should not have been closed yet");

                assert_eq!(
                    a_consequences,
                    Consequences::with_direct(b_id),
                    "span `a` should only have the direct consequence `b`"
                );
            }
        }

        mod on_follows_from {
            use crate::test::*;

            /// Upon `consequence.follows_from(cause)`, the layer should record
            /// that `consequence` indirectly follows from `cause` in `causes`'s
            /// `Consequences`.
            #[test]
            fn should_record_consequence() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let cause = tracing::trace_span!("cause");
                let cause_id = cause.id().unwrap();

                let consequence = tracing::trace_span!("consequence");
                let consequence_id = consequence.id().unwrap();

                let consequences = causality::consequences(registry, &cause_id)
                    .expect("span `cause` should not have been closed yet");

                assert_eq!(
                    consequences,
                    Consequences::default(),
                    "span `cause` should not have any consequences"
                );

                consequence.follows_from(&cause_id);

                let consequences = causality::consequences(registry, &cause_id)
                    .expect("span `cause` should not have been closed yet");

                assert_eq!(
                    consequences,
                    Consequences::with_indirect(consequence_id),
                    "span `cause` should have an indirect `consequence`"
                );
            }

            /// Upon `consequence.follows_from(cause)`, the layer should record
            /// that `cause` indirectly led to `consequence` in `consequence`'s
            /// `IndirectCauses`.
            #[test]
            fn should_record_cause() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let cause = tracing::trace_span!("cause");
                let cause_id = cause.id().unwrap();

                let consequence = tracing::trace_span!("consequence");
                let consequence_id = consequence.id().unwrap();

                assert!(
                    registry
                        .span_data(&consequence_id)
                        .expect("span `consequence` should not yet be closed.")
                        .extensions()
                        .get::<crate::data::IndirectCauses>()
                        .is_none(),
                    "span `consequence` should not yet have `IndirectCauses`"
                );

                consequence.follows_from(&cause_id);

                assert!(
                    registry
                        .span_data(&consequence_id)
                        .expect("span `consequence` should not yet be closed.")
                        .extensions()
                        .get::<crate::data::IndirectCauses>()
                        .expect("span `consequence` should have `IndirectCauses`")
                        .contains(&cause_id),
                    "`consequence`'s `IndirectCauses` should contain `cause_id`"
                );
            }

            /// Upon `consequence.follows_from(cause)`, the layer should notify
            /// `cause`'s listeners that `cause` indirectly led to `consequence`.
            #[test]
            fn should_notify_listeners() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let cause = tracing::trace_span!("cause");
                let cause_id = cause.id().unwrap();

                let consequence = tracing::trace_span!("consequence");
                let consequence_id = consequence.id().unwrap();

                let (_trace, cause_updates) = crate::trace(registry, &cause_id, 1024).unwrap();
                let (_trace, consequence_updates) =
                    crate::trace(registry, &consequence_id, 1024).unwrap();

                assert!(consequence_updates.is_empty());
                assert!(cause_updates.is_empty());

                consequence.follows_from(&cause_id);

                assert!(
                    consequence_updates.is_empty(),
                    "The listeners on `consequence` should not have been \
                    notified of anything."
                );
                assert_eq!(
                    cause_updates.next(),
                    Some(Update::NewIndirect {
                        cause: cause_id.clone(),
                        consequence: consequence_id.clone(),
                    }),
                    "The listeners on `cause` should be notified that \
                    `consequence` indirectly follows from `cause`."
                );
                assert!(cause_updates.is_empty());
            }
        }

        mod on_close {
            use crate::test::*;

            /// Upon the closure of a span, the layer should, for each indirect
            /// cause of that span, erase the closed span as an indirect
            /// consequence.
            #[test]
            fn should_erase_consequence() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let cause = tracing::trace_span!("cause");
                let cause_id = cause.id().unwrap();

                let consequence = tracing::trace_span!("consequence");
                let consequence_id = consequence.id().unwrap();

                let (_trace, _updates) = crate::trace(registry, &cause_id, 1024).unwrap();
                let (_trace, _updates) = crate::trace(registry, &consequence_id, 1024).unwrap();

                assert_eq!(
                    causality::consequences(registry, &cause_id)
                        .expect("span `cause` should not have been closed yet"),
                    Consequences::default(),
                    "span `cause` should not have any consequences"
                );

                consequence.follows_from(&cause_id);

                assert_eq!(
                    causality::consequences(registry, &cause_id)
                        .expect("span `cause` should not have been closed yet"),
                    Consequences::with_indirect(consequence_id.clone()),
                    "span `cause` should have one indirect consequence"
                );

                drop(consequence);

                assert_eq!(
                    causality::consequences(registry, &cause_id)
                        .expect("span `cause` should not have been closed yet"),
                    Consequences::default(),
                    "span `cause` should not have any consequences"
                );
            }

            /// Upon the closure of a span, the layer should, for each indirect
            /// cause of that span, notify those cause's listeners that this
            /// indirect within their [`Trace`] has been closed.
            #[test]
            fn should_notify_causes_acyclic() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let cause = tracing::trace_span!("cause");
                let cause_id = cause.id().unwrap();

                let consequence = tracing::trace_span!("consequence");
                let consequence_id = consequence.id().unwrap();

                consequence.follows_from(&cause_id);

                let (_trace, cause_updates) = crate::trace(registry, &cause_id, 1024).unwrap();
                let (_trace, _consequence_updates) =
                    crate::trace(registry, &consequence_id, 1024).unwrap();

                drop(consequence);

                assert_eq!(
                    cause_updates.next(),
                    Some(Update::CloseIndirect {
                        id: consequence_id.clone(),
                        indirect_causes: vec![cause_id.clone()],
                    }),
                    "The listeners on `cause` should be notified that
                    `consequence` was closed."
                );
                assert!(cause_updates.is_empty());
            }

            /// Upon the closure of a span, the layer should, for each indirect
            /// cause of that span, notify those cause's listeners that this
            /// indirect within their [`Trace`] has been closed.
            #[test]
            fn should_notify_causes_cyclic() {
                let subscriber: Arc<dyn Subscriber + Send + Sync> =
                    Arc::new(Registry::default().with(causality::Layer));
                let _guard = subscriber.clone().set_default();
                let subscriber: Arc<dyn Subscriber> = subscriber;
                let registry = subscriber.downcast_ref::<Registry>().unwrap();

                let cause = tracing::trace_span!("cause");
                let cause_id = cause.id().unwrap();

                let consequence = cause.clone();
                let consequence_id = consequence.id().unwrap();

                consequence.follows_from(&cause_id);

                let (_trace, cause_updates) = crate::trace(registry, &cause_id, 1024).unwrap();
                let (_trace, _consequence_updates) =
                    crate::trace(registry, &consequence_id, 1024).unwrap();

                drop([cause, consequence]);

                assert_eq!(
                    cause_updates.next(),
                    Some(Update::CloseCyclic {
                        id: consequence_id.clone(),
                        direct_cause: None,
                        indirect_causes: vec![cause_id.clone()],
                    }),
                    "The listeners on `cause` should be notified that
                    `consequence` was closed."
                );

                assert!(cause_updates.is_empty());
            }
        }
    }
}

#[cfg(test)]
mod test2 {
    use std::sync::Arc;
    use tracing_core::Subscriber;
    use tracing_subscriber::registry::{LookupSpan, SpanData};
    use tracing_subscriber::{prelude::*, registry::Registry};

    #[test]
    fn should_update_transitively_1() {
        let subscriber: Arc<dyn Subscriber + Send + Sync> =
            Arc::new(Registry::default().with(crate::Layer));
        let _guard = subscriber.clone().set_default();
        let subscriber: Arc<dyn Subscriber> = subscriber;
        let subscriber = subscriber.downcast_ref::<Registry>().unwrap();

        let a = tracing::trace_span!("a");
        let a_id = a.id().unwrap();

        let b = a.in_scope(|| tracing::trace_span!("b"));
        let b_id = b.id().unwrap();

        let (trace, updates) = crate::trace(subscriber, &a_id, 1).unwrap();
        assert!(trace.consequences(&a_id).unwrap().contains_direct(&b_id));

        let c = b.in_scope(|| tracing::trace_span!("c"));
        let c_id = c.id().unwrap();

        dbg!(subscriber
            .span_data(&b_id)
            .unwrap()
            .extensions()
            .get::<crate::Listeners>()
            .is_some());

        assert_eq!(
            updates.next(),
            Some(crate::Update::OpenDirect {
                cause: b_id,
                consequence: c_id,
            })
        );
    }

    #[test]
    fn should_update_transitively_2() {
        let subscriber: Arc<dyn Subscriber + Send + Sync> =
            Arc::new(Registry::default().with(crate::Layer));
        let _guard = subscriber.clone().set_default();
        let subscriber: Arc<dyn Subscriber> = subscriber;
        let subscriber = subscriber.downcast_ref::<Registry>().unwrap();

        let a = tracing::trace_span!("a");
        let a_id = a.id().unwrap();

        let (_trace, updates) = crate::trace(subscriber, &a_id, 1024).unwrap();

        let b = a.in_scope(|| tracing::trace_span!("b"));
        let b_id = b.id().unwrap();

        let c = b.in_scope(|| tracing::trace_span!("c"));
        let c_id = c.id().unwrap();

        dbg!(subscriber
            .span_data(&b_id)
            .unwrap()
            .extensions()
            .get::<crate::Listeners>()
            .is_some());

        dbg!(subscriber
            .span_data(&c_id)
            .unwrap()
            .extensions()
            .get::<crate::Listeners>()
            .is_some());

        assert_eq!(
            updates.next(),
            Some(crate::Update::OpenDirect {
                cause: a_id,
                consequence: b_id.clone(),
            })
        );

        assert_eq!(
            updates.next(),
            Some(crate::Update::OpenDirect {
                cause: b_id,
                consequence: c_id,
            })
        );
    }
}

#[cfg(test)]
mod test_layer {
    use super::test_util;
    use std::sync::Arc;
    use tracing::trace_span;
    use tracing_core::Subscriber;
    use tracing_subscriber::{prelude::*, registry::Registry};

    /// Tests the causality layer with on a trace involving a root without
    /// consequences.
    #[test]
    fn root() {
        let subscriber: Arc<dyn Subscriber + Send + Sync> =
            Arc::new(Registry::default().with(crate::Layer));
        let _guard = subscriber.clone().set_default();
        let subscriber: Arc<dyn Subscriber> = subscriber;
        let subscriber = subscriber.downcast_ref::<Registry>().unwrap();

        let root = trace_span!("root");
        let updates = test_util::updates_for(subscriber, &root);

        assert_eq!(
            test_util::direct_cause_of(subscriber, &root),
            None,
            "span `root` should not have any parent"
        );

        test_util::assert_lacks_consequences(subscriber, &root);

        let root_id = root.id().unwrap();
        drop(root);

        assert_eq!(
            updates.next(),
            Some(crate::Update::CloseDirect {
                id: root_id,
                direct_cause: None,
                //indirect_causes: vec![],
            }),
            "listeners on Span `root` should have been updated",
        );
    }

    /// Tests the causality layer on a trace involving a root with a single
    /// direct consequence.
    #[test]
    fn direct_consequence() {
        let subscriber: Arc<dyn Subscriber + Send + Sync> =
            Arc::new(Registry::default().with(crate::Layer));
        let _guard = subscriber.clone().set_default();
        let subscriber: Arc<dyn Subscriber> = subscriber;
        let subscriber = subscriber.downcast_ref::<Registry>().unwrap();

        let root = trace_span!("root");
        let root_id = root.id().unwrap();
        let root_updates = test_util::updates_for(subscriber, &root);

        test_util::assert_lacks_consequences(subscriber, &root);

        assert!(root_updates.is_empty());

        let consequence = root.in_scope(|| trace_span!("consequence"));
        let consequence_id = consequence.id().unwrap();
        let consequence_updates = test_util::updates_for(subscriber, &consequence);

        assert_eq!(
            root_updates.next(),
            Some(crate::Update::OpenDirect {
                cause: root.id().unwrap(),
                consequence: consequence.id().unwrap(),
            }),
            "listeners on Span `root` should have been updated",
        );

        assert!(root_updates.is_empty());

        test_util::assert_lacks_consequences(subscriber, &consequence);

        assert_eq!(
            test_util::direct_cause_of(subscriber, &consequence),
            root.id(),
            "`consequence` should be the direct consequence of `root`"
        );

        assert_eq!(
            test_util::consequences_of(subscriber, &root),
            crate::Consequences::with_direct(consequence.id().unwrap()),
            "`consequence` should be the direct consequence of `root`"
        );

        drop(root);

        // `consequence` is still extant, so `root` isn't actually closed
        assert!(root_updates.is_empty());
        assert!(consequence_updates.is_empty());

        drop(consequence);

        // `consequence` is closed, because there are no other spans with the same id
        let consequence_closed_update = crate::Update::CloseDirect {
            id: consequence_id.clone(),
            direct_cause: Some(root_id.clone()),
        };
        assert_eq!(
            consequence_updates.next(),
            Some(consequence_closed_update.clone()),
            "listeners on Span `consequences` should have been updated",
        );
        assert_eq!(
            root_updates.next(),
            Some(consequence_closed_update),
            "listeners on Span `root` should have been updated",
        );

        // and, with `consequences` gone, `root` is actually closed, too
        assert_eq!(
            root_updates.next(),
            Some(crate::Update::CloseDirect {
                id: root_id,
                direct_cause: None,
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
        let subscriber: Arc<dyn Subscriber + Send + Sync> =
            Arc::new(Registry::default().with(crate::Layer));
        let _guard = subscriber.clone().set_default();
        let subscriber: Arc<dyn Subscriber> = subscriber;
        let subscriber = subscriber.downcast_ref::<Registry>().unwrap();

        let cause = trace_span!("cause");
        let cause_id = cause.id().unwrap();
        let cause_updates = test_util::updates_for(subscriber, &cause);

        let consequence = trace_span!("consequence");
        let consequence_id = consequence.id().unwrap();
        let consequence_updates = test_util::updates_for(subscriber, &consequence);

        assert!(cause_updates.is_empty());
        assert!(consequence_updates.is_empty());

        consequence.follows_from(&cause_id);

        assert!(test_util::consequences_of(subscriber, &cause).contains_indirect(&consequence_id));

        assert!(consequence_updates.is_empty());
        assert_eq!(
            cause_updates.next(),
            Some(crate::Update::NewIndirect {
                cause: cause_id.clone(),
                consequence: consequence_id.clone(),
            }),
            "listeners should have been updated that `consequence` indirectly follows from `cause`",
        );
        assert!(cause_updates.is_empty());

        drop(consequence);

        assert_eq!(
            cause_updates.next(),
            Some(crate::Update::CloseIndirect {
                id: consequence_id.clone(),
                //direct_cause: None,
                indirect_causes: vec![cause_id],
            }),
            "listeners on `a` should have been notified that that `b` was dropped",
        );
    }
}
