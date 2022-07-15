use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
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

pub(crate) type Metadata = &'static tracing_core::Metadata<'static>;

/// A causality graph, rooted at a given [`Id`].
#[derive(Debug, Clone)]
pub struct Trace<M = crate::Metadata>
where
    M: Clone + Debug,
{
    pub root: Span<M>,
    pub adj: HashMap<Span<M>, Consequences<M>>,
}

#[derive(Debug, Clone)]
pub struct Span<M = crate::Metadata>
where
    M: Clone + Debug,
{
    pub id: Id,
    pub metadata: M,
}

impl<M> Hash for Span<M>
where
    M: Clone + Debug,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl<M> Eq for Span<M> where M: Clone + Debug {}

impl<M, N> PartialEq<Span<N>> for Span<M>
where
    M: Clone + Debug,
    N: Clone + Debug,
{
    fn eq(&self, other: &Span<N>) -> bool {
        &self.id == &other.id
    }
}

impl<M> Trace<M>
where
    M: Clone + Debug,
{
    pub fn with_root(root: Span<M>) -> Self {
        Self {
            root,
            adj: Default::default(),
        }
    }

    /// The `Id` of the root span of this trace.
    pub fn root(&self) -> Span<M> {
        self.root.to_owned()
    }

    /// The consequences of the `root` span of this trace.
    pub fn root_consequences(&self) -> &Consequences<M> {
        self.adj.get(&self.root).unwrap()
    }

    /// The consequences of the given `id`.
    pub fn consequences(&self, span: &Span<M>) -> Option<&Consequences<M>> {
        self.adj.get(span)
    }

    /// Update [`Trace`] with the given [`Update`].
    pub fn apply(mut self, update: Update<M>) -> Option<Trace<M>> {
        match update {
            Update::OpenDirect { cause, consequence } => {
                self.adj
                    .entry(cause)
                    .or_insert_with(Consequences::none)
                    .add_direct(consequence);
                Some(self)
            }
            Update::NewIndirect { cause, consequence } => {
                self.adj
                    .entry(cause)
                    .or_insert_with(Consequences::none)
                    .add_indirect(consequence);
                Some(self)
            }
            Update::CloseDirect { span, direct_cause } => {
                if let Some(direct_cause) = direct_cause {
                    let _ = self.adj.remove(&span);
                    if let Some(consequences) = self.adj.get_mut(&direct_cause) {
                        consequences.remove_direct(&span);
                    }
                    Some(self)
                } else {
                    debug_assert_eq!(self.root, span);
                    None
                }
            }
            Update::CloseIndirect {
                span: id,
                indirect_causes,
            } => {
                let _ = self.adj.remove(&id);

                for indirect_cause in indirect_causes {
                    if let Some(consequences) = self.adj.get_mut(&indirect_cause) {
                        consequences.remove_direct(&id);
                    }
                }

                Some(self)
            }
            Update::CloseCyclic {
                span: id,
                direct_cause,
                indirect_causes,
            } => {
                if let Some(direct_cause) = direct_cause {
                    let _ = self.adj.remove(&id);
                    if let Some(consequences) = self.adj.get_mut(&direct_cause) {
                        consequences.remove_direct(&id);
                    }
                    for indirect_cause in indirect_causes {
                        if let Some(consequences) = self.adj.get_mut(&indirect_cause) {
                            consequences.remove_direct(&id);
                        }
                    }
                    Some(self)
                } else {
                    debug_assert_eq!(self.root, id);
                    None
                }
            }
        }
    }

    /// A breadth-first traversal of [`Trace`].
    pub fn iter(&self) -> impl Iterator<Item = (Span<M>, &Consequences<M>)> {
        let mut queue = vec![(self.root.clone())];
        std::iter::from_fn(move || {
            let span = queue.pop()?;
            let consequences = self.consequences(&span)?;
            queue.extend(consequences.iter_direct());
            Some((span, consequences))
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
///     let a_id_and_metadata = causality::Span {
///         id: a.id().unwrap(),
///         metadata: a.metadata().unwrap()
///     };
///
///     let b = a.in_scope(|| tracing::trace_span!("b"));
///     let b_id_and_metadata = causality::Span {
///         id: b.id().unwrap(),
///         metadata: b.metadata().unwrap()
///     };
///
///     let (trace, updates) = causality::trace(subscriber, &a_id_and_metadata.id, 1).unwrap();
///     assert!(trace.consequences(&a_id_and_metadata).unwrap().contains_direct(&b_id_and_metadata));
///
///     let c = b.in_scope(|| tracing::trace_span!("c"));
///     let c_id_and_metadata = causality::Span {
///         id: c.id().unwrap(),
///         metadata: c.metadata().unwrap()
///     };
///     
///     assert_eq!(
///         updates.next(),
///         Some(causality::Update::OpenDirect {
///             cause: b_id_and_metadata,
///             consequence: c_id_and_metadata,
///         })
///     );
/// }
/// ```
pub fn trace<S>(s: &S, id: &Id, update_capacity: usize) -> Option<(Trace, Updates)>
where
    S: for<'span> LookupSpan<'span> + ?Sized,
{
    let (sender, updates) = channel::bounded(id.clone(), update_capacity);
    let root = Span {
        id: id.clone(),
        metadata: s.span_data(id)?.metadata(),
    };
    let mut trace = Trace {
        root: root.clone(),
        adj: HashMap::default(),
    };
    let mut queue = vec![root.to_owned()];
    while let Some(span) = queue.pop() {
        if let Some(span_data) = s.span_data(&span.id) {
            let mut extensions = span_data.extensions_mut();
            // add the update listener
            get_or_init_with::<Listeners, _>(&mut extensions, Listeners::new)
                .insert(sender.clone());
            if let Some(consequences) = extensions.get_mut::<Consequences>() {
                let direct_consequences = consequences.clone();
                // add any further consequences to the traversal queue
                queue.extend(direct_consequences.direct.iter().cloned());
                // and to the trace
                trace.adj.insert(span, direct_consequences);
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
///     let a_id_and_metadata = causality::Span {
///         id: a.id().unwrap(),
///         metadata: a.metadata().unwrap()
///     };
///
///     assert_eq!(
///         causality::consequences(registry, &a_id_and_metadata.id),
///         Some(Consequences::none())
///     );
///
///     let b = a.in_scope(|| tracing::trace_span!("b"));
///     let b_id_and_metadata = causality::Span {
///         id: b.id().unwrap(),
///         metadata: b.metadata().unwrap()
///     };
///
///     assert_eq!(
///         causality::consequences(registry, &a_id_and_metadata.id),
///         Some(Consequences::with_direct(b_id_and_metadata))
///     );
///
///     drop(b);
///
///     assert_eq!(
///         causality::consequences(registry, &a_id_and_metadata.id),
///         Some(Consequences::none())
///     );
///
///     drop(a);
///
///     assert_eq!(
///         causality::consequences(registry, &a_id_and_metadata.id),
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
pub enum Update<M = crate::Metadata>
where
    M: Clone + Debug,
{
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
    ///     let cause_id_and_metadata = causality::Span {
    ///         id: cause.id().unwrap(),
    ///         metadata: cause.metadata().unwrap()
    ///     };
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
    ///
    ///     let consequence = cause.in_scope(|| tracing::trace_span!("consequence"));
    ///     let consequence_id_and_metadata = causality::Span {
    ///         id: consequence.id().unwrap(),
    ///         metadata: consequence.metadata().unwrap()
    ///     };
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::OpenDirect {
    ///             cause: cause_id_and_metadata,
    ///             consequence: consequence_id_and_metadata,
    ///         }],
    ///         "The listeners on `cause` should be notified that it has a \
    ///         direct `consequence`."
    ///     );
    /// }
    /// ```
    OpenDirect {
        cause: Span<M>,
        consequence: Span<M>,
    },

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
    ///     let cause_id_and_metadata = causality::Span {
    ///         id: cause.id().unwrap(),
    ///         metadata: cause.metadata().unwrap()
    ///     };
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
    ///
    ///     let consequence = tracing::trace_span!("consequence");
    ///     let consequence_id_and_metadata = causality::Span {
    ///         id: consequence.id().unwrap(),
    ///         metadata: consequence.metadata().unwrap()
    ///     };
    ///     
    ///     consequence.follows_from(&cause_id_and_metadata.id);
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::NewIndirect {
    ///             cause: cause_id_and_metadata.clone(),
    ///             consequence: consequence_id_and_metadata.clone(),
    ///         }],
    ///         "The listeners on `cause` should be notified that it has a \
    ///         indirect `consequence`."
    ///     );
    /// }
    /// ```
    NewIndirect {
        cause: Span<M>,
        consequence: Span<M>,
    },

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
    ///     let cause_id_and_metadata = causality::Span {
    ///         id: cause.id().unwrap(),
    ///         metadata: cause.metadata().unwrap()
    ///     };
    ///
    ///     let consequence = cause.in_scope(|| tracing::trace_span!("consequence"));
    ///     let consequence_id_and_metadata = causality::Span {
    ///         id: consequence.id().unwrap(),
    ///         metadata: consequence.metadata().unwrap()
    ///     };
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
    ///
    ///     drop(consequence);
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::CloseDirect {
    ///             span: consequence_id_and_metadata.clone(),
    ///             direct_cause: Some(cause_id_and_metadata),
    ///         }],
    ///         "The listeners on `cause` should be notified that
    ///         `consequence` was closed."
    ///     );
    /// }
    /// ```
    CloseDirect {
        span: Span<M>,
        direct_cause: Option<Span<M>>,
    },

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
    ///     let cause_id_and_metadata = causality::Span {
    ///         id: cause.id().unwrap(),
    ///         metadata: cause.metadata().unwrap()
    ///     };
    ///
    ///     let consequence = tracing::trace_span!("consequence");
    ///     let consequence_id_and_metadata = causality::Span {
    ///         id: consequence.id().unwrap(),
    ///         metadata: consequence.metadata().unwrap()
    ///     };
    ///
    ///     consequence.follows_from(&cause_id_and_metadata.id);
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
    ///
    ///     drop(consequence);
    ///
    ///     assert_eq!(
    ///         cause_updates.drain().collect::<Vec<_>>(),
    ///         vec![Update::CloseIndirect {
    ///             span: consequence_id_and_metadata,
    ///             indirect_causes: vec![cause_id_and_metadata],
    ///         }],
    ///         "The listeners on `cause` should be notified that
    ///         `consequence` was closed."
    ///     );
    /// }
    /// ```
    CloseIndirect {
        span: Span<M>,
        indirect_causes: Vec<Span<M>>,
    },

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
    ///     let cause_id_and_metadata = causality::Span {
    ///         id: cause.id().unwrap(),
    ///         metadata: cause.metadata().unwrap()
    ///     };
    ///
    ///     let consequence = cause.clone();
    ///     let consequence_id_and_metadata = causality::Span {
    ///         id: consequence.id().unwrap(),
    ///         metadata: consequence.metadata().unwrap()
    ///     };
    ///
    ///     consequence.follows_from(&cause_id_and_metadata.id);
    ///
    ///     let (_trace, cause_updates) = causality::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
    ///
    ///     drop([cause, consequence]);
    ///
    ///     assert_eq!(
    ///         cause_updates.into_iter().collect::<Vec<_>>(),
    ///         vec![Update::CloseCyclic {
    ///             span: consequence_id_and_metadata.clone(),
    ///             direct_cause: None,
    ///             indirect_causes: vec![cause_id_and_metadata.clone()],
    ///         }],
    ///         "The listeners on `cause` should be notified that
    ///         `consequence` was closed."
    ///     );
    /// }
    /// ```
    CloseCyclic {
        span: Span<M>,
        direct_cause: Option<Span<M>>,
        indirect_causes: Vec<Span<M>>,
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
        let id_and_metadata = Span {
            id: span_id.to_owned(),
            metadata: span.metadata(),
        };

        // 1. insert `consequence` as an indirect consequence of `cause`
        if let Some(consequences) = span_data.get_mut::<Consequences>() {
            consequences.indirect.insert(id_and_metadata.clone());
        } else {
            span_data.insert(Consequences::with_indirect(id_and_metadata.clone()));
        }

        // 2. insert `cause` as an indirect cause of `consequence`
        if let Some(follows_from) = span_data.get_mut::<IndirectCauses>() {
            follows_from.add_cause(id_and_metadata.clone());
        } else {
            span_data.insert(IndirectCauses::with_cause(id_and_metadata.clone()));
        }

        if let Some(listeners) = span_data.get_mut::<Listeners>() {
            // 3. notify causes's listeners that it indirectly lead to `consequence`
            channel::Sender::broadcast(
                listeners,
                Update::NewIndirect {
                    cause: id_and_metadata.clone(),
                    consequence: id_and_metadata.clone(),
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
        let consequence_id_and_metadata = Span {
            id: id.to_owned(),
            metadata: span.metadata(),
        };

        if let Some(direct_cause) = span.parent() {
            let mut cause_extensions = direct_cause.extensions_mut();
            let cause_id_and_metadata = Span {
                id: direct_cause.id(),
                metadata: direct_cause.metadata(),
            };

            if let Some(listeners) = cause_extensions.get_mut::<Listeners>() {
                // 1. notify listeners, if any, that `id` is a consequence
                channel::Sender::broadcast(
                    listeners,
                    Update::OpenDirect {
                        cause: cause_id_and_metadata,
                        consequence: consequence_id_and_metadata.clone(),
                    },
                );

                // 2. copy cause's listeners onto `consequence`
                crate::get_or_init_with::<Listeners, _>(&mut span.extensions_mut(), Listeners::new)
                    .extend(listeners.iter().cloned());
            }

            // 3. register that `cause` directly lead to `consequence`.
            if let Some(consequences) = cause_extensions.get_mut::<Consequences>() {
                consequences.direct.insert(consequence_id_and_metadata);
            } else {
                cause_extensions.insert(Consequences::with_direct(consequence_id_and_metadata));
            }
        }
    }

    fn on_follows_from(
        &self,
        consequence_id_and_metadata: &Id,
        cause_id_and_metadata: &Id,
        ctx: Context<'_, S>,
    ) {
        use data::IndirectCauses;

        if cause_id_and_metadata == consequence_id_and_metadata {
            return self.on_follows_self(consequence_id_and_metadata, ctx);
        }

        let cause = ctx.span(cause_id_and_metadata).expect(
            "The `cause_id_and_metadata` provided to 
            `tracing_causality::Layer::on_follows_from` did not correspond to \
            an opened `Span` for the underlying subscriber. This span may have \
            already been closed, or been assigned by a different subscriber, \
            or there may be a bug in the subscriber underlying this layer.",
        );

        let consequence = ctx.span(consequence_id_and_metadata).expect(
            "The `consequence_id_and_metadata` provided to 
            `tracing_causality::Layer::on_follows_from` did not correspond to \
            an opened `Span` for the underlying subscriber. This span may have \
            already been closed, or been assigned by a different subscriber, \
            or there may be a bug in the subscriber underlying this layer.",
        );

        let cause_id_and_metadata = Span {
            id: cause_id_and_metadata.to_owned(),
            metadata: cause.metadata(),
        };

        let consequence_id_and_metadata = Span {
            id: consequence_id_and_metadata.to_owned(),
            metadata: consequence.metadata(),
        };

        let mut cause_data = cause.extensions_mut();
        let mut consequence_data = consequence.extensions_mut();

        // 1. insert `consequence` as an indirect consequence of `cause`
        if let Some(consequences) = cause_data.get_mut::<Consequences>() {
            consequences
                .indirect
                .insert(consequence_id_and_metadata.clone());
        } else {
            cause_data.insert(Consequences::with_indirect(
                consequence_id_and_metadata.clone(),
            ));
        }

        // 2. insert `cause` as an indirect cause of `consequence`
        if let Some(follows_from) = consequence_data.get_mut::<IndirectCauses>() {
            follows_from.add_cause(cause_id_and_metadata.clone());
        } else {
            consequence_data.insert(IndirectCauses::with_cause(cause_id_and_metadata.clone()));
        }

        if let Some(listeners) = cause_data.get_mut::<Listeners>() {
            // 3. notify causes's listeners that it indirectly lead to `consequence`
            channel::Sender::broadcast(
                listeners,
                Update::NewIndirect {
                    cause: cause_id_and_metadata,
                    consequence: consequence_id_and_metadata,
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

        let closed_id_and_metadata = Span {
            id: id.to_owned(),
            metadata: span.metadata(),
        };

        // `None` if this span is not its own immediate indirect cause,
        // otherwise `Some(indirect_causes)`.
        let mut is_cyclic = None;

        // 1. delete `id` as a consequence from each of its indirect causes
        if let Some(follows_from) = extensions.remove::<IndirectCauses>() {
            let indirect_causes: Vec<Span> = follows_from.causes.into_iter().collect();

            let drop_update = Update::CloseIndirect {
                span: closed_id_and_metadata.clone(),
                indirect_causes: indirect_causes.clone(),
            };

            for cause in &indirect_causes {
                if &cause.id == &id {
                    is_cyclic = Some(indirect_causes.clone());
                    continue;
                } else if let Some(cause) = ctx.span(&cause.id) {
                    let mut extensions = cause.extensions_mut();

                    if let Some(consequences) = extensions.get_mut::<Consequences>() {
                        consequences.remove_indirect(&closed_id_and_metadata);
                    }

                    if let Some(listeners) = extensions.get_mut::<Listeners>() {
                        channel::Sender::broadcast(listeners, drop_update.clone());
                    }
                } else {
                    // `cause_id_and_metadata` corresponds to a `Span` that has already been
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
                consequences.remove_direct(&closed_id_and_metadata);
            }
        }

        // 3. notify listeners, if any, that `id` was dropped
        if let Some(listeners) = extensions.get_mut::<Listeners>() {
            let update = if let Some(indirect_causes) = is_cyclic {
                Update::CloseCyclic {
                    span: closed_id_and_metadata,
                    direct_cause: direct_cause.map(|c| Span {
                        id: c.id(),
                        metadata: c.metadata(),
                    }),
                    indirect_causes,
                }
            } else {
                Update::CloseDirect {
                    span: closed_id_and_metadata,
                    direct_cause: direct_cause.map(|c| Span {
                        id: c.id(),
                        metadata: c.metadata(),
                    }),
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
            let a_id_and_metadata = causality::Span {
                id: a.id().unwrap(),
                metadata: a.metadata().unwrap(),
            };

            assert!(registry
                .span_data(&a_id_and_metadata.id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            let (_trace, _updates) =
                causality::trace(registry, &a_id_and_metadata.id, 1024).unwrap();

            // after `trace`, there should be 1 listener on `a`
            assert_eq!(
                registry
                    .span_data(&a_id_and_metadata.id)
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
            let a_id_and_metadata = causality::Span {
                id: a.id().unwrap(),
                metadata: a.metadata().unwrap(),
            };

            let b = a.in_scope(|| tracing::trace_span!("b"));
            let b_id_and_metadata = causality::Span {
                id: b.id().unwrap(),
                metadata: b.metadata().unwrap(),
            };

            assert!(registry
                .span_data(&a_id_and_metadata.id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            assert!(registry
                .span_data(&b_id_and_metadata.id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            let (_trace, _updates) =
                causality::trace(registry, &a_id_and_metadata.id, 1024).unwrap();

            // after `trace`, there should be 1 listener on `a`
            assert_eq!(
                registry
                    .span_data(&a_id_and_metadata.id)
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
                    .span_data(&b_id_and_metadata.id)
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
            let a_id_and_metadata = causality::Span {
                id: a.id().unwrap(),
                metadata: a.metadata().unwrap(),
            };

            let b = a.in_scope(|| tracing::trace_span!("b"));
            let b_id_and_metadata = causality::Span {
                id: b.id().unwrap(),
                metadata: b.metadata().unwrap(),
            };

            assert!(registry
                .span_data(&a_id_and_metadata.id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            assert!(registry
                .span_data(&b_id_and_metadata.id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            // trace `b`
            let (_trace, _updates) =
                causality::trace(registry, &b_id_and_metadata.id, 1024).unwrap();

            // after `trace`, there should be 0 listeners on `a`
            assert!(registry
                .span_data(&a_id_and_metadata.id)
                .unwrap()
                .extensions()
                .get::<crate::Listeners>()
                .is_none());

            // after `trace`, there should be 1 listener on `b`
            assert_eq!(
                registry
                    .span_data(&b_id_and_metadata.id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on this span")
                    .len(),
                1
            );

            // trace `a`
            let (_trace, _updates) =
                causality::trace(registry, &a_id_and_metadata.id, 1024).unwrap();

            // after `trace`, there should be 1 listener on `a`
            assert_eq!(
                registry
                    .span_data(&a_id_and_metadata.id)
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
                    .span_data(&b_id_and_metadata.id)
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
                let a_id_and_metadata = causality::Span {
                    id: a.id().unwrap(),
                    metadata: a.metadata().unwrap(),
                };

                // prior to `trace`, there are no listeners on `a`
                assert!(registry
                    .span_data(&a_id_and_metadata.id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .is_none());

                let (_trace, updates) =
                    causality::trace(registry, &a_id_and_metadata.id, 1024).unwrap();

                // after `trace`, there should be 1 listener on `a`
                assert_eq!(
                    registry
                        .span_data(&a_id_and_metadata.id)
                        .unwrap()
                        .extensions()
                        .get::<crate::Listeners>()
                        .expect("there should be listeners on this span")
                        .len(),
                    1
                );

                let b = a.in_scope(|| tracing::trace_span!("b"));
                let b_id_and_metadata = causality::Span {
                    id: b.id().unwrap(),
                    metadata: b.metadata().unwrap(),
                };

                assert_eq!(
                    updates.next(),
                    Some(Update::OpenDirect {
                        cause: a_id_and_metadata,
                        consequence: b_id_and_metadata,
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
                let a_id_and_metadata = causality::Span {
                    id: a.id().unwrap(),
                    metadata: a.metadata().unwrap(),
                };

                let (_trace, _updates) =
                    causality::trace(registry, &a_id_and_metadata.id, 1024).unwrap();

                let b = a.in_scope(|| tracing::trace_span!("b"));
                let b_id_and_metadata = causality::Span {
                    id: b.id().unwrap(),
                    metadata: b.metadata().unwrap(),
                };

                let (_trace, _updates) =
                    causality::trace(registry, &b_id_and_metadata.id, 1024).unwrap();

                let a_listeners = registry
                    .span_data(&a_id_and_metadata.id)
                    .unwrap()
                    .extensions()
                    .get::<crate::Listeners>()
                    .expect("there should be listeners on span `a`")
                    .clone();

                let b_listeners = registry
                    .span_data(&b_id_and_metadata.id)
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
                let a_id_and_metadata = causality::Span {
                    id: a.id().unwrap(),
                    metadata: a.metadata().unwrap(),
                };

                let a_consequences = causality::consequences(registry, &a_id_and_metadata.id)
                    .expect("span `a` should not have been closed yet");

                assert_eq!(
                    a_consequences,
                    Consequences::default(),
                    "span `a` should not have any consequences"
                );

                let b = a.in_scope(|| tracing::trace_span!("b"));
                let b_id_and_metadata = causality::Span {
                    id: b.id().unwrap(),
                    metadata: b.metadata().unwrap(),
                };

                let a_consequences = causality::consequences(registry, &a_id_and_metadata.id)
                    .expect("span `a` should not have been closed yet");

                assert_eq!(
                    a_consequences,
                    Consequences::with_direct(b_id_and_metadata),
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
                let cause_id_and_metadata = causality::Span {
                    id: cause.id().unwrap(),
                    metadata: cause.metadata().unwrap(),
                };

                let consequence = tracing::trace_span!("consequence");
                let consequence_id_and_metadata = causality::Span {
                    id: consequence.id().unwrap(),
                    metadata: consequence.metadata().unwrap(),
                };

                let consequences = causality::consequences(registry, &cause_id_and_metadata.id)
                    .expect("span `cause` should not have been closed yet");

                assert_eq!(
                    consequences,
                    Consequences::default(),
                    "span `cause` should not have any consequences"
                );

                consequence.follows_from(&cause_id_and_metadata.id);

                let consequences = causality::consequences(registry, &cause_id_and_metadata.id)
                    .expect("span `cause` should not have been closed yet");

                assert_eq!(
                    consequences,
                    Consequences::with_indirect(consequence_id_and_metadata),
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
                let cause_id_and_metadata = causality::Span {
                    id: cause.id().unwrap(),
                    metadata: cause.metadata().unwrap(),
                };

                let consequence = tracing::trace_span!("consequence");
                let consequence_id_and_metadata = causality::Span {
                    id: consequence.id().unwrap(),
                    metadata: consequence.metadata().unwrap(),
                };

                assert!(
                    registry
                        .span_data(&consequence_id_and_metadata.id)
                        .expect("span `consequence` should not yet be closed.")
                        .extensions()
                        .get::<crate::data::IndirectCauses>()
                        .is_none(),
                    "span `consequence` should not yet have `IndirectCauses`"
                );

                consequence.follows_from(&cause_id_and_metadata.id);

                assert!(
                    registry
                        .span_data(&consequence_id_and_metadata.id)
                        .expect("span `consequence` should not yet be closed.")
                        .extensions()
                        .get::<crate::data::IndirectCauses>()
                        .expect("span `consequence` should have `IndirectCauses`")
                        .contains(&cause_id_and_metadata),
                    "`consequence`'s `IndirectCauses` should contain `cause_id_and_metadata`"
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
                let cause_id_and_metadata = causality::Span {
                    id: cause.id().unwrap(),
                    metadata: cause.metadata().unwrap(),
                };

                let consequence = tracing::trace_span!("consequence");
                let consequence_id_and_metadata = causality::Span {
                    id: consequence.id().unwrap(),
                    metadata: consequence.metadata().unwrap(),
                };

                let (_trace, cause_updates) =
                    crate::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
                let (_trace, consequence_updates) =
                    crate::trace(registry, &consequence_id_and_metadata.id, 1024).unwrap();

                assert!(consequence_updates.is_empty());
                assert!(cause_updates.is_empty());

                consequence.follows_from(&cause_id_and_metadata.id);

                assert!(
                    consequence_updates.is_empty(),
                    "The listeners on `consequence` should not have been \
                    notified of anything."
                );
                assert_eq!(
                    cause_updates.next(),
                    Some(Update::NewIndirect {
                        cause: cause_id_and_metadata.clone(),
                        consequence: consequence_id_and_metadata.clone(),
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
                let cause_id_and_metadata = causality::Span {
                    id: cause.id().unwrap(),
                    metadata: cause.metadata().unwrap(),
                };

                let consequence = tracing::trace_span!("consequence");
                let consequence_id_and_metadata = causality::Span {
                    id: consequence.id().unwrap(),
                    metadata: consequence.metadata().unwrap(),
                };

                let (_trace, _updates) =
                    crate::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
                let (_trace, _updates) =
                    crate::trace(registry, &consequence_id_and_metadata.id, 1024).unwrap();

                assert_eq!(
                    causality::consequences(registry, &cause_id_and_metadata.id)
                        .expect("span `cause` should not have been closed yet"),
                    Consequences::default(),
                    "span `cause` should not have any consequences"
                );

                consequence.follows_from(&cause_id_and_metadata.id);

                assert_eq!(
                    causality::consequences(registry, &cause_id_and_metadata.id)
                        .expect("span `cause` should not have been closed yet"),
                    Consequences::with_indirect(consequence_id_and_metadata.clone()),
                    "span `cause` should have one indirect consequence"
                );

                drop(consequence);

                assert_eq!(
                    causality::consequences(registry, &cause_id_and_metadata.id)
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
                let cause_id_and_metadata = causality::Span {
                    id: cause.id().unwrap(),
                    metadata: cause.metadata().unwrap(),
                };

                let consequence = tracing::trace_span!("consequence");
                let consequence_id_and_metadata = causality::Span {
                    id: consequence.id().unwrap(),
                    metadata: consequence.metadata().unwrap(),
                };

                consequence.follows_from(&cause_id_and_metadata.id);

                let (_trace, cause_updates) =
                    crate::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
                let (_trace, _consequence_updates) =
                    crate::trace(registry, &consequence_id_and_metadata.id, 1024).unwrap();

                drop(consequence);

                assert_eq!(
                    cause_updates.next(),
                    Some(Update::CloseIndirect {
                        span: consequence_id_and_metadata.clone(),
                        indirect_causes: vec![cause_id_and_metadata.clone()],
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
                let cause_id_and_metadata = causality::Span {
                    id: cause.id().unwrap(),
                    metadata: cause.metadata().unwrap(),
                };

                let consequence = cause.clone();
                let consequence_id_and_metadata = causality::Span {
                    id: consequence.id().unwrap(),
                    metadata: consequence.metadata().unwrap(),
                };

                consequence.follows_from(&cause_id_and_metadata.id);

                let (_trace, cause_updates) =
                    crate::trace(registry, &cause_id_and_metadata.id, 1024).unwrap();
                let (_trace, _consequence_updates) =
                    crate::trace(registry, &consequence_id_and_metadata.id, 1024).unwrap();

                drop([cause, consequence]);

                assert_eq!(
                    cause_updates.next(),
                    Some(Update::CloseCyclic {
                        span: consequence_id_and_metadata.clone(),
                        direct_cause: None,
                        indirect_causes: vec![cause_id_and_metadata.clone()],
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
    use crate::{self as causality, Consequences, Update, Updates};
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
        let a_id_and_metadata = causality::Span {
            id: a.id().unwrap(),
            metadata: a.metadata().unwrap(),
        };

        let b = a.in_scope(|| tracing::trace_span!("b"));
        let b_id_and_metadata = causality::Span {
            id: b.id().unwrap(),
            metadata: b.metadata().unwrap(),
        };

        let (trace, updates) = crate::trace(subscriber, &a_id_and_metadata.id, 1).unwrap();
        assert!(trace
            .consequences(&a_id_and_metadata)
            .unwrap()
            .contains_direct(&b_id_and_metadata));

        let c = b.in_scope(|| tracing::trace_span!("c"));
        let c_id_and_metadata = causality::Span {
            id: c.id().unwrap(),
            metadata: c.metadata().unwrap(),
        };

        dbg!(subscriber
            .span_data(&b_id_and_metadata.id)
            .unwrap()
            .extensions()
            .get::<crate::Listeners>()
            .is_some());

        assert_eq!(
            updates.next(),
            Some(crate::Update::OpenDirect {
                cause: b_id_and_metadata,
                consequence: c_id_and_metadata,
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
        let a_id_and_metadata = causality::Span {
            id: a.id().unwrap(),
            metadata: a.metadata().unwrap(),
        };

        let (_trace, updates) = crate::trace(subscriber, &a_id_and_metadata.id, 1024).unwrap();

        let b = a.in_scope(|| tracing::trace_span!("b"));
        let b_id_and_metadata = causality::Span {
            id: b.id().unwrap(),
            metadata: b.metadata().unwrap(),
        };

        let c = b.in_scope(|| tracing::trace_span!("c"));
        let c_id_and_metadata = causality::Span {
            id: c.id().unwrap(),
            metadata: c.metadata().unwrap(),
        };

        dbg!(subscriber
            .span_data(&b_id_and_metadata.id)
            .unwrap()
            .extensions()
            .get::<crate::Listeners>()
            .is_some());

        dbg!(subscriber
            .span_data(&c_id_and_metadata.id)
            .unwrap()
            .extensions()
            .get::<crate::Listeners>()
            .is_some());

        assert_eq!(
            updates.next(),
            Some(crate::Update::OpenDirect {
                cause: a_id_and_metadata,
                consequence: b_id_and_metadata.clone(),
            })
        );

        assert_eq!(
            updates.next(),
            Some(crate::Update::OpenDirect {
                cause: b_id_and_metadata,
                consequence: c_id_and_metadata,
            })
        );
    }
}
