//! Data associated with spans.

use crate::Span;
use std::collections::{BTreeSet, HashSet};
use tracing_core::span::Id;

/// The consequences — direct and indirect — of a `Span`.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Consequences {
    pub(crate) direct: HashSet<Span>,
    pub(crate) indirect: HashSet<Span>,
}

impl Consequences {
    /// Constructs a new, empty `Consequences`.
    pub fn none() -> Self {
        Self {
            direct: HashSet::default(),
            indirect: HashSet::default(),
        }
    }

    /// Constructs a `Consequences` with the given direct consequence.
    pub fn with_direct(direct: Span) -> Self {
        let mut consequences = Self::none();
        consequences.direct.insert(direct);
        consequences
    }

    /// Constructs a `Consequences` with the given indirect consequence.
    pub fn with_indirect(indirect: Span) -> Self {
        let mut consequences = Self::none();
        consequences.indirect.insert(indirect);
        consequences
    }

    /// Add the given direct consequence.
    pub fn add_direct(&mut self, direct: Span) {
        self.direct.insert(direct);
    }

    /// Add the given indirect consequence.
    pub fn add_indirect(&mut self, indirect: Span) {
        self.indirect.insert(indirect);
    }

    /// Remove the given direct consequence.
    pub(crate) fn remove_direct(&mut self, direct: &Span) {
        self.direct.remove(direct);
    }

    /// Remove the given indirect consequence.
    pub(crate) fn remove_indirect(&mut self, indirect: &Span) {
        self.indirect.remove(indirect);
    }

    /// Returns `true` if the given `id` is among this span's direct consequences.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, Consequences};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// let subscriber: Arc<dyn Subscriber + Send + Sync > =
    ///     Arc::new(Registry::default().with(causality::Layer));
    /// subscriber.clone().init();
    /// let subscriber: Arc<dyn Subscriber> = subscriber;
    /// let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    /// let root = trace_span!("root");
    /// let root_id_and_metadata = causality::Span {
    ///     id: root.id().unwrap(),
    ///     metadata: root.metadata().unwrap()
    /// };
    /// let consequence = root.in_scope(|| trace_span!("consequence"));
    /// let consequence_id_and_metadata = causality::Span {
    ///     id: consequence.id().unwrap(),
    ///     metadata: consequence.metadata().unwrap()
    /// };
    ///
    /// let root_data = registry.span_data(&root_id_and_metadata.id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert!(root_consequences.contains_direct(&consequence_id_and_metadata));
    /// ```
    pub fn contains_direct(&self, span: &Span) -> bool {
        self.direct.contains(span)
    }

    /// Returns `true` if the given `id` is among this span's indirect consequences.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, Consequences};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// let subscriber: Arc<dyn Subscriber + Send + Sync > =
    ///     Arc::new(Registry::default().with(causality::Layer));
    /// subscriber.clone().init();
    /// let subscriber: Arc<dyn Subscriber> = subscriber;
    /// let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    /// let root = trace_span!("root");
    /// let root_id_and_metadata = causality::Span {
    ///     id: root.id().unwrap(),
    ///     metadata: root.metadata().unwrap()
    /// };
    /// let consequence = trace_span!("consequence");
    /// let consequence_id_and_metadata = causality::Span {
    ///     id: consequence.id().unwrap(),
    ///     metadata: consequence.metadata().unwrap()
    /// };
    /// consequence.follows_from(&root_id_and_metadata.id);
    ///
    /// let root_data = registry.span_data(&root_id_and_metadata.id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert!(root_consequences.contains_indirect(&consequence_id_and_metadata));
    /// ```
    pub fn contains_indirect(&self, span: &Span) -> bool {
        self.indirect.contains(span)
    }

    /// An iterator visiting all direct consequences in arbitrary order.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, Consequences};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// let subscriber: Arc<dyn Subscriber + Send + Sync > =
    ///     Arc::new(Registry::default().with(causality::Layer));
    /// subscriber.clone().init();
    /// let subscriber: Arc<dyn Subscriber> = subscriber;
    /// let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    /// let root = trace_span!("root");
    /// let root_id_and_metadata = causality::Span {
    ///     id: root.id().unwrap(),
    ///     metadata: root.metadata().unwrap()
    /// };
    /// let consequence = root.in_scope(|| trace_span!("consequence"));
    /// let consequence_id_and_metadata = causality::Span {
    ///     id: consequence.id().unwrap(),
    ///     metadata: consequence.metadata().unwrap()
    /// };
    ///
    /// let root_data = registry.span_data(&root_id_and_metadata.id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert_eq!(
    ///     root_consequences.iter_direct().next(),
    ///     Some(consequence_id_and_metadata)
    /// );
    /// ```
    pub fn iter_direct(&self) -> impl ExactSizeIterator<Item = Span> + '_ {
        self.direct.iter().cloned()
    }

    /// An iterator visiting all direct consequences in arbitrary order.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, Consequences};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// let subscriber: Arc<dyn Subscriber + Send + Sync > =
    ///     Arc::new(Registry::default().with(causality::Layer));
    /// subscriber.clone().init();
    /// let subscriber: Arc<dyn Subscriber> = subscriber;
    /// let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    /// let root = trace_span!("root");
    /// let root_id_and_metadata = causality::Span {
    ///     id: root.id().unwrap(),
    ///     metadata: root.metadata().unwrap()
    /// };
    /// let consequence = trace_span!("consequence");
    /// let consequence_id_and_metadata = causality::Span {
    ///     id: consequence.id().unwrap(),
    ///     metadata: consequence.metadata().unwrap()
    /// };
    /// consequence.follows_from(&root_id_and_metadata.id);
    ///
    /// let root_data = registry.span_data(&root_id_and_metadata.id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert_eq!(
    ///     root_consequences.iter_indirect().next(),
    ///     Some(consequence_id_and_metadata)
    /// );
    /// ```
    pub fn iter_indirect(&self) -> impl ExactSizeIterator<Item = Span> + '_ {
        self.indirect.iter().cloned()
    }
}

/// The indirect (`follows_from`) causes of a `Span`.
pub struct IndirectCauses {
    pub(crate) causes: HashSet<Span>,
}

impl IndirectCauses {
    pub(crate) fn new() -> Self {
        Self {
            causes: HashSet::default(),
        }
    }

    pub(crate) fn add_cause(&mut self, cause: Span) {
        self.causes.insert(cause);
    }

    pub(crate) fn with_cause(cause: Span) -> Self {
        let mut follows_from = Self::new();
        follows_from.add_cause(cause);
        follows_from
    }

    /// Returns `true` if the given `id` is among this span's indirect causes.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, data::IndirectCauses};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// let subscriber: Arc<dyn Subscriber + Send + Sync > =
    ///     Arc::new(Registry::default().with(causality::Layer));
    /// subscriber.clone().init();
    /// let subscriber: Arc<dyn Subscriber> = subscriber;
    /// let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    /// let root = trace_span!("root");
    /// let root_id_and_metadata = causality::Span {
    ///     id: root.id().unwrap(),
    ///     metadata: root.metadata().unwrap()
    /// };
    /// let consequence = trace_span!("consequence");
    /// let consequence_id_and_metadata = causality::Span {
    ///     id: consequence.id().unwrap(),
    ///     metadata: consequence.metadata().unwrap()
    /// };
    /// consequence.follows_from(&root_id_and_metadata.id);
    /// consequence.follows_from(&consequence_id_and_metadata.id);
    ///
    /// let consequence_data = registry.span_data(&consequence_id_and_metadata.id).unwrap();
    /// let consequence_extensions = consequence_data.extensions();
    /// let consequence_causes = consequence_extensions.get::<IndirectCauses>().unwrap();
    /// assert!(consequence_causes.contains(&root_id_and_metadata));
    /// assert!(consequence_causes.contains(&consequence_id_and_metadata));
    /// ```
    pub fn contains(&self, span: &Span) -> bool {
        self.causes.contains(span)
    }

    /// Produces an iterator over this span's indirect causes.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use tracing::{Subscriber, trace_span};
    /// use tracing_causality::{self as causality, data::IndirectCauses};
    /// use tracing_subscriber::{prelude::*, registry::{LookupSpan, SpanData, Registry}};
    ///
    /// let subscriber: Arc<dyn Subscriber + Send + Sync > =
    ///     Arc::new(Registry::default().with(causality::Layer));
    /// subscriber.clone().init();
    /// let subscriber: Arc<dyn Subscriber> = subscriber;
    /// let registry = subscriber.downcast_ref::<Registry>().unwrap();
    ///
    /// let root = trace_span!("root");
    /// let root_id_and_metadata = causality::Span {
    ///     id: root.id().unwrap(),
    ///     metadata: root.metadata().unwrap()
    /// };
    /// let consequence = trace_span!("consequence");
    /// let consequence_id_and_metadata = causality::Span {
    ///     id: consequence.id().unwrap(),
    ///     metadata: consequence.metadata().unwrap()
    /// };
    /// consequence.follows_from(&root_id_and_metadata.id);
    ///
    /// let consequence_data = registry.span_data(&consequence_id_and_metadata.id).unwrap();
    /// let consequence_extensions = consequence_data.extensions();
    /// let consequence_causes = consequence_extensions.get::<IndirectCauses>().unwrap();
    /// assert_eq!(
    ///     consequence_causes.iter().next(),
    ///     Some(&root_id_and_metadata)
    /// );
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &Span> {
        self.causes.iter()
    }
}

pub(crate) type Listeners = BTreeSet<crate::channel::Sender>;
