//! Data associated with spans.

use std::collections::{BTreeSet, HashSet};
use tracing_core::span::Id;

/// The consequences — direct and indirect — of a `Span`.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Consequences {
    pub(crate) direct: HashSet<Id>,
    pub(crate) indirect: HashSet<Id>,
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
    pub fn with_direct(direct: Id) -> Self {
        let mut consequences = Self::none();
        consequences.direct.insert(direct);
        consequences
    }

    /// Constructs a `Consequences` with the given indirect consequence.
    pub fn with_indirect(indirect: Id) -> Self {
        let mut consequences = Self::none();
        consequences.indirect.insert(indirect);
        consequences
    }

    /// Add the given direct consequence.
    pub(crate) fn add_direct(&mut self, direct: Id) {
        self.direct.insert(direct);
    }

    /// Add the given indirect consequence.
    pub(crate) fn add_indirect(&mut self, indirect: Id) {
        self.indirect.insert(indirect);
    }

    /// Remove the given direct consequence.
    pub(crate) fn remove_direct(&mut self, direct: &Id) {
        self.direct.remove(direct);
    }

    /// Remove the given indirect consequence.
    pub(crate) fn remove_indirect(&mut self, indirect: &Id) {
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
    /// let root_id = root.id().unwrap();
    /// let consequence = root.in_scope(|| trace_span!("consequence"));
    /// let consequence_id = consequence.id().unwrap();
    ///
    /// let root_data = registry.span_data(&root_id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert!(root_consequences.contains_direct(&consequence_id));
    /// ```
    pub fn contains_direct(&self, id: &Id) -> bool {
        self.direct.contains(id)
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
    /// let root_id = root.id().unwrap();
    /// let consequence = trace_span!("consequence");
    /// let consequence_id = consequence.id().unwrap();
    /// consequence.follows_from(&root);
    ///
    /// let root_data = registry.span_data(&root_id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert!(root_consequences.contains_indirect(&consequence_id));
    /// ```
    pub fn contains_indirect(&self, id: &Id) -> bool {
        self.indirect.contains(id)
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
    /// let root_id = root.id().unwrap();
    /// let consequence = root.in_scope(|| trace_span!("consequence"));
    /// let consequence_id = consequence.id().unwrap();
    ///
    /// let root_data = registry.span_data(&root_id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert_eq!(
    ///     root_consequences.iter_direct().next(),
    ///     Some(consequence_id)
    /// );
    /// ```
    pub fn iter_direct(&self) -> impl Iterator<Item = Id> + '_ {
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
    /// let root_id = root.id().unwrap();
    /// let consequence = trace_span!("consequence");
    /// let consequence_id = consequence.id().unwrap();
    /// consequence.follows_from(&root);
    ///
    /// let root_data = registry.span_data(&root_id).unwrap();
    /// let root_extensions = root_data.extensions();
    /// let root_consequences = root_extensions.get::<Consequences>().unwrap();
    /// assert_eq!(
    ///     root_consequences.iter_indirect().next(),
    ///     Some(consequence_id)
    /// );
    /// ```
    pub fn iter_indirect(&self) -> impl Iterator<Item = Id> + '_ {
        self.indirect.iter().cloned()
    }
}

/// The indirect (`follows_from`) causes of a `Span`.
pub struct IndirectCauses {
    pub(crate) causes: HashSet<Id>,
}

impl IndirectCauses {
    pub(crate) fn new() -> Self {
        Self {
            causes: HashSet::default(),
        }
    }

    pub(crate) fn add_cause(&mut self, cause: Id) {
        self.causes.insert(cause);
    }

    pub(crate) fn with_cause(cause: Id) -> Self {
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
    /// let root_id = root.id().unwrap();
    /// let consequence = trace_span!("consequence");
    /// let consequence_id = consequence.id().unwrap();
    /// consequence.follows_from(&root);
    /// consequence.follows_from(&consequence);
    ///
    /// let consequence_data = registry.span_data(&consequence_id).unwrap();
    /// let consequence_extensions = consequence_data.extensions();
    /// let consequence_causes = consequence_extensions.get::<IndirectCauses>().unwrap();
    /// assert!(consequence_causes.contains(&root_id));
    /// assert!(consequence_causes.contains(&consequence_id));
    /// ```
    pub fn contains(&self, id: &Id) -> bool {
        self.causes.contains(id)
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
    /// let root_id = root.id().unwrap();
    /// let consequence = trace_span!("consequence");
    /// let consequence_id = consequence.id().unwrap();
    /// consequence.follows_from(&root);
    ///
    /// let consequence_data = registry.span_data(&consequence_id).unwrap();
    /// let consequence_extensions = consequence_data.extensions();
    /// let consequence_causes = consequence_extensions.get::<IndirectCauses>().unwrap();
    /// assert_eq!(
    ///     consequence_causes.iter().next(),
    ///     Some(&root_id)
    /// );
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &Id> {
        self.causes.iter()
    }
}

pub(crate) type Listeners = BTreeSet<crate::channel::Sender>;
