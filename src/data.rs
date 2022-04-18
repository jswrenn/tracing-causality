//! Data associated with spans.

use std::collections::HashSet;
use tracing_core::span::Id;

/// The consequences — direct and indirect — of a `Span`.
#[derive(Clone)]
pub struct Consequences {
    pub direct: HashSet<Id>,
    pub indirect: HashSet<Id>,
}

impl Consequences {
    pub(crate) fn new() -> Self {
        Self {
            direct: HashSet::default(),
            indirect: HashSet::default(),
        }
    }

    pub(crate) fn with_direct(direct: Id) -> Self {
        let mut consequences = Self::new();
        consequences.direct.insert(direct);
        consequences
    }

    pub(crate) fn with_indirect(indirect: Id) -> Self {
        let mut consequences = Self::new();
        consequences.indirect.insert(indirect);
        consequences
    }

    pub(crate) fn add_direct(&mut self, direct: Id) {
        self.direct.insert(direct);
    }

    pub(crate) fn add_indirect(&mut self, indirect: Id) {
        self.indirect.insert(indirect);
    }

    pub(crate) fn remove_direct(&mut self, direct: &Id) {
        self.direct.remove(direct);
    }

    pub(crate) fn remove_indirect(&mut self, indirect: &Id) {
        self.indirect.remove(indirect);
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
}

pub(crate) type Listeners = Vec<crate::channel::Sender>;
