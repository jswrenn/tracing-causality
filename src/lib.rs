use dashmap::{DashMap, DashSet};
use indexmap::{IndexMap, IndexSet};
use std::iter::ExactSizeIterator;
use std::sync::{Arc, RwLock, RwLockWriteGuard};
use tracing_core::span::{Attributes, Id};
use tracing_core::subscriber::Subscriber;
use tracing_subscriber::layer::Context;
use tracing_subscriber::registry::LookupSpan;

/// The immediate consequences of a span.
#[derive(Default, Debug, Clone)]
struct Causality<Consequences, Causes> {
    /// The direct (parent–child) consequences of a span.
    direct: Consequences,
    /// The indirect (follows-from) consequences of a span.
    indirect: Consequences,
    /// This span was, indirectly, caused by.
    indirectly_caused_by: Causes,
}

/// A concurrently-updatable set of causal trees.
type ConcurrentCausalTrees = DashMap<Id, Causality<DashSet<Id>, DashSet<Id>>>;

/// A lockable [`ConcurrentCausalTrees`].
type LockableCausalTrees = RwLock<ConcurrentCausalTrees>;

/// A locked [`ConcurrentCausalTrees`].
type LockedCausalTrees<'a> = RwLockWriteGuard<'a, ConcurrentCausalTrees>;

/// An immutable causality trace tree, rooted at a given [`Id`].
#[derive(Debug, Clone)]
pub struct Trace {
    /// The root [`Id`] of this [`Trace`]'s tree.
    pub root: Id,
    /// The causality trace, rooted at `Trace::root`.
    tree: IndexMap<Id, Causality<IndexSet<Id>, ()>>,
}

impl Trace {
    /// If the given `id` is part of this [`Trace`], produces an iterator over
    /// the [`Id`]s of spans with a direct (parent–child) causal relationship to
    /// the span with the given `id`.
    ///
    /// The [`Id`]s produced by this iterator are guaranteed to appear in
    /// [`Trace`].
    ///
    /// Produces `None` if `id` is not a part of this [`Trace`].
    pub fn direct(&self, id: &Id) -> Option<impl ExactSizeIterator<Item = &Id>> {
        self.tree
            .get(id)
            .map(|consequences| consequences.direct.iter())
    }

    /// If the given `id` is part of this [`Trace`], produces an iterator over
    /// the [`Id`]s of spans with a indirect (follows_from) causal relationship
    /// to the given `id`.
    ///
    /// The [`Id`]s produced by this iterator are **not** guaranteed to appear
    /// in [`Trace`].
    ///
    /// Produces `None` if `id` is not a part of this [`Trace`].
    pub fn indirect(&self, id: &Id) -> Option<impl ExactSizeIterator<Item = &Id>> {
        self.tree
            .get(id)
            .map(|consequences| consequences.indirect.iter())
    }
}

impl Trace {
    /// Traverse the given graph to produce a trace rooted at the given `Id`.
    fn of<'a>(trees: &'a ConcurrentCausalTrees, id: Id) -> Self {
        let mut trace = Self {
            root: id.clone(),
            tree: Default::default(),
        };
        // the queue of vertices (span ids) that remain to be visited
        let mut queue = vec![id];
        while let Some(id) = queue.pop() {
            let trace_vertex = trace.tree.entry(id.clone()).or_default();
            if let Some(consequences) = trees.get(&id) {
                // reserve space for `id`'s consequences
                queue.reserve(consequences.direct.len());
                trace_vertex.direct.reserve(consequences.direct.len());
                trace_vertex.indirect.reserve(consequences.indirect.len());

                // copy the direct consequences
                for direct_consequence in consequences.direct.iter() {
                    queue.push(direct_consequence.clone());
                    trace_vertex.direct.insert(direct_consequence.clone());
                }

                // copy the indirect consequences
                for indirect_consequence in consequences.indirect.iter() {
                    trace_vertex.direct.insert(indirect_consequence.clone());
                }
            }
        }
        trace
    }
}

/// A concurrently-updated set of causal trees for tracing spans.
#[derive(Debug, Clone)]
pub struct Traces {
    trees: Arc<LockableCausalTrees>,
}

/// An exclusive lock on [`Traces`].
///
/// Acquire this lock by calling [`Traces::lock`].
///
/// While this lock is held, the causality graph shared by [`Traces`]
/// and [`Layer`] is read-only. This ensures that the [`Trace`]s
/// produced by [`Lock::consequences`] are consistent with
/// respect to the instant that method is invoked.
///
/// This lock should only ever be held very briefly, as holding it will cause
/// [`Layer`] to block.
pub struct Lock<'tracing_causality> {
    trees: LockedCausalTrees<'tracing_causality>,
}

impl<'tracing_causality> Lock<'tracing_causality> {
    /// Produce the [`Trace`] rooted at the given [`Id`].
    ///
    /// The produced [`Trace`] will be consistent with respect to the instant
    /// this method is invoked.
    pub fn consequences(&self, id: Id) -> Trace {
        Trace::of(&self.trees, id.clone())
    }
    
    /// Release this [`Lock`]. Dropping this [`Lock`] has the same effect.
    pub fn release(self) {
        let _ = self;
    }
}

impl Traces {
    /// Constructs a [`Traces`].
    pub fn new() -> Self {
        Self {
            trees: Arc::new(LockableCausalTrees::default()),
        }
    }

    /// Produces a [tracing-subscriber `Layer`][tracing-layer] concurrently
    /// updates this [`Traces`] with the causal relationship between spans.
    ///
    /// [tracing-layer]: tracing_subscriber::layer::Layer
    pub fn layer(&self) -> Layer {
        Layer {
            trees: self.trees.clone(),
        }
    }

    /// Secure an exclusive lock on [`Traces`].
    ///
    /// While this lock is held, the causality graph shared by
    /// [`Traces`] and [`Layer`] is read-only. This ensures
    /// that the [`Trace`]s produced by [`Lock::consequences`]
    /// are consistent with respect to the instant that method is invoked.
    ///
    /// This lock should only ever be held very briefly, as holding it will
    /// cause [`Layer`] to block.
    pub fn lock(&self) -> Lock<'_> {
        Lock {
            trees: self.trees.write().unwrap_or_else(|e| unreachable!({ e })),
        }
    }

    /// Produce the [`Trace`] rooted at the given [`Id`].
    ///
    /// The underlying causality graph held by [`Traces`] and
    /// [`Layer`] may be updated concurrently *while* this method is
    /// traversing it to produce a trace.
    ///
    /// To instead produce a [`Trace`] over a frozen causality graph, first
    /// invoke [`Traces::lock`], then call [`Lock::consequences`].
    pub fn consequences(&self, id: Id) -> Trace {
        let graph = self.trees.read().unwrap_or_else(|e| unreachable!({ e }));
        Trace::of(&graph, id.clone())
    }
}

/// A [tracing-subscriber `Layer`][tracing-layer] that concurrently updates
/// [`Traces`].
///
/// Acquire the [`Layer`] corresponding to a [`Trace`] by calling
/// [`Traces::layer`].
///
/// [tracing-layer]: tracing_subscriber::layer::Layer
pub struct Layer {
    trees: Arc<LockableCausalTrees>,
}

impl<S> tracing_subscriber::layer::Layer<S> for Layer
where
    S: Subscriber + for<'span> LookupSpan<'span> + Send + Sync,
{
    fn on_new_span(&self, attrs: &Attributes<'_>, id: &Id, _ctx: Context<'_, S>) {
        let trees = self.trees.read().unwrap_or_else(|e| unreachable!({ e }));
        // add the span id as a vertex in the causality graph
        trees.insert(id.clone(), Default::default());
        // if the span has a parent, add an edge between the parent and the span
        if let Some(parent) = attrs.parent() {
            if let Some(consequences) = trees.get(parent) {
                consequences.direct.insert(id.clone());
            } else {
                panic!("parent {:?} closed before child {:?}", parent, id);
            }
        }
    }

    fn on_follows_from(&self, consequent: &Id, cause: &Id, _ctx: Context<'_, S>) {
        let trees = self.trees.read().unwrap_or_else(|e| unreachable!({ e }));
        // record that `consequent` is an indirect consequence of `cause`
        if let Some(causality) = trees.get(cause) {
            causality.indirect.insert(consequent.clone());
        } else {
            // If `cause` cannot be found in the causality graph, it suggests
            // that `cause` was, somehow, already closed by the time
            // `consequent` declared that it followed from `cause`.
            //
            // This should not occur; per the documentation of `Span::follows_from`:
            // > If this span is disabled, or the resulting follows-from
            // > relationship would be invalid, this function will do nothing.
            unreachable!(
                "consequent {:?} closed before cause {:?}",
                consequent, cause
            );
        };
        // record that `consequent`'s indirect causes includes `cause`
        if let Some(causality) = trees.get(consequent) {
            causality.indirectly_caused_by.insert(cause.clone());
        } else {
            // If `consequent` cannot be found in the causality graph, it
            // suggests that, somehow, `causality` was closed by the time it
            // declared that it followed from `cause`. This should be
            // impossible.
            unreachable!(
                "consequent {:?} closed before cause {:?}",
                consequent, cause
            );
        };
    }

    fn on_close(&self, id: Id, _ctx: Context<'_, S>) {
        let trees = self.trees.read().unwrap_or_else(|e| unreachable!({ e }));
        if let Some((_, causality)) = trees.remove(&id) {
            // Consider this scenario, in which `a` has the direct consequence
            // `b`; `d` indirectly follows from both `b` and `c`; and `e`
            // indirectly follows from `d`:
            //
            //     a━━━┓
            //         b───┐   ┌─e
            //             ├─d─┤
            //         c───┘   └─f
            //
            // Then, `d` is closed.
            //
            // What we'd like to happen in this scenario, is for `d` to
            // disappear as an indirect consequence of both `b` *and* `c`.
            //
            // To achieve this, spans also keep track of their indirect causes,
            // and for each of these indirect causes, we remove exinct span as
            // a consequence.
            for indirect_cause in causality.indirectly_caused_by {
                if let Some(consequences) = trees.get(&indirect_cause) {
                    consequences.indirect.remove(&id);
                } else {
                    // `indirect_cause` was, itself, closed while this function
                    // cleaned up after `id`, and thus handled it's own cleanup.
                }
            }
            // We'll also remove `d` from both `e.indirectly_caused_by`
            // and `f.indirectly_caused_by`:
            for indirect_consequence in causality.indirect {
                if let Some(causality) = trees.get(&indirect_consequence) {
                    causality.indirectly_caused_by.remove(&id);
                } else {
                    // TODO: fill this comment in.
                }
            }
            // We don't need to clean up `id`'s direct consequences, since they
            // will have been closed *before* `id`.
        } else {
            // If `id` cannot be found in the causality graph, either `on_close`
            // has been manually-invoked with an `id` *not* produced by `S`, or
            // `on_new_span` was not invoked for this `id`, or, somehow, the
            // span with this `id` has already been closed.
            panic!("span {:?} does not exist in causality graph", id);
        }
    }
}
