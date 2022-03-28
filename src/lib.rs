use std::fmt;
use std::iter::ExactSizeIterator;
use std::sync::{Arc, RwLock, RwLockWriteGuard};
use tracing_core::span::{Attributes, Id};
use tracing_core::subscriber::Subscriber;
use tracing_subscriber::layer::Context;
use tracing_subscriber::registry::LookupSpan;

#[derive(Clone, Debug, Default)]
struct Hasher;

impl std::hash::BuildHasher for Hasher {
    type Hasher = rustc_hash::FxHasher;

    fn build_hasher(&self) -> Self::Hasher {
        rustc_hash::FxHasher::default()
    }
}

type DashMap<K, V> = dashmap::DashMap<K, V, Hasher>;
type DashSet<V> = dashmap::DashSet<V, Hasher>;
type IndexMap<K, V> = indexmap::IndexMap<K, V, Hasher>;
type IndexSet<V> = indexmap::IndexSet<V, Hasher>;

/// Produces both a causality-tracing layer, and a queryable causality graph.
///
/// This is a shorthand for:
/// ```rust
/// let causality_layer = tracing_causality::Layer::new();
/// let causality_graph = causality_layer.traces();
/// ```
pub fn new() -> (Layer, Traces) {
    let causality_layer = Layer::new();
    let causality_graph = causality_layer.traces();
    (causality_layer, causality_graph)
}

/// The consequences of some [`Id`].
///
/// The direct [`Consequences`] of an [`Id`] are produced by [`Trace::direct`].
/// The indirect [`Consequences`] of an [`Id`] are produced by
/// [`Trace::indirect`].
#[derive(Debug, Clone)]
pub struct Consequences<'trace> {
    consequences: &'trace IndexSet<Id>,
}

impl<'trace> Consequences<'trace> {
    pub const EMPTY: Consequences<'static> = Consequences {
        consequences: &IndexSet::with_hasher(Hasher),
    };

    /// The number of consequences.
    pub fn count(&self) -> usize {
        self.consequences.len()
    }

    /// Produces `true` if `id` is one of the consequences.
    pub fn has<'s>(&self, id: impl Into<Option<&'s Id>>) -> bool {
        id.into()
            .map(|id| self.consequences.contains(id))
            .unwrap_or(false)
    }

    /// Produces an iterator over the consequences.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Id> {
        self.consequences.iter()
    }
}

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
    root: Id,
    /// The causality trace, rooted at `Trace::root`.
    tree: IndexMap<Id, Causality<IndexSet<Id>, ()>>,
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
                    trace_vertex.indirect.insert(indirect_consequence.clone());
                }
            }
        }
        trace
    }

    /// Produces the direct [`Consequences`] of a given [`Id`].
    pub fn direct<'s>(&self, id: impl Into<Option<&'s Id>>) -> Consequences<'_> {
        id.into()
            .and_then(|id| self.tree.get(id))
            .map(|consequences| Consequences {
                consequences: &consequences.direct,
            })
            .unwrap_or(Consequences::EMPTY)
    }

    /// Produces the indirect [`Consequences`] of a given [`Id`].
    pub fn indirect<'s>(&self, id: impl Into<Option<&'s Id>>) -> Consequences<'_> {
        id.into()
            .and_then(|id| self.tree.get(id))
            .map(|consequences| Consequences {
                consequences: &consequences.indirect,
            })
            .unwrap_or(Consequences::EMPTY)
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
/// While this lock is held, the causality graph shared by [`Traces`] and
/// [`Layer`] is read-only. This ensures that the [`Trace`]s produced by
/// [`Lock::trace`] are consistent with respect to the instant that method is
/// invoked.
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
    pub fn trace<'s>(&self, id: &'s Id) -> Trace {
        Trace::of(&self.trees, id.clone())
    }

    /// Release this [`Lock`]. Dropping this [`Lock`] has the same effect.
    pub fn release(self) {
        let _ = self;
    }
}

impl Traces {
    /// Secure an exclusive lock on [`Traces`].
    ///
    /// While this lock is held, the causality graph shared by [`Traces`] and
    /// [`Layer`] is read-only. This ensures that the [`Trace`]s produced by
    /// [`Lock::trace`] are consistent with respect to the instant that method
    /// is invoked.
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
    /// invoke [`Traces::lock`], then call [`Lock::trace`].
    pub fn trace<'s>(&self, id: &'s Id) -> Trace {
        let graph = self.trees.read().unwrap_or_else(|e| unreachable!({ e }));
        Trace::of(&graph, id.clone())
    }
}

/// A [tracing-subscriber `Layer`][tracing-layer] that concurrently updates
/// [`Traces`].
///
/// Acquire the [`Layer`] corresponding to a [`Trace`] by calling
/// [`Layer::traces`].
///
/// [tracing-layer]: tracing_subscriber::layer::Layer
pub struct Layer {
    trees: Arc<LockableCausalTrees>,
}

impl Layer {
    /// Produces a [tracing-subscriber `Layer`][tracing-layer] concurrently
    /// updates [`Traces`] with the causal relationship between spans.
    ///
    /// [tracing-layer]: tracing_subscriber::layer::Layer
    pub fn new() -> Self {
        Self {
            trees: Arc::new(LockableCausalTrees::default()),
        }
    }

    /// A concurrently-updated causality graph of the traces analyzed by this
    /// [`Layer`].
    pub fn traces(&self) -> Traces {
        Traces {
            trees: self.trees.clone(),
        }
    }
}

impl<S> tracing_subscriber::layer::Layer<S> for Layer
where
    S: Subscriber + for<'span> LookupSpan<'span> + Send + Sync,
{
    fn on_new_span(&self, _: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let trees = self.trees.read().unwrap_or_else(|e| unreachable!({ e }));
        // add the span id as a vertex in the causality graph
        trees.insert(id.clone(), Default::default());
        // if the span has a parent, add an edge between the parent and the span
        if let Some(parent) = ctx.lookup_current().map(|parent| parent.id()) {
            if let Some(consequences) = trees.get(&parent) {
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
                "cause {:?} closed before consequent {:?}",
                cause, consequent
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

fn display(
    f: &mut fmt::Formatter,
    root: &Id,
    is_last: bool,
    tree: &IndexMap<Id, Causality<IndexSet<Id>, ()>>,
    prefix: &mut String,
) -> fmt::Result {
    let direct = &tree.get(root).unwrap().direct;
    let indirect = &tree.get(root).unwrap().indirect;
    let root = root.into_u64();

    let root_prefix = format!("{}{}─", prefix, if is_last { '└' } else { '├' });
    let mut root_prefix = root_prefix.chars();
    let _ = (root_prefix.next(), root_prefix.next());
    let root_prefix = root_prefix.as_str();

    if indirect.len() > 0 {
        write!(f, "{}{} ⤑ ", root_prefix, root)?;
        f.debug_set()
            .entries(indirect.iter().map(|id| id.into_u64()))
            .finish()?;
        writeln!(f)?;
    } else {
        writeln!(f, "{}{:?}", root_prefix, root)?;
    }

    prefix.push_str(if is_last { "│ " } else { "  " });

    for (i, consequence) in direct.iter().enumerate() {
        let is_last = i == direct.len() - 1;
        display(f, consequence, is_last, tree, prefix)?;
    }

    let _ = (prefix.pop(), prefix.pop());

    Ok(())
}

impl fmt::Display for Trace {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        display(f, &self.root, true, &self.tree, &mut String::new())
    }
}
