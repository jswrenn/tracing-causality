use tracing_subscriber::{prelude::*, registry::Registry};

fn main() {
    let (layer, traces) = tracing_causality::new();
    let _ = Registry::default().with(layer).init();

    let a = tracing::trace_span!("a");
    let a_id = a.id().unwrap();

    // a frozen trace, rooted at `a`
    let trace = traces.trace(&a_id);
    // `a` does not have any direct consequences
    assert_eq!(trace.direct(&a_id).count(), 0);
    // ...nor indirect consequences
    assert_eq!(trace.indirect(&a_id).count(), 0);

    // create span `b`, a child of `a`
    let b = a.in_scope(|| tracing::trace_span!("b"));
    let b_id = b.id().unwrap();

    // since traces are static snapshots of the
    // causality graph, `b` is not in `trace`
    assert_eq!(trace.direct(&a_id).count(), 0);

    // re-trace `a`
    let trace = traces.trace(&a_id);
    // `a` has 1 direct consequence: `b`
    assert_eq!(trace.direct(&a_id).count(), 1);
    assert_eq!(trace.direct(&a_id).iter().next(), Some(&b_id));
    // `b` does not have any direct consequences
    assert_eq!(trace.direct(&b_id).count(), 0);
    // ...nor indirect consequences
    assert_eq!(trace.indirect(&b_id).count(), 0);

    // create span `c`, which follows-from `b`
    let c = tracing::trace_span!("c");
    c.follows_from(&b_id);

    // `b` now has one indirect consequence: `c`
    assert_eq!(traces.trace(&a_id).indirect(&b_id).count(), 1);
    assert_eq!(traces.trace(&b_id).indirect(&b_id).count(), 1);
}
