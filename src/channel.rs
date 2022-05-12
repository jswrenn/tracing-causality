use crate::Update;
use std::{
    collections::BTreeSet,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};
use tracing_core::span::Id;

/// Constructs a channel of [`Trace`] updates bounded at `capacity`.
pub(crate) fn bounded(id: Id, capacity: usize) -> (Sender, Updates) {
    let (sender, receiver) = flume::bounded(capacity);
    let overflow_flag = OverflowFlag::default();
    let sender = Sender {
        id,
        sender,
        overflow_flag: overflow_flag.clone(),
    };
    let updates = Updates {
        receiver,
        overflow_flag,
    };
    (sender, updates)
}

#[derive(Default, Clone)]
struct OverflowFlag {
    flag: Arc<AtomicBool>,
}

impl OverflowFlag {
    fn set(&self) {
        self.flag.store(true, Ordering::Release);
    }

    fn check(&self) -> bool {
        self.flag.load(Ordering::Acquire)
    }
}

#[cfg(test)]
mod test_overflow_flag {
    use super::OverflowFlag;

    #[test]
    fn set_and_check() {
        let flag = OverflowFlag::default();
        // the starting value of the flag is `false`
        assert_eq!(flag.check(), false);
        // calling `set` makes the flag value `true`
        flag.set();
        assert_eq!(flag.check(), true);
        // calling `set` again does NOT toggle the flag to `false`
        flag.set();
        assert_eq!(flag.check(), true);
    }
}

/// A stream of [`Update`]s that affect a [`Trace`][crate::Trace].
pub struct Updates {
    receiver: flume::Receiver<Update>,
    overflow_flag: OverflowFlag,
}

impl Updates {
    pub fn is_empty(&self) -> bool {
        self.receiver.is_empty()
    }

    pub(crate) fn next(&self) -> Option<Update> {
        self.receiver.try_recv().ok()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Update> {
        self.receiver
            .into_iter()
            .take_while(move |_| !self.overflow_flag.check())
    }

    pub fn into_stream(self) -> impl futures_core::stream::Stream {
        use futures::stream::StreamExt;
        self.receiver
            .into_stream()
            .take_while(move |_| std::future::ready(!self.overflow_flag.check()))
    }
}

#[derive(Clone)]
pub(crate) struct Sender {
    id: Id,
    sender: flume::Sender<Update>,
    overflow_flag: OverflowFlag,
}

impl Sender {
    fn try_send(&self, update: Update) -> Result<(), ()> {
        use flume::TrySendError::{Disconnected, Full};

        self.sender
            .try_send(update)
            .map_err(|err| match err {
                Full(_) => {
                    // notify receivers that an update has been dropped
                    self.overflow_flag.set();
                }
                Disconnected(_) => {
                    // don't take any action here if disconnected
                }
            })
            .map(|_| {})
    }

    pub(crate) fn broadcast(listeners: &mut BTreeSet<Self>, update: Update) {
        listeners.retain(|listener| listener.try_send(update.clone()).is_ok());
    }
}

impl std::hash::Hash for Sender {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Eq for Sender {}

impl Ord for Sender {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.into_u64().cmp(&other.id.into_u64())
    }
}

impl PartialOrd for Sender {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.id.into_u64().partial_cmp(&other.id.into_u64())
    }
}

impl PartialEq for Sender {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

#[cfg(test)]
mod test_sender {
    use super::*;
    use tracing_core::span::Id;

    #[test]
    fn try_send_success() {
        let (sender, updates) = bounded(Id::from_u64(1), 1);
        let update = Update::Direct {
            cause: Id::from_u64(1),
            consequence: Id::from_u64(2),
        };
        let send_result = sender.try_send(update.clone());
        assert!(send_result.is_ok());
        assert_eq!(updates.next(), Some(update.clone()));
        assert!(updates.is_empty());
    }

    #[test]
    fn try_send_err_disconnected() {
        // drop `Updates` immediately
        let (sender, _) = bounded(Id::from_u64(1), 1);
        let update = Update::Direct {
            cause: Id::from_u64(1),
            consequence: Id::from_u64(2),
        };
        let send_result = sender.try_send(update);
        assert!(send_result.is_err());
    }

    #[test]
    fn try_send_err_full() {
        // set capacity to 0 to overflow on first send
        let (sender, updates) = bounded(Id::from_u64(1), 0);
        let update = Update::Direct {
            cause: Id::from_u64(1),
            consequence: Id::from_u64(2),
        };
        assert_eq!(updates.overflow_flag.check(), false);
        let send_result = sender.try_send(update);
        assert!(send_result.is_err());
        assert_eq!(updates.overflow_flag.check(), true);
        assert_eq!(updates.next(), None,);
    }
}
