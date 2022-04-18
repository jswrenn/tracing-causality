use crate::Update;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

/// Constructs a channel of [`Trace`] updates bounded at `capacity`.
pub(crate) fn bounded(capacity: usize) -> (Sender, Updates) {
    let (sender, receiver) = flume::bounded(capacity);
    let overflow_flag = OverflowFlag::default();
    let sender = Sender {
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
    pub fn into_iter(self) -> impl Iterator<Item = Update> {
        self.receiver
            .into_iter()
            .take_while(move |_| !self.overflow_flag.check())
    }

    pub fn into_stream(self) -> impl futures_core::stream::Stream {
        use futures::stream::StreamExt;
        self.receiver.into_stream()
          .take_while(move |_| std::future::ready(!self.overflow_flag.check()))
    }
}

#[derive(Clone)]
pub(crate) struct Sender {
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

    pub(crate) fn broadcast(listeners: &mut Vec<Self>, update: Update) {
        listeners.retain(|listener| listener.try_send(update.clone()).is_ok());
    }
}

#[cfg(test)]
mod test_sender {
    use super::*;
    use tracing_core::span::Id;

    #[test]
    fn try_send_success() {
        let (sender, updates) = bounded(1);
        let update = Update::Direct {
            cause: Id::from_u64(1),
            consequence: Id::from_u64(2),
        };
        let send_result = sender.try_send(update);
        assert!(send_result.is_ok());
    }

    #[test]
    fn try_send_err_disconnected() {
        // drop `Updates` immediately
        let (sender, _) = bounded(1);
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
        let (sender, updates) = bounded(0);
        let update = Update::Direct {
            cause: Id::from_u64(1),
            consequence: Id::from_u64(2),
        };
        assert_eq!(updates.overflow_flag.check(), false);
        let send_result = sender.try_send(update);
        assert!(send_result.is_err());
        assert_eq!(updates.overflow_flag.check(), true);
    }
}
