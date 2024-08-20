//! A one-shot channel for sending data.

use std::{
    cell::UnsafeCell,
    marker::PhantomData,
    mem::MaybeUninit,
    sync::atomic::{self, AtomicBool, Ordering},
    thread::Thread,
};

pub struct Channel<T> {
    ready: AtomicBool,
    value: UnsafeCell<MaybeUninit<T>>,
}
impl<T> Channel<T> {
    pub fn new() -> Self {
        Self {
            ready: AtomicBool::new(false),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    pub fn split(&mut self) -> (Sender<'_, T>, Receiver<'_, T>) {
        // Drop any value currently sitting in the channel and reset `ready`.
        *self = Self::new();
        (
            Sender {
                channel: self,
                unpark_thread: std::thread::current(),
            },
            Receiver {
                channel: self,
                _phantom: PhantomData,
            },
        )
    }
}
unsafe impl<T> Sync for Channel<T> where T: Send {}
impl<T> Drop for Channel<T> {
    fn drop(&mut self) {
        if self.ready.load(Ordering::Acquire) {
            // SAFETY: `ready` has been written, so the value is valid.
            unsafe { self.value.get_mut().assume_init_drop() }
        }
    }
}
impl<T> Default for Channel<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Sender<'a, T> {
    channel: &'a Channel<T>,
    unpark_thread: Thread,
}
impl<'a, T> Sender<'a, T> {
    pub fn send(self, value: T) {
        // SAFETY:
        // We haven't written `ready` yet, so nothing is reading `value`.
        // `self` isn't shared, so nothing else is writing `value`.
        let slot = unsafe { &mut *self.channel.value.get() };
        slot.write(value);
        self.channel.ready.store(true, Ordering::Release);
        self.unpark_thread.unpark();
    }
}

pub struct Receiver<'a, T> {
    channel: &'a Channel<T>,
    /// Phantom to make receiver `!Send`
    _phantom: PhantomData<*const ()>,
}
impl<'a, T> Receiver<'a, T> {
    pub fn is_ready(&self) -> bool {
        self.channel.ready.load(Ordering::Relaxed)
    }

    pub fn receive(self) -> T {
        while !self.is_ready() {
            std::thread::park();
        }
        // Use a `fence` to ensure ordering
        atomic::fence(Ordering::Acquire);
        // Indicate that we've moved the value out, and won't drop it.
        self.channel.ready.store(false, Ordering::Relaxed);
        // SAFETY: `ready` has been written, so the value won't be written again.
        let slot = unsafe { &*self.channel.value.get() };
        // SAFETY:
        // `ready` has been written, so the value is initialized.
        // This method consumes `self`, so we can pull it out.
        unsafe { slot.assume_init_read() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test copied with modifications from the book
    #[test]
    fn test() {
        let mut channel = Channel::new();
        std::thread::scope(|s| {
            let (sender, receiver) = channel.split();
            s.spawn(move || {
                std::thread::sleep(std::time::Duration::from_millis(10));
                sender.send("hello world!");
            });
            assert!(!receiver.is_ready());
            assert_eq!(receiver.receive(), "hello world!");
        });
    }
}
