//! A mutual-exclusion lock implementation.
//!
//! See [`Mutex`].

use crate::futex::Futex;
use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering},
};

/// The `state` value for an unlocked [`Mutex`].
const MUTEX_UNLOCKED: u32 = 0;
/// The `state` value for a locked [`Mutex`] which is known to not be contended.
const MUTEX_LOCKED_UNCONTENDED: u32 = 1;
/// The `state` value for a locked [`Mutex`] which might be contended.
const MUTEX_LOCKED_CONTENDED: u32 = 2;

/// A mutex guarding some data.
pub struct Mutex<T> {
    /// The lock's state.
    ///
    /// See [`MUTEX_UNLOCKED`], [`MUTEX_LOCKED_CONTENDED`], and [`MUTEX_LOCKED_UNCONTENDED`] for
    /// the possible values the futex can have.
    state: Futex,
    /// The value guarded by the mutex.
    value: UnsafeCell<T>,
}

impl<T> Mutex<T> {
    /// Construct a [`Mutex`] to wrap the given value.
    pub const fn new(value: T) -> Self {
        Self {
            state: Futex::new(MUTEX_UNLOCKED),
            value: UnsafeCell::new(value),
        }
    }

    /// Destruct the mutex and return the inner value.
    ///
    /// This function does not have to lock because consuming the value means it cannot be in use
    /// anywhere else.
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }

    /// Lock the mutex, returning an RAII guard.
    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.try_lock().unwrap_or_else(||
            // Use `lock_contended` as a fallback if we can't immediately acquire.
        self.lock_contended())
    }

    /// Attempt to lock the mutex without blocking.
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T>> {
        self.state
            .atomic
            .compare_exchange_weak(
                MUTEX_UNLOCKED,
                MUTEX_LOCKED_UNCONTENDED,
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .ok()
            .map(|_| MutexGuard { mutex: self })
    }

    /// A slow fallback path that blocks until we can acquire the mutex.
    ///
    /// This begins with a short spinloop segment to save syscalls if the mutex is unlocked
    /// quickly, followed by a blocking loop using [`Futex`].
    #[cold]
    fn lock_contended(&self) -> MutexGuard<'_, T> {
        /// The number of times to try spinning in a loop.
        const MAX_SPIN_COUNT: usize = 128;
        let mut spin_count = 0;
        while self.state.atomic.load(
            // Atomic CAS takes exclusive control over the memory for this core, even if it fails,
            // so we just check the value to save cores from thrashing their caches with each
            // other.
            Ordering::Relaxed,
        ) ==
        // If another thread says the mutex is contended, then spinning probably won't help.
        MUTEX_LOCKED_UNCONTENDED
            && spin_count < MAX_SPIN_COUNT
        {
            spin_count += 1;
            core::hint::spin_loop();
        }
        if let Some(guard) = self.try_lock() {
            return guard;
        }
        // After giving up on spinning, we enter a blocking loop that marks the lock as contended.
        while self
            .state
            .atomic
            .swap(MUTEX_LOCKED_CONTENDED, Ordering::Acquire)
            != MUTEX_UNLOCKED
        {
            // We now wait against the expected value of 2.
            self.state.wait(MUTEX_LOCKED_CONTENDED);
        }
        // If it returned 0, we got the lock now, so we can return.
        //
        // This can erroneously indicate threads are waiting if we were the only thread in the
        // above loop, but the cost of that mistake is an extra syscall, so we're fine.
        MutexGuard { mutex: self }
    }
}
impl<T: Default> Default for Mutex<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

unsafe impl<T: Send> Sync for Mutex<T> {}

/// A guard holding a locked mutex.
pub struct MutexGuard<'a, T> {
    /// The mutex that has been locked.
    mutex: &'a Mutex<T>,
}
unsafe impl<T: Sync> Sync for MutexGuard<'_, T> {}
impl<T> Deref for MutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: We've locked the mutex, so no one else has access.
        unsafe { &*self.mutex.value.get() }
    }
}
impl<T> DerefMut for MutexGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: We've locked the mutex, so no one else has access.
        unsafe { &mut *self.mutex.value.get() }
    }
}
impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        if self
            .mutex
            .state
            .atomic
            .swap(MUTEX_UNLOCKED, Ordering::Release)
            == MUTEX_LOCKED_CONTENDED
        {
            // Wake a thread waiting on the mutex, if the mutex might be contended.
            self.mutex.state.wake_one();
        }
    }
}

/// A "condition variable" on which threads can wait for signals from other threads.
pub struct Condvar {
    /// A counter of the number of times this condition has been notified.
    counter: Futex,
    /// The number of threads waiting on this condition.
    num_waiters: AtomicUsize,
}
impl Condvar {
    /// Create a new [`Condvar`].
    pub const fn new() -> Self {
        Self {
            counter: Futex::new(0),
            num_waiters: AtomicUsize::new(0),
        }
    }

    /// Wait for a call to [`Self::notify_one`] or [`Self::notify_all`].
    ///
    /// `mutex_guard` is a lock on a mutex. The mutex will be unlocked while waiting, and then
    /// reacquired before returning. Calls to a notify function should be done while holding the
    /// same mutex to avoid race conditions causing the notification to be missed and this method
    /// to wait forever.
    ///
    /// Note that this may spuriously wake up, so you should check that whatever condition you were
    /// waiting for has actually happened.
    pub fn wait<'a, T>(&self, mutex_guard: MutexGuard<'a, T>) -> MutexGuard<'a, T> {
        // Track the original value of the counter.
        //
        // We could theoretically miss exactly 2^32 notify calls, since this value wraps, but we keep
        // sections dependent on critical values short enough that this is exceedingly unlikely in any
        // reasonable situation (and if that does happen, there will likely be another one soon
        // enough, anyways).
        //
        // We also might spuriously turn a `notify_one` into a "notify_two" if another thread calls
        // `notify_one` to wake another thread between us reading the value and waiting on it (we
        // have to drop the mutex before waiting on the condition, so there must be a gap for that
        // to slot in).
        let counter_value = self.counter.atomic.load(Ordering::Relaxed);
        self.num_waiters.fetch_add(1, Ordering::Relaxed);

        // Unlock the mutex.
        let mutex = mutex_guard.mutex;
        drop(mutex_guard);

        // Wait for the counter's value to change.
        self.counter.wait(counter_value);

        self.num_waiters.fetch_sub(1, Ordering::Relaxed);
        mutex.lock()
    }

    /// Notify one thread waiting on this condition variable.
    pub fn notify_one(&self) {
        if self.num_waiters.load(Ordering::Relaxed) > 0 {
            self.counter.atomic.fetch_add(1, Ordering::Relaxed);
            self.counter.wake_one();
        }
    }

    /// Notify all threads waiting on this condition variable.
    pub fn notify_all(&self) {
        if self.num_waiters.load(Ordering::Relaxed) > 0 {
            self.counter.atomic.fetch_add(1, Ordering::Relaxed);
            self.counter.wake_all();
        }
    }
}
impl Default for Condvar {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    /// Test with very heavy lock contention on a very short critical section.
    ///
    /// Copied with modifications from a benchmark in the book.
    #[test]
    fn test_contended_short_critical_section() {
        const NUM_THREADS: usize = 16;
        const NUM_ITERS_PER_THREAD: usize = 100;

        let m = Mutex::new(0);
        std::thread::scope(|s| {
            for _ in 0..NUM_THREADS {
                s.spawn(|| {
                    for _ in 0..NUM_ITERS_PER_THREAD {
                        *m.lock() += 1;
                    }
                });
            }
        });
        assert_eq!(m.into_inner(), NUM_THREADS * NUM_ITERS_PER_THREAD);
    }

    /// Test with heavy lock contention on a long critical section.
    #[test]
    fn test_contended_long_critical_section() {
        const NUM_THREADS: usize = 8;
        const NUM_ITERS_PER_THREAD: usize = 10;
        const CRITICAL_SECTION_DURATION: Duration = Duration::from_millis(20);

        let m = Mutex::new(0);
        std::thread::scope(|s| {
            for _ in 0..NUM_THREADS {
                s.spawn(|| {
                    for _ in 0..NUM_ITERS_PER_THREAD {
                        let mut lock = m.lock();
                        std::thread::sleep(CRITICAL_SECTION_DURATION);
                        *lock += 1;
                    }
                });
            }
        });
        assert_eq!(m.into_inner(), NUM_THREADS * NUM_ITERS_PER_THREAD);
    }

    /// Test sending signals via [`Condvar`].
    ///
    /// Copied with modifications from the book.
    #[test]
    fn test_condvar() {
        let mutex = Mutex::<u32>::default();
        let condvar = Condvar::default();

        let mut wakeups = 0;

        std::thread::scope(|s| {
            s.spawn(|| {
                std::thread::sleep(Duration::from_secs(1));
                *mutex.lock() = 5;
                condvar.notify_one();
            });

            let mut m = mutex.lock();
            while *m == 0 {
                m = condvar.wait(m);
                wakeups += 1;
            }

            assert_eq!(*m, 5);
        });
        // Check that the main thread actually did wait (not busy-loop),
        // while still allowing for a few spurious wake ups.
        assert!(wakeups < 8);
    }
}
