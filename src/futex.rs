//! A futex implementation.
//!
//! See [`Futex`].

use std::sync::atomic::AtomicU32;

/// A futex implementation for Linux.
///
/// Refer to the futex (2) man page for more details.
pub struct Futex {
    /// The value being stored in the futex.
    ///
    /// You can modify this value with any atomic operations, but ensure to call [`Self::wake_one`]
    /// or [`Self::wake_all`] if any other threads might be waiting on the value.
    pub atomic: AtomicU32,
}
impl Futex {
    /// Construct a new [`Futex`] with a given value.
    pub const fn new(value: u32) -> Self {
        Self {
            atomic: AtomicU32::new(value),
        }
    }

    /// Call `FUTEX_WAIT` on `self` with the given expected value.
    ///
    /// This function will, if `self` stores the value `expected`, block until someone else calls
    /// [`Self::wake_one`] or the like to wake the mutex. You should assume that spurious wakes are
    /// possible and check your condition in a loop.
    ///
    /// This method synchronizes to return after all previous wakes on self. Specifically, if this
    /// wake was not spurious and was caused by a call to [`Self::wake_one`] or [`Self::wake_all`],
    /// then it synchronizes to return after that call.
    ///
    /// Refer to the futex (2) man page for more details.
    pub fn wait(&self, expected: u32) {
        // SAFETY: Futex waits on an atomic are safe.
        unsafe {
            libc::syscall(
                libc::SYS_futex,
                &self.atomic,
                libc::FUTEX_WAIT,
                expected,
                std::ptr::null::<libc::timespec>(),
            );
        }
        std::sync::atomic::fence(std::sync::atomic::Ordering::Acquire);
    }

    /// Call `FUTEX_WAKE` on `self` to wake one waiting thread.
    ///
    /// This method synchronizes with any threads that were waiting on this futex, to happen before
    /// the thread wakes up.
    ///
    /// Refer to the futex (2) man page for more details.
    pub fn wake_one(&self) {
        std::sync::atomic::fence(std::sync::atomic::Ordering::Release);
        // SAFETY: Waiters must handle spurious wakes, so this is safe to call.
        unsafe {
            libc::syscall(libc::SYS_futex, &self.atomic, libc::FUTEX_WAKE, 1);
        }
    }

    /// Call `FUTEX_WAKE` on `self` to wake all waiting thread.
    ///
    /// This function returns the number of threads which were waiting on `self`.
    ///
    /// This method synchronizes with any threads that were waiting on this futex, to happen before
    /// the thread wakes up.
    ///
    /// Refer to the futex (2) man page for more details.
    pub fn wake_all(&self) -> u32 {
        std::sync::atomic::fence(std::sync::atomic::Ordering::Release);
        // SAFETY: Waiters must handle spurious wakes, so this is safe to call.
        unsafe {
            libc::syscall(
                libc::SYS_futex,
                &self.atomic,
                libc::FUTEX_WAKE,
                // We assume there aren't >2B threads waiting on `self`
                i32::MAX,
            ) as u32
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::atomic::{AtomicUsize, Ordering},
        time::{Duration, Instant},
    };

    use super::*;

    #[test]
    fn test_no_wait_on_value_mismatch() {
        let futex = Futex::new(0);

        let start = Instant::now();
        futex.wait(1);
        assert!(start.elapsed() < Duration::from_millis(20));
    }

    #[test]
    fn test_waiting() {
        let futex = Futex::new(0);

        std::thread::scope(|s| {
            s.spawn(|| {
                std::thread::sleep(Duration::from_millis(100));
                futex.atomic.store(1, Ordering::Relaxed);
                futex.wake_one();
            });

            let mut wake_count = 0;
            let start = Instant::now();
            while futex.atomic.load(Ordering::Relaxed) == 0 {
                futex.wait(0);
                wake_count += 1;
            }
            let elapsed = start.elapsed();
            assert!(elapsed >= Duration::from_millis(80));
            assert!(elapsed <= Duration::from_millis(120));
            assert!(wake_count > 0);
            assert!(wake_count < 16);
        });
    }

    #[test]
    fn test_wake_counts() {
        /// The number of threads to wait on the futex.
        const NUM_WAITER_THREADS: usize = 16;

        // We need a barrier to ensure all threads have a chance to wake up before we continue.
        let barrier = std::sync::Barrier::new(NUM_WAITER_THREADS + 1);

        let futex = Futex::new(0);
        let exited_threads = AtomicUsize::new(0);
        std::thread::scope(|s| {
            for _ in 0..NUM_WAITER_THREADS {
                s.spawn(|| {
                    while futex.atomic.load(Ordering::Relaxed) == 0 {
                        futex.wait(0);
                    }
                    exited_threads.fetch_add(1, Ordering::Relaxed);
                    barrier.wait();
                });
            }
            std::thread::sleep(Duration::from_millis(10));
            futex.atomic.store(1, Ordering::Relaxed);
            futex.wake_one();
            std::thread::sleep(Duration::from_millis(10));
            assert_eq!(exited_threads.load(Ordering::Relaxed), 1);
            futex.wake_all();
            barrier.wait();
            assert_eq!(exited_threads.load(Ordering::Relaxed), NUM_WAITER_THREADS);
        });
    }
}
