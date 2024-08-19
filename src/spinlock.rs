//! Spin lock implementation

use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::AtomicBool,
};

/// A spin lock-based implementation of a mutex.
///
/// This mutex does not handle poisoning. If your code can panic, that's on you.
pub struct SpinLock<T: ?Sized> {
    /// Whether the mutex is currently locked.
    locked: AtomicBool,
    /// The inner value being locked.
    inner: UnsafeCell<T>,
}
impl<T> SpinLock<T> {
    /// Construct a new mutex around the given value.
    pub const fn new(value: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            inner: UnsafeCell::new(value),
        }
    }

    /// Extract the value from `self`.
    ///
    /// This is safe because ownership means no [`Guard`]s have it locked.
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}
impl<T: ?Sized> SpinLock<T> {
    /// Lock the mutex.
    ///
    /// This returns a guard that provides access to the inner value and releases the lock on drop.
    pub fn lock(&self) -> Guard<'_, T> {
        loop {
            if self.locked.swap(true, std::sync::atomic::Ordering::Acquire) == false {
                break Guard {
                    lock_var: &self.locked,
                    // SAFETY: We just locked the lock.
                    inner: unsafe { &mut *self.inner.get() },
                };
            }
            std::hint::spin_loop();
        }
    }
}
unsafe impl<T: ?Sized + Send> Sync for SpinLock<T> {}

/// RAII guard on the [`SpinLock`].
///
/// If you [`std::mem::forget`] this guard, then the mutex will never unlock.
pub struct Guard<'a, T: ?Sized> {
    /// An atomic implementing the lock.
    lock_var: &'a AtomicBool,
    /// The inner value to be accessed.
    inner: &'a mut T,
}
impl<'a, T: ?Sized> Drop for Guard<'a, T> {
    fn drop(&mut self) {
        self.lock_var
            .store(false, std::sync::atomic::Ordering::Release);
    }
}
impl<'a, T: ?Sized> Deref for Guard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}
impl<'a, T: ?Sized> DerefMut for Guard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test case copied with modifications from the book
    #[test]
    fn simple_test() {
        /// Number of concurrent threads.
        const THREAD_COUNT: usize = 3;

        let x = SpinLock::new(Vec::new());
        std::thread::scope(|s| {
            for _ in 0..THREAD_COUNT {
                s.spawn(|| {
                    let mut g = x.lock();
                    g.push(1);
                    std::thread::sleep(std::time::Duration::from_millis(20));
                    g.push(2);
                });
            }
        });
        let vec = x.into_inner();
        assert!(vec.iter().filter(|&&e| e == 1).count() == THREAD_COUNT);
        assert!(vec.iter().filter(|&&e| e == 2).count() == THREAD_COUNT);
    }
}
