//! An atomic reference-counted pointer.

use std::{
    cell::UnsafeCell,
    mem::ManuallyDrop,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{self, AtomicUsize, Ordering},
};

pub struct Arc<T: ?Sized> {
    ptr: NonNull<ArcInner<T>>,
}
impl<T> Arc<T> {
    /// Construct a new [`Arc`] pointing to the given value.
    pub fn new(value: T) -> Self {
        Self {
            ptr: NonNull::from(Box::leak(Box::new(ArcInner {
                data_refcount: AtomicUsize::new(1),
                alloc_refcount: AtomicUsize::new(1),
                value: UnsafeCell::new(ManuallyDrop::new(value)),
            }))),
        }
    }
}
impl<T: ?Sized> Arc<T> {
    /// Helper function to get the inner data.
    fn data(&self) -> &ArcInner<T> {
        // SAFETY: `self.ptr` is a valid, initialized pointer.
        unsafe { self.ptr.as_ref() }
    }

    /// Get mutable access to the value, if this `Arc` isn't shared.
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        // We check that there are no weak pointers, and if there aren't any, we lock the value.
        if this
            .data()
            .alloc_refcount
            .compare_exchange(1, usize::MAX, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            return None;
        }
        let is_unique = this.data().data_refcount.load(Ordering::Relaxed) == 1;
        // We can unlock downgrading now.
        this.data().alloc_refcount.store(1, Ordering::Release);
        if !is_unique {
            return None;
        }
        // We only need to establish an ording if making a mutable reference.
        atomic::fence(Ordering::Acquire);
        // SAFETY: The refcount is 1, so we're the only ones with access
        Some(unsafe { this.ptr.as_mut() }.value.get_mut())
    }

    /// Get the current refcount.
    pub fn data_refcount(this: &Self) -> usize {
        this.data().data_refcount.load(Ordering::Relaxed)
    }

    /// Get the current refcount.
    pub fn alloc_refcount(this: &Self) -> usize {
        this.data().alloc_refcount.load(Ordering::Relaxed)
    }

    /// Create a new [`Weak`] pointer to the same allocation.
    pub fn downgrade(this: &Self) -> Weak<T> {
        // Increment the alloc refcount
        loop {
            let old_count = this.data().alloc_refcount.load(Ordering::Relaxed);
            if old_count == usize::MAX {
                // TODO Potential hazard: Once we leak the weak pointer count, this loop will spin
                // forever.
                std::hint::spin_loop();
                continue;
            }
            let new_count = old_count.saturating_add(1);
            if this
                .data()
                .alloc_refcount
                .compare_exchange_weak(
                    old_count,
                    new_count,
                    // Synchronize with the release in `Self::get_mut`
                    Ordering::Acquire,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                break;
            }
        }
        Weak { ptr: this.ptr }
    }
}
impl<T: ?Sized> Clone for Arc<T> {
    fn clone(&self) -> Self {
        increment_atomic_saturating(&self.data().data_refcount);
        Self { ptr: self.ptr }
    }
}
impl<T: ?Sized> Deref for Arc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // We can borrow the value as a shared reference unless `self` is borrowed by
        // [`Self::get_mut`], which takes an exclusive reference to `self`.
        unsafe { &*self.data().value.get() }
    }
}
unsafe impl<T: Send + Sync + ?Sized> Send for Arc<T> {}
unsafe impl<T: Send + Sync + ?Sized> Sync for Arc<T> {}
impl<T: ?Sized> Drop for Arc<T> {
    fn drop(&mut self) {
        let data = self.data();
        if decrement_if_unsaturated(&data.data_refcount) == 0 {
            // We're the last Arc and we should drop the value.

            // The drop must be after ALL releases.
            std::sync::atomic::fence(Ordering::Acquire);

            // SAFETY: We're the last `Arc`, so nothing will access `data.value` anymore.
            let value = unsafe { &mut *data.value.get() };
            // SAFETY: We're the last `Arc`, so nothing will access `data.value` anymore.
            unsafe { ManuallyDrop::drop(value) };

            // No more `Arc`s exist, so we have to decrement the alloc refcount
            if decrement_if_unsaturated(&data.alloc_refcount) == 0 {
                drop(
                    // SAFETY:
                    // We initially allocated the data through `Box::new`, so we can convert it
                    // back to a `Box` to deallocate.
                    //
                    // We've just proved that we have the only remaining pointer to the
                    // allocation, so it can return to being a `Box`.
                    unsafe { Box::from_raw(self.ptr.as_ptr()) },
                );
            }
        }
    }
}

pub struct Weak<T: ?Sized> {
    ptr: NonNull<ArcInner<T>>,
}
impl<T: ?Sized> Weak<T> {
    pub fn upgrade(this: &Self) -> Option<Arc<T>> {
        let data = this.data();
        loop {
            let old_refcount = data.data_refcount.load(Ordering::Relaxed);
            if old_refcount == 0 {
                // All `Arc`s have been freed, so the data was dropped.
                return None;
            }
            let new_refcount = old_refcount.saturating_add(1);
            if data
                .data_refcount
                .compare_exchange_weak(
                    old_refcount,
                    new_refcount,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                )
                .is_ok()
            {
                return Some(Arc { ptr: this.ptr });
            }
        }
    }

    /// Helper function to get the inner data.
    fn data(&self) -> &ArcInner<T> {
        // SAFETY: `self.ptr` is a valid, initialized pointer.
        unsafe { self.ptr.as_ref() }
    }
}
impl<T: ?Sized> Clone for Weak<T> {
    fn clone(&self) -> Self {
        increment_atomic_saturating(&self.data().alloc_refcount);
        Self { ptr: self.ptr }
    }
}
unsafe impl<T: Send + Sync + ?Sized> Send for Weak<T> {}
unsafe impl<T: Send + Sync + ?Sized> Sync for Weak<T> {}
impl<T: ?Sized> Drop for Weak<T> {
    fn drop(&mut self) {
        let data = self.data();
        if decrement_if_unsaturated(&data.alloc_refcount) == 0 {
            drop(
                // SAFETY:
                // We initially allocated the data through `Box::new`, so we can convert it
                // back to a `Box` to deallocate.
                //
                // We've just proved that we have the only remaining pointer to the
                // allocation, so it can return to being a `Box`.
                unsafe { Box::from_raw(self.ptr.as_ptr()) },
            );
        }
    }
}

/// Saturating increment an atomic, returning the new value.
///
/// We use this on the constructors of [`Arc`] and [`Weak`] to increment their refcounts.
fn increment_atomic_saturating(counter: &AtomicUsize) -> usize {
    let mut old_count = counter.load(Ordering::Relaxed);
    loop {
        let new_count = old_count.saturating_add(1);
        match counter.compare_exchange_weak(
            old_count,
            new_count,
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            Ok(_) => {
                return new_count;
            }
            Err(updated_count) => {
                old_count = updated_count;
            }
        }
    }
}

/// Decrement an atomic if it hasn't saturated, returning the new value.
///
/// We use this on the destructors of [`Arc`] and [`Weak`] to decrement their refcounts.
fn decrement_if_unsaturated(counter: &AtomicUsize) -> usize {
    let mut old_count = counter.load(Ordering::Relaxed);
    loop {
        if old_count == usize::MAX {
            return old_count;
        }
        let new_count = old_count.saturating_sub(1);
        match counter.compare_exchange_weak(
            old_count,
            new_count,
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            Ok(_) => {
                return new_count;
            }
            Err(updated_count) => {
                old_count = updated_count;
            }
        }
    }
}

struct ArcInner<T: ?Sized> {
    /// Current count of strong pointers ([`Arc`]s only).
    ///
    /// Saturates at `usize::MAX`, at which point the object is leaked.
    data_refcount: AtomicUsize,
    /// Count of weak pointers, plus 1 if any strong pointers exist.
    ///
    /// Saturates at `usize::MAX`, at which point the allocation is leaked. However, if
    /// [`Self::data_refcount`] didn't saturate, the object may still be released.
    alloc_refcount: AtomicUsize,
    value: UnsafeCell<ManuallyDrop<T>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A struct that increments a counter whenever dropped.
    struct DetectDrop<'a>(&'a AtomicUsize);

    impl<'a> Drop for DetectDrop<'a> {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// Copied from the book
    #[test]
    fn test_refcounting() {
        static NUM_DROPS: AtomicUsize = AtomicUsize::new(0);

        // Create two Arcs sharing an object containing a string
        // and a DetectDrop, to detect when it's dropped.
        let x = Arc::new(("hello", DetectDrop(&NUM_DROPS)));
        let y = x.clone();

        // Send x to another thread, and use it there.
        let t = std::thread::spawn(move || {
            assert_eq!(x.0, "hello");
        });

        // In parallel, y should still be usable here.
        assert_eq!(y.0, "hello");

        // Wait for the thread to finish.
        t.join().unwrap();

        // One Arc, x, should be dropped by now.
        // We still have y, so the object shouldn't have been dropped yet.
        assert_eq!(NUM_DROPS.load(Ordering::Relaxed), 0);

        // Drop the remaining `Arc`.
        drop(y);

        // Now that `y` is dropped too,
        // the object should've been dropped.
        assert_eq!(NUM_DROPS.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_dropping_with_downcasts() {
        static NUM_DROPS: AtomicUsize = AtomicUsize::new(0);

        let strong = Arc::new(DetectDrop(&NUM_DROPS));

        // Dropping a weak pointer doesn't cause a drop
        {
            let weak = Arc::downgrade(&strong);
            drop(weak);
            assert_eq!(NUM_DROPS.load(Ordering::Relaxed), 0);
        }

        let weak = Arc::downgrade(&strong);

        // Having a weak pointer around doesn't stop it from dropping.
        drop(strong);
        assert_eq!(NUM_DROPS.load(Ordering::Relaxed), 1);

        drop(weak);
        assert_eq!(NUM_DROPS.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_mut_refs() {
        let mut val = Arc::new(5_u32);
        assert!(
            Arc::get_mut(&mut val).is_some(),
            "Should succeed on unshared Arc"
        );
        let val2 = val.clone();
        assert!(
            Arc::get_mut(&mut val).is_none(),
            "Should fail on shared Arc"
        );
        drop(val2);
        assert!(
            Arc::get_mut(&mut val).is_some(),
            "Should succeed on unshared Arc"
        );
        std::thread::spawn({
            let mut val = val.clone();
            move || {
                assert!(
                    Arc::get_mut(&mut val).is_none(),
                    "Should fail on shared Arc"
                );
            }
        })
        .join()
        .expect("Child thread panicked");
        assert!(
            Arc::get_mut(&mut val).is_some(),
            "Should succeed on unshared Arc"
        );
    }

    #[test]
    fn test_upgrading() {
        let strong = Arc::new(27_u32);
        let weak = Arc::downgrade(&strong);
        assert_eq!(
            strong.ptr.as_ptr() as usize,
            Weak::upgrade(&weak)
                .expect("should upgrade weak pointers while a strong pointer exists")
                .ptr
                .as_ptr() as usize,
            "Upgraded pointer should point to the same location as original",
        );
        drop(strong);
        assert!(Weak::upgrade(&weak).is_none(), "Upgrading weak pointers should no longer be possible after all strong pointers are dropped");
    }
}
