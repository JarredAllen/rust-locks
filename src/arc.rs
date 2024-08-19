//! An atomic reference-counted pointer.

use std::{
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
                refcount: AtomicUsize::new(1),
                value,
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
        if Self::refcount(this) == 1 {
            // We only need to establish an ording if making a mutable reference.
            atomic::fence(Ordering::Acquire);
            // SAFETY: The refcoutn is 1, so we're the only ones with access
            Some(unsafe { &mut this.ptr.as_mut().value })
        } else {
            None
        }
    }

    /// Get the current refcount.
    pub fn refcount(this: &Self) -> usize {
        this.data().refcount.load(Ordering::Relaxed)
    }
}
impl<T: ?Sized> Clone for Arc<T> {
    fn clone(&self) -> Self {
        {
            // Increment the refcount
            let data = self.data();
            loop {
                let refcount = data.refcount.load(std::sync::atomic::Ordering::Relaxed);
                if data
                    .refcount
                    .compare_exchange_weak(
                        refcount,
                        refcount.saturating_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break;
                }
            }
        }
        Self { ptr: self.ptr }
    }
}
impl<T: ?Sized> Deref for Arc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data().value
    }
}
impl<T: ?Sized> Drop for Arc<T> {
    fn drop(&mut self) {
        let data = self.data();
        loop {
            let refcount = data.refcount.load(std::sync::atomic::Ordering::Relaxed);
            println!("Maybe dropping with refcount {refcount}");
            if refcount == usize::MAX {
                // Saturate at max and stop counting
                return;
            }
            match data.refcount.compare_exchange_weak(
                refcount,
                refcount - 1,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(1) => {
                    // Returns old value, so 1 means we're the last reference and we should drop.

                    // The drop must be after ALL releases.
                    std::sync::atomic::fence(Ordering::Acquire);
                    drop(
                        // SAFETY: We constructed from a box, so we can convert back
                        unsafe { Box::from_raw(self.ptr.as_ptr()) },
                    );
                    return;
                }
                Ok(_) => {
                    return;
                }
                Err(_) => {}
            }
        }
    }
}
unsafe impl<T: Send + Sync> Send for Arc<T> {}
unsafe impl<T: Send + Sync> Sync for Arc<T> {}

struct ArcInner<T: ?Sized> {
    /// Current count of pointers.
    ///
    /// Saturates at `usize::MAX`, at which point the object is leaked.
    refcount: AtomicUsize,
    value: T,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Copied from the book
    #[test]
    fn test_refcounting() {
        static NUM_DROPS: AtomicUsize = AtomicUsize::new(0);

        struct DetectDrop;

        impl Drop for DetectDrop {
            fn drop(&mut self) {
                NUM_DROPS.fetch_add(1, Ordering::Relaxed);
            }
        }

        // Create two Arcs sharing an object containing a string
        // and a DetectDrop, to detect when it's dropped.
        let x = Arc::new(("hello", DetectDrop));
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
}
