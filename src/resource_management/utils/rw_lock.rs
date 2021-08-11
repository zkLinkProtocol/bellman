use pin_project::*;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use futures_locks::{RwLock as RwLockAsync, RwLockReadGuard, RwLockWriteGuard, RwLockReadFut, RwLockWriteFut};

#[derive(Clone, Debug)]
pub struct RwLock<T: Send + 'static>{
    inner: RwLockAsync<T>
}

impl<T: Send + 'static> RwLock<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: RwLockAsync::new(value)
        }
    }

    pub fn read(&self) -> RwLockReadFuture<T> {
        RwLockReadFuture {
            inner: self.inner.clone()
        }
    }

    pub fn write(&self) -> RwLockWriteFuture<T> {
        RwLockWriteFuture {
            inner: self.inner.clone()
        }
    }
}

#[pin_project]
pub struct RwLockReadFuture<T: Send + 'static>{
    #[pin]
    inner: RwLockAsync<T>
}

impl<T: Send + 'static> Future for RwLockReadFuture<T> {
    type Output = RwLockReadGuard<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        let this = self.project();
        let inner = this.inner;
        println!("Polling RWLock for read");
        match inner.try_read() {
            Ok(guard) => {
                Poll::Ready(guard)
            },
            Err(..) => {
                Poll::Pending
            }
        }
        // match inner.poll(cx) {
        //     Poll::Ready(v) => {
        //         Poll::Ready(v)
        //     },
        //     Poll::Pending => {
        //         Poll::Pending
        //     }
        // }
    }
}

#[pin_project]
pub struct RwLockWriteFuture<T: Send + 'static>{
    #[pin]
    inner: RwLockAsync<T>
}

impl<T: Send + 'static> Future for RwLockWriteFuture<T> {
    type Output = RwLockWriteGuard<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        let this = self.project();
        let inner = this.inner;
        println!("Polling RWLock for write");
        match inner.try_write() {
            Ok(guard) => {
                Poll::Ready(guard)
            },
            Err(..) => {
                println!("Lock is busy");
                Poll::Pending
            }
        }

        // match inner.poll(cx) {
        //     Poll::Ready(v) => {
        //         Poll::Ready(v)
        //     },
        //     Poll::Pending => {
        //         Poll::Pending
        //     }
        // }
    }
}