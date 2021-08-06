use std::sync::atomic::AtomicUsize;

use lazy_static::__Deref;

#[derive(Debug)]
pub struct Priority<const N: usize>{
    depth: AtomicUsize,
    modifiers: [u8; N]
}

impl<const N: usize> Priority<N> {
    pub fn new() -> Self {
        Self {
            depth: AtomicUsize::from(0),
            modifiers: [0u8; N]
        }
    }

    pub fn child(&self) -> Self {
        let depth = self.depth.load(std::sync::atomic::Ordering::Acquire);
        assert!(depth + 1 < N);
        Self {
            depth: AtomicUsize::from(depth + 1),
            modifiers: self.modifiers
        }
    }

    pub fn next(self) -> Self {
        let depth = self.depth.load(std::sync::atomic::Ordering::Acquire);
        assert!(depth < N);
        let mut mods = self.modifiers;
        mods[depth] += 1;
        Self {
            depth: self.depth,
            modifiers: mods
        }
    }
}

impl<const N: usize> PartialOrd for Priority<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for Priority<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let self_depth = self.depth.load(std::sync::atomic::Ordering::Acquire);
        let other_depth = other.depth.load(std::sync::atomic::Ordering::Acquire);
        let depth = std::cmp::max(self_depth, other_depth);
        for (a, b) in self.modifiers.iter().zip(other.modifiers.iter()).take(self_depth) {
            let ord = a.cmp(b);
            if ord != std::cmp::Ordering::Equal {
                return ord;
            }
        }

        std::cmp::Ordering::Equal
    }
}

impl<const N: usize> PartialEq for Priority<N> {
    fn eq(&self, other: &Self) -> bool {
        let self_depth = self.depth.load(std::sync::atomic::Ordering::Acquire);
        let other_depth = other.depth.load(std::sync::atomic::Ordering::Acquire);
        if self_depth != other_depth {
            return false;
        }
        for (a, b) in self.modifiers.iter().zip(other.modifiers.iter()).take(self_depth) {
            if a != b {
                return false;
            }
        }

        true
    }
}

impl<const N: usize> Eq for Priority<N> {}

impl<const N: usize> Clone for Priority<N> {
    fn clone(&self) -> Self {
        let depth = self.depth.load(std::sync::atomic::Ordering::Acquire);
        Self {
            depth: AtomicUsize::from(depth),
            modifiers: self.modifiers
        }
    }
}

