// TODO: sha256 and blake gadgets have many things in common - merge their interfaces
// into single abstract class
pub mod tables;
pub mod utils;
// non-optimized version has 3836 constraints
pub mod gadgets;
pub mod optimized_gadgets;
pub mod test;