#!/bin/sh

# cargo test --release -- --ignored --nocapture test_multiexp_performance_on_large_data
cargo test --release -- --ignored --nocapture test_large_data_different_multiexps
