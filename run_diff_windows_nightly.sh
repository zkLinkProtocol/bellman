#!/bin/sh

cargo +nightly test --release --features "asm" -- --ignored --nocapture test_large_data_different_windows
