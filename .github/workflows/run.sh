#!/bin/sh
set -eux
cargo test -r -- --nocapture
