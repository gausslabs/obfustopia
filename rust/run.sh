#!/bin/bash

for i in {1..20}; do
    echo "[Obfustopia] Iteration $i:"
    rm -rf ./log/output.log ./out
    mkdir out
    RUSTFLAGS="-Awarnings" cargo run --release --features="time" -- ./out/out.bin ./out/original_out.bin
    echo "[Obfustopia] Completed iteration $i."
done
