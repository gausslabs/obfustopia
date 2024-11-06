#!/bin/bash

# Step 1: Create the "test_outputs" directory if it doesn't exist
mkdir -p test_outputs

# Step 2: Generate the current date and time in "YYYY-MM-DD_HH-MM-SS" format
curr_date_time=$(date +"%Y-%m-%d_%H-%M-%S")

# Step 3: Create the folder with the current date and time within "test_outputs"
base_dir="test_outputs/$curr_date_time"
mkdir -p "$base_dir"

strat1_dir="$base_dir/strat1"
strat2_dir="$base_dir/strat2"
mkdir -p "$strat1_dir" "$strat2_dir"

# Strategy 1
for i in {1..5}; do
    echo "[Obfustopia: Strategy 1] Iteration $i:"
    mkdir -p "$strat1_dir/$i"
    RUSTFLAGS="-Awarnings" cargo run --release --features="time" -- 1 "$strat1_dir/$i/logs.log" "$strat1_dir/$i/out.bin" "$strat1_dir/$i/original_out.bin" 1
    echo "[Obfustopia: Strategy 1] Completed iteration $i."
done

# Strategy 2
for i in {1..5}; do
    echo "[Obfustopia: Strategy 2] Iteration $i:"
    mkdir -p "$strat2_dir/$i"
    RUSTFLAGS="-Awarnings" cargo run --release --features="time" -- 1 "$strat2_dir/$i/logs.log" "$strat2_dir/$i/out.bin" "$strat2_dir/$i/original_out.bin" 2
    echo "[Obfustopia: Strategy 2] Completed iteration $i."
done