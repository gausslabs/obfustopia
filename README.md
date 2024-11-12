### Run obfuscation

To obfsucate a random reversible circuit that is an SPRP run the following command

```
cargo run --release -- 1 [log_path] [job_path] [orignal_circuit_path] [1 OR 2]
```

where

-   log_path: is location to store the log file.
-   job_path: is location to store the obfuscation job. Obfuscation job stores the obfuscation progress and the obfuscated circuit.
-   original_circuit_path: is location to store the sampled reversible SPRP circuit. It is the circuit being obfuscated.
-   1 OR 2: 1 OR 2 are different obfuscation strategies. We recommend 1 by default.

### Verify obfuscation job

To verify that the obfuscated circuit of an obfuscation job is functionally equivalent to the original circuit, run the following command

```
cargo run --release -- 2 [job_path] [iterations]
```

where

-   job_path: is location where obfuscated job is stored
-   iterations: is no. of iterations. Each iteration samples a random input and checks that output of original circuit is equivalent to output of obfuscated circuit.
g
Note: Two circuits with `n` bit inputs for big enough `n` can only be tested probabilitiscally equal. This is because brute forcing through all 2^{n} inputs takes time. However there's no reason why it cannot be done.

### Circuit binary to JSON conversion

It's more convenient to look a pretty JSON format than a binary file. A JSON file can also be sent over the network without scaring the receiver. Which is why we provide a way to convert circuit binary to JSON file.

```
cargo run --release -- 3 [circuit_bin_path] [circuit_json_path]
```

where

-   circuit_bin_path: is location of circuit's binary.
-   circuit_json_path: location to store circuit's JSON file.

### Obfuscated circuit binary to JSON conversion

Once obfucation job is finished, you can isolate the obfuscated circuit into a JSON file with

```
cargo run --release -- 4 [job_path] [circuit_json_path]
```

where

-   job_path: is location of obfuscation job's binary
-   circuit_json_path: location to store obfuscated circuit's JSON.

### Verify funtional equivalence of 2 circuits

To verify that two circuits are functionally equal, run

```
cargo run --release -- 5 [circuit0_json_path] [circuit1_json_path] [iterations]
```

where

-   circuit0_json_path: is path to JSON file of circuit 0
-   circuit1_json_path: is path to JSON file of circuit 1
-   iterations: no. of iterations

### Evaluate circuit on input of choice

To evaluate circuit on input of choice run the following,

```
cargo run --release -- 6 [circuit_json_path] [binary_input]
```

-   circuit_json_path: is path to JSON file of circuit to evaluate
-   binary_input: Binary string of the input. String must have `n` bits where `n` are no. of wires in the circuit. For example binary_input = "0,1,0,1" for n = 4.
