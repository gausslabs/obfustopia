import copy

WIRES_DEFAULT = 3

class CNOT:
    def __init__(self, control: int, out: int, control_not: bool, wires: int=WIRES_DEFAULT):
        self.control = control
        self.out = out
        self.control_not = control_not
        self.wires = wires

    def evaluate(self, input: [bool]) -> [bool]:
        assert len(input) == self.wires
        input = copy.deepcopy(input)

        to_not = input[self.control] ^ self.control_not
        input[self.out] = input[self.out] ^ to_not
        return input

class Circuit:
    def __init__(self, gates: [CNOT]):
        self.gates = gates
        self.wires = gates[0].wires

    def evaluate(self, input: [bool]):
        out = copy.deepcopy(input)
        for g in self.gates:
            out = g.evaluate(out)
        return out



def find_permutation(circuit: Circuit): 
    wires = circuit.wires
    low = 0
    high = (1<<wires)

    permutation = []
    for v in range(low, high):
        input = []
        for i in range(0, wires):
            input.append(bool((v >> i)&1))
        output = circuit.evaluate(input=input)

        diff = 0
        for (v0, v1) in zip(input, output):
            if v0 != v1:
                diff +=1
        print(diff)

        vout = 0
        for index, b in enumerate(output):
            vout+=(int(b)<<index)
        permutation.append(vout)

    return permutation

circuit1 = Circuit(
    gates=[
        CNOT(2, 0, False),
        CNOT(1, 2, False),
        CNOT(0, 1, True)
    ]
)

circuit2 = Circuit(
    gates=[
        CNOT(2, 0, False),
        CNOT(1, 2, True),
        CNOT(0, 1, True)
    ]
)

print(find_permutation(circuit=circuit1))
print(find_permutation(circuit=circuit2))

    

        
