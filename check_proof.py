import sys
from collections import defaultdict

import citip_parsing

if len(sys.argv) != 3:
    print(f"Usage: {sys.argv[0]} input.citip output.proof")
    sys.exit()
input_file = sys.argv[1]
proof_file = sys.argv[2]

target, steps = citip_parsing.parse_proof(input_file, proof_file)

# Track the total of all proof steps, storing it as a dict mapping from (world, set(random vars)) to
# coefficient.
total = defaultdict(float)
total_rhs = 0.0
for is_equality, terms, rhs in steps:
    total_rhs += rhs
    for coeff, world, term in terms:
        total[(world, term)] += coeff

target_terms, target_rhs = target

# Check that the proof matches the bound (to some precision)

precision = 1e-4
total_rhs -= target_rhs
assert(abs(total_rhs) <= precision)

for coeff, world, term in target_terms:
    total[(world, term)] -= coeff

for (world, term), coeff in total.items():
    assert(abs(coeff) <= precision)

print("Verification successful.")
print(f"Note that this only checks that the steps listed in \"{proof_file}\"")
print(f"(and the implicit functional dependencies from \"{input_file}\") imply")
print(f"the consequences stated at the end of \"{proof_file}\". It does not")
print(f"check that the bounds used in each step match those listed in \"{input_file}\".")
