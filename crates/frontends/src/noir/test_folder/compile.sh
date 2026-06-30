#!/bin/bash
# Compiles the Noir test circuits into ACIR artifacts (`target/*.json`)
set -euo pipefail
TEST_PATH="$(dirname "$(realpath "${BASH_SOURCE[0]}")")"
for test_path in test_circuit test_no_external_inputs test_bitwise test_brillig test_sha256_compression test_poseidon2 test_keccak test_blake2s test_blake3; do
	(cd "${TEST_PATH}/${test_path}" && nargo compile)
done
