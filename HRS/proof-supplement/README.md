# Proof supplement: Proposition S11.1 and Corollary S11.2

These 31 Lean modules contain the proofs of covariance and cubic-tensor relaxation (Supplement Proposition S11.1) and the joint particle-number and time limits (Supplement Corollary S11.2). Each is byte-identical to the source used for the earlier independent comparison and to its hash in the frozen base's list of omitted modules. Their 48 direct retained-module dependencies remain in the original base.

| Frozen statement in `HRS.Whole` | Proved term in `HRS.Fp81.V01` |
| --- | --- |
| `r2_tensor_relaxation` | `fp81v01_tensor_relaxation` |
| `r2_two_parameter_edgeworth` | `fp81v01_two_parameter_edgeworth` |

Both proved terms are in [the final module](HRS/MS/Fp81V01Final.lean). The [type check](ExactTypes.lean) uses the full type of each frozen statement. The frozen [base package](../lean/) is unchanged.

## Reproduce the scoped check

Build the base under its pinned Lean toolchain first. Use Python 3.10 or later and a filesystem with symbolic-link support:

```sh
python3 build_proof_supplement.py \
  --base ../lean --lean "$(elan which lean)" \
  --output "$(mktemp -d)/supplement"
```

Run from this directory. The build uses the existing pinned base and dependency caches, compiles only the 31 added modules into a new directory, then checks the two exact proof terms. None of the original package's source files or cache entries is overwritten. The command needs no network once the base is built. It does not repeat the historical independent two-kernel comparison.
