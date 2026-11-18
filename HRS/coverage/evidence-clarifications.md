> Historical verification snapshot; see [current-source scope](../lean/CURRENT_SOURCE_CHANGES.md) for the later removal.

# Reading the proof statuses

**Common coercivity.** In the frozen package's scope note, read the old declaration in the exclusions list as `HRS.commutator_coercivity_common`. Its separately proved provider is `HRS.commutator_coercivity_common_proof` (HRS/Energy/Commutator/CommonProof.lean, line 23). Row 241 of the current manifest records the independent-statement Comparator pass for that provider. A new axiom check of the exact sanitized build reports only the three standard axioms for the provider.

**Specifications and providers.** The frozen `HRS.screening_comparison` is admitted. Use `HRS.screening_comparison_proof` for its proof: their types were checked equal; the latter has only the standard axioms. The corresponding stationary-limit and first-order commutator entries make the same distinction explicitly in the reader.

**Two fields, two meanings.** The row for `HRS.Whole.r2_two_parameter_edgeworth` retains the historical coverage label “stated” and, separately, a theorem pass via a tie to the frozen statement. A theorem pass for a tied provider is not an axiom clearance of the old specification. Sixteen unresolved claim tokens lack a bound Lean module; sixteen separate remarks lack a historical claim row. Neither omission, by itself, diagnoses a missing theorem.

**Eight whole-space declarations.** The [scoped axiom report](headline-axioms.json) records the eight declarations shown in the whole-space chapter and the common-coercivity provider. The compiler reported only `propext`, `Classical.choice` and `Quot.sound`. This probe used the already compiled modules of the accepted sanitized package. It did not repeat the historical independent-statement Comparator tests or kernel replays.

The exact-byte package build was incremental. Results from the earlier cold build and earlier independent Comparator and replay runs retain their own input and scope. All of these checks are distinct from comparison of the English statements with Lean, and from verification of the manuscript’s written proofs.


**Complete scoped axiom inventory.** Of 1,151 distinct probed constants, 350 depend on `sorryAx`. The shipped [base type checks](checks/ProofBindings.lean) provide separate standard-axiom terms of exactly the required type for 347. The [proof supplement](../proof-supplement/README.md) restores two source providers omitted during base pruning, for S11.1 and S11.2.

The 347 include the three S8.1 critical clauses by applying the corresponding forcing lemma to the proved forcing term, and the S8.3 weighted adjoint estimate from its proved provider. Earlier records marked these four simply as theorem passes. Their original specification constants remain admission-dependent. No new independent two-kernel comparison is claimed.
