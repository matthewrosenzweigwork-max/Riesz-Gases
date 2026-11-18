# Paper and Lean source index

[Browse the complete index](index.html) or read [the evidence guide](evidence.html). The headings cover the main paper and supplement: 24 sections, 143 subsections, 315 named items and 20 additional passages. Lean is authoritative.

- `headings.tsv` and `paper-sources.tsv`: manuscript headings and loci.
- `claim-locators.tsv`: historical claim rows, preserving their original scope.
- `declaration-locators.tsv`: exact current declaration name, module, source hash and line where bound; seven qualifications corrected from the recorded tokens.
- `current-axioms.tsv`: the axiom dependencies Lean reported for 1,151 individual constants on the compiled frozen package.
- `checks/ProofBindings.lean`: exact proof expressions for 347 admitted base constants; independently named providers or composites of retained results. The two binder-order adapters and the rebuilt entropy dispatcher are explicit.
- `checks/WholeSpaceSupplement.lean`: the two additional proof expressions in the [companion source](../proof-supplement/README.md).
- `featured-declarations.tsv`: the original 18 paired reader entries. The eight whole-space additions are in the reader and the canonical native handoff. `selected-paper-providers.tsv` records eight initial paper-index examples and is not a complete proof inventory.

Sixteen historical row tokens lack a bound module. Sixteen different manuscript remarks have no claim-ledger row. Neither set is counted as a failed proof. The original frozen ledger and export notes are unmodified in `../lean/`; this index distinguishes stale specification labels from actual proved terms.
