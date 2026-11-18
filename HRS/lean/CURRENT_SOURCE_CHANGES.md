# Current-source removal of Appendix D.6

The current source omits the unused admitted declaration `HRS.fdl_commutator`.
No replacement theorem or new proof is asserted. The original `hrs-v0.1.0` tag
and historical build, Comparator, replay and axiom receipts retain their original
scope; they are not receipts for these changed source bytes.

Only `HRS/Appendix/FDL.lean` changes among the Lean package source files. Its
summary line 15 and declaration/documentation lines 370–391 are blanked, so
all surviving declarations and downstream source line references are unchanged.
Remark D.7 and its mathematical labels are retained.

Before SHA256: `899dd10aabc2e1a5806c2add4f78e9bb32dd819dedc4158fcc4c1fee20d8756f`

Current SHA256: `c07c58414c8c2804cc36200b2784379fb68b779b21bc0e4202fdd7baccb6d007`

`MANIFEST/SHA256SUMS_included_files.txt` binds current files. `claims_current.tsv`
excludes the removed declaration. `claims_manifest.tsv` and the locator
`inventory/inputs.json` retain their historical evidence scope. Current locator
and axiom TSVs are the historical inventory restricted to surviving declarations,
not fresh kernel queries; their source-location hashes bind current source text.
The 1,182-entry/1,151-constant counts in historical evidence refer to the original
snapshot, before removal; current lists contain 1,181 rows and 1,150 constants.

The old reader `sample-6` and coverage target remain neutral navigation anchors
in Appendix D. Native search snapshots are retained as historical generated
inputs. The live search index and its text payloads exclude the removed card and obsolete prose. The old permalink resolves to Appendix D, without an entry in current search results.
The portable documentation build performs no Lean proof compilation.

## Targeted checks

A scan of the pre-removal compiled environment for all 11,166 base modules found no reference to the removed constant in any of 910,101 declarations, including types, proof and definition bodies, and recursor rules. The 31 compiled companion modules (213 constants) also contained no reference. Thus no retained proof depends on this declaration.

Lean 4.34.1 compiled the changed Appendix D module against the pinned, previously built imports. Importing that new module confirmed that `HRS.fdl_commutator` is absent and the following `HRS.fdl_scope` is still present. The other seven existing admission warnings in the module remain. The check was targeted; there was no new full build, independent-statement comparison, or kernel replay.

In the source manuscripts the lemma and its displayed estimate have no cross-reference outside their own Appendix D subsection. The comparison-kernel identity in the main text comes from Itô’s formula and does not invoke this estimate. The manuscripts themselves have not been changed.
