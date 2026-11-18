import HRS.MS.R2IidAux1

/-!
# S11IID: the iid rows of `Round2.lean`, ties

`r2_static_edgeworth_iid_proof` proves the frozen row `HRS.Whole.r2_static_edgeworth_iid` (`R2StaticEdgeworth d 0 0 m ρ`
for a probability density `ρ`) from the Hilbert-space Edgeworth expansion `HRS.hilbert_edgeworth_C4` applied on the product space
`((ℕ → ℝ^d) × B_m, μ^{⊗ℕ} ⊗ G)` (`HRS/MS/R2IidAux1.lean`, `s11iid_static`).  No statement was adjusted.
-/

noncomputable section

namespace HRS.MS.R2Iid

theorem r2_static_edgeworth_iid_proof : type_of% @HRS.Whole.r2_static_edgeworth_iid :=
  @HRS.Whole.s11iid_static

example := (@r2_static_edgeworth_iid_proof : type_of% @HRS.Whole.r2_static_edgeworth_iid)

end HRS.MS.R2Iid
