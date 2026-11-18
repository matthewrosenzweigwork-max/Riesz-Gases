import HRS.MS.SA16Y4Ct7

/-!
# S.A.16 (SA16Y4) Ct8: the pairing identity for `R_n`

`sa16y4_R_pair`: for every component `κ`, `N ∈ C_c^∞` and `Y ∈ W^{k,p}`,
`∫ (R_n Y)_κ N = ∫ Y_κ (ρ_n ⋆ N)` (density of `Jcc` + `sa16y4_mol_dual`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct8
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the `κ`-th component functional (pairing with a `C_c^∞` test function) on `WmpSpace` -/
def sa16y4_ellK (k : ℕ) (κ : WIndex d k) {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N) :
    WmpSpace d k p →L[ℝ] ℝ :=
  (sa16s_pair d k p κ hN.1.continuous hN.2).comp (WmpSpace d k p).subtypeL

lemma sa16y4_ellK_apply (k : ℕ) (κ : WIndex d k) {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N)
    (Y : WmpSpace d k p) :
    sa16y4_ellK k κ hN Y = ∫ x, ((Y : WLp d k p) : EuclideanSpace ℝ (Fin d) → WIndex d k → ℝ) x κ * N x := by
  unfold sa16y4_ellK
  rw [ContinuousLinearMap.comp_apply, sa16s_pair_apply]
  rfl

lemma sa16y4_ellK_Jcc (k : ℕ) (κ : WIndex d k) {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N)
    (ψ : ccSub d) : sa16y4_ellK (p := p) k κ hN (sa16r_Jcc d k p ψ) = ∫ x, partialDeriv κ.2 ψ.1 x * N x := by
  rw [sa16y4_ellK_apply, sa16r_Jcc_eq]
  refine integral_congr_ae ?_
  filter_upwards [sa16r_cc_elt_coe (p := p) ψ.2 k] with x hx
  rw [hx]
  rfl

theorem sa16y4_R_pair (k n : ℕ) (R : WmpSpace d k p →L[ℝ] WmpSpace d k p)
    (hR : ∀ ψ : ccSub d, R (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩)
    (κ : WIndex d k) {N : EuclideanSpace ℝ (Fin d) → ℝ} (hN : IsCcInfty N) (Y : WmpSpace d k p) :
    sa16y4_ellK k κ hN (R Y) = sa16y4_ellK k κ (sa16y4_mol_cc hN n) Y := by
  refine (sa16r_Jcc_dense d k p).induction_on Y (isClosed_eq ?_ ?_) (fun ψ => ?_)
  · exact (sa16y4_ellK k κ hN).continuous.comp R.continuous
  · exact (sa16y4_ellK k κ (sa16y4_mol_cc hN n)).continuous
  · rw [hR ψ, sa16y4_ellK_Jcc, sa16y4_ellK_Jcc]
    have h1 : partialDeriv κ.2 (sa16q_mol n ψ.1) = sa16q_mol n (partialDeriv κ.2 ψ.1) :=
      sa16q_mol_pd n (ψ.2.1.of_le (by simp)) κ.2
    simp only [h1]
    exact sa16y4_mol_dual n (sa16s_cc_partialDeriv ψ.2 κ.2) hN
end Ct8

end HRS.Whole.AppendixA.Phase2SA16R
