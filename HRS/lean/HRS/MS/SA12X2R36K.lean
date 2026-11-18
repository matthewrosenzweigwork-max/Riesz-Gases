import HRS.MH.ScreenedF1

/-!
# S.A.12 R36 (SA12X2), part K: compact support of advected cutoffs

For a compactly supported cutoff `χ`, `advCutoff χ Ψ τ z = χ(Ψ_τ^{-1}· − z)` has compact support
(the flow is invertible and Lipschitz, `flow_invertible`, `flow_lipschitz`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_advCutoff_hasCompactSupport {T Cb : ℝ} {m : ℕ} (hT : 0 ≤ T) {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {χ : Euc d → ℝ} (hχ : HasCompactSupport χ) (z : Euc d) :
    HasCompactSupport (advCutoff χ Ψ τ z) := by
  have hb' := HRS.MH.Screened.f1a_drift hb
  have hΨ' := HRS.MH.Screened.f1a_flow hΨ
  obtain ⟨Φ, hΦ1, hΦ2, -⟩ := HRS.MS.FlowA.flow_invertible hT hb' hΨ' τ hτ
  have hL := HRS.MS.FlowA.flow_lipschitz hT hb' hΨ' τ hτ
  have hcont : Continuous (Ψ τ) := by
    refine LipschitzWith.continuous (LipschitzWith.of_dist_le' (K := Real.exp (Cb * τ)) ?_)
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact hL x y
  have hinv : ∀ x, Function.invFun (Ψ τ) x = Φ x := by
    intro x
    have hsurj : ∃ a, Ψ τ a = x := ⟨Φ x, hΦ2 x⟩
    calc Function.invFun (Ψ τ) x = Φ (Ψ τ (Function.invFun (Ψ τ) x)) := (hΦ1 _).symm
      _ = Φ x := by rw [Function.invFun_eq hsurj]
  have hS : IsCompact ((fun y : Euc d => y + z) '' tsupport χ) :=
    hχ.isCompact.image (continuous_id.add continuous_const)
  have hK : IsCompact (Ψ τ '' ((fun y : Euc d => y + z) '' tsupport χ)) := hS.image hcont
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  have hx' : χ (Φ x - z) ≠ 0 := by
    have h0 : advCutoff χ Ψ τ z x ≠ 0 := hx
    unfold advCutoff at h0
    rwa [hinv x] at h0
  have hmem : Φ x - z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.2 hx')
  exact ⟨Φ x, ⟨Φ x - z, hmem, sub_add_cancel _ _⟩, hΦ2 x⟩

end HRS.MH.AdjointRd.Phase2SA12
