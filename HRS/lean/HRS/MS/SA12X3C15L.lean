import HRS.MS.SA12X3C15K
import HRS.MS.UniqG2dDef

/-!
# S.A.12 C15 (SA12X3), part L: the near-spill absorption `kappa * card E <= nu / 2` and integrability of cut jets
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_spill_ok {Rg : PDE.Regime} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν ν₀ : ℝ} (hν : 0 ≤ ν)
    (hR : RdRegimeHolds Rg d s M ν ν₀) (E : Finset (Fin d → ℤ)) :
    0 ≤ nearSpill Rg ν₀ E ∧ nearSpill Rg ν₀ E * (E.card : ℝ) ≤ ν / 2 := by
  cases Rg with
  | R3 =>
    have h0 : 0 < ν₀ := hR.2.1
    have h1 : ν₀ ≤ ν := hR.2.2
    simp only [nearSpill]
    refine ⟨by positivity, ?_⟩
    by_cases hc : (E.card : ℝ) = 0
    · rw [hc]; simp; linarith
    · have hcp : 0 < (E.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
      have : ν₀ / (8 * (E.card : ℝ)) * (E.card : ℝ) = ν₀ / 8 := by field_simp
      rw [this]; linarith
  | R2b _ => exact absurd hR id
  | R1 => simp [nearSpill]; linarith
  | R2a => simp [nearSpill]; linarith
  | R2c => simp [nearSpill]; linarith

theorem sa12x3_adv_cut_integrable {m : ℕ} {Cb T : ℝ} {χ : Euc d → ℝ} (hχc : ContDiff ℝ ∞ χ) (hχk : HasCompactSupport χ)
    {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} (hb : IsAdvectingDrift m Cb T b) (hΨ : IsNegDriftFlow T b Ψ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (c : Euc d) {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {j : ℕ}
    (idx : Fin j → Fin d) :
    Integrable (fun x => (advCutoff χ Ψ τ c x * partialDeriv idx F x) ^ 2) := by
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have h1 : Continuous (advCutoff χ Ψ τ c) :=
    hχc.continuous.comp ((hfl.contDiff_inv τ hτ).continuous.sub continuous_const)
  have h2 : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
  have hcs := sa12x2_advCutoff_hasCompactSupport hT hb hΨ hτ hχk c
  exact Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure (Euc d))) ((h1.mul h2).pow 2)
    ((hcs.mul_right (f' := partialDeriv idx F)).comp_left (g := fun t : ℝ => t ^ 2) (by simp))

end HRS.MH.AdjointRd.Phase2SA12Construction
