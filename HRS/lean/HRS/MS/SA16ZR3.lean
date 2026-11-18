import HRS.MS.SA16ZR2

/-!
# S.A.16 (SA16Z) R3: `L^p` bound of the first-order Leibniz terms `C1`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section R3
variable {d : ℕ} {s : ℝ}

/-- `‖P_a ψ‖_p` for `ψ = ∂^κ φ`, in terms of the jets `S_{r+2}(φ)` -/
lemma sa16z_P_jet_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a φ : Euc d → ℝ}, ContDiff ℝ ∞ a → IsCcInfty φ → ∀ {Ba La : ℝ}, 0 ≤ Ba → 0 ≤ La →
      (∀ y, |a y| ≤ Ba) → (∀ y, ‖fderiv ℝ a y‖ ≤ La) → ∀ {r : ℕ} (κ : Fin r → Fin d),
      eLpNorm (sa16z_P s a (partialDeriv κ φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * (Ba + La) * ((d : ℝ) * (1 + d))) * sa16z_S p φ (r + 2) := by
  obtain ⟨C, hC, hB⟩ := sa16z_P_Lp hd hs0 hsd hθ1 hp
  refine ⟨C, hC, fun {a φ} ha hφ {Ba La} hBa hLa hab hLa' {r} κ => ?_⟩
  have hψ : IsCcInfty (partialDeriv κ φ) := sa16s_cc_partialDeriv hφ κ
  refine (hB ha hψ hBa hLa hab hLa').trans ?_
  have hG : ∀ i : Fin d, eLpNorm (fun y => fderiv ℝ (partialDeriv κ φ) y (sa16z_e i)) (ENNReal.ofReal p) volume ≤
      sa16z_S p φ (r + 2) := by
    intro i
    refine le_trans ?_ (sa16z_JJ_le_S φ (k := r + 1) (N := r + 2) (by omega))
    unfold sa16z_JJ
    refine eLpNorm_mono ((sa16z_dm_cc hψ i).1.continuous.aestronglyMeasurable) fun y => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
    exact sa16z_pd_dm_abs hφ.1 κ i y
  have hH : ∀ i : Fin d, eLpNorm (fun y => ‖fderiv ℝ (sa16z_dm (partialDeriv κ φ) i) y‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal d * sa16z_S p φ (r + 2) := by
    intro i
    refine le_trans ?_ (by gcongr; exact sa16z_JJ_le_S φ (k := r + 2) (N := r + 2) le_rfl : ENNReal.ofReal d * sa16z_JJ p φ (r + 2) ≤ ENNReal.ofReal d * sa16z_S p φ (r + 2))
    unfold sa16z_JJ
    refine sa16z_eLpNorm_le_mul ((sa16z_dm_smooth hψ.1 i).continuous_fderiv (by simp)).norm.aestronglyMeasurable
      (Nat.cast_nonneg d) (fun y => ?_) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
    exact sa16z_pd_dm_fderiv hφ.1 κ i y
  have hsum : ∑ i : Fin d, (eLpNorm (fun y => fderiv ℝ (partialDeriv κ φ) y (sa16z_e i)) (ENNReal.ofReal p) volume +
      eLpNorm (fun y => ‖fderiv ℝ (fun z => fderiv ℝ (partialDeriv κ φ) z (sa16z_e i)) y‖) (ENNReal.ofReal p)
        volume) ≤ ENNReal.ofReal ((d : ℝ) * (1 + d)) * sa16z_S p φ (r + 2) := by
    calc _ ≤ ∑ i : Fin d, (sa16z_S p φ (r + 2) + ENNReal.ofReal d * sa16z_S p φ (r + 2)) :=
          Finset.sum_le_sum fun i _ => add_le_add (hG i) (hH i)
      _ = ENNReal.ofReal ((d : ℝ) * (1 + d)) * sa16z_S p φ (r + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg d)]
          simp [ENNReal.ofReal_natCast]
          ring
  calc ENNReal.ofReal (C * (Ba + La)) * _ ≤ ENNReal.ofReal (C * (Ba + La)) *
        (ENNReal.ofReal ((d : ℝ) * (1 + d)) * sa16z_S p φ (r + 2)) := by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hC (add_nonneg hBa hLa))]

end R3

end HRS.Whole.AppendixA.Phase2SA16R
