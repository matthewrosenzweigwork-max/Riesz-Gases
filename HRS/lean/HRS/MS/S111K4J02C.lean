import Mathlib

/-!
# S11.1 / J02, piece C (S111K4): the integral Minkowski inequality in `L²(P)` for nonnegative integrands

`k4j_minkowski_L2`: `∫_P (∫_μ F(z,w) dz)² ≤ (∫_μ (∫_P F(z,w)² dP)^{1/2} dz)²`, by duality with truncations.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111K4J01

theorem k4j_minkowski_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [SFinite μ] (F : ℝ × Ω → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, (∫⁻ z, F (z, w) ∂μ) ^ 2 ∂P ≤
      (∫⁻ z, (∫⁻ w, F (z, w) ^ 2 ∂P) ^ (1 / 2 : ℝ) ∂μ) ^ 2 := by
  set G : Ω → ℝ≥0∞ := fun w => ∫⁻ z, F (z, w) ∂μ with hG
  have hGm : Measurable G := Measurable.lintegral_prod_left' hF
  set M : ℝ≥0∞ := ∫⁻ z, (∫⁻ w, F (z, w) ^ 2 ∂P) ^ (1 / 2 : ℝ) ∂μ with hM
  by_cases hMtop : M = ⊤
  · rw [hMtop]; simp
  have key : ∀ n : ℕ, ∫⁻ w, (min (G w) n) ^ 2 ∂P ≤ M ^ 2 := by
    intro n
    set Gn : Ω → ℝ≥0∞ := fun w => min (G w) n with hGn_def
    have hGn : Measurable Gn := hGm.min measurable_const
    set N : ℝ≥0∞ := ∫⁻ w, Gn w ^ 2 ∂P with hN
    have hNfin : N < ⊤ := by
      calc N ≤ ∫⁻ _w, (n : ℝ≥0∞) ^ 2 ∂P :=
            lintegral_mono fun w => pow_le_pow_left' (min_le_right _ _) 2
        _ = (n : ℝ≥0∞) ^ 2 := by simp
        _ < ⊤ := ENNReal.pow_lt_top (ENNReal.natCast_lt_top n)
    have h1 : N ≤ ∫⁻ w, G w * Gn w ∂P :=
      lintegral_mono fun w => by
        rw [pow_two]; exact mul_le_mul' (min_le_left _ _) le_rfl
    have h2 : ∫⁻ w, G w * Gn w ∂P = ∫⁻ z, ∫⁻ w, F (z, w) * Gn w ∂P ∂μ := by
      have hGnfin : ∀ w, Gn w ≠ ⊤ := fun w =>
        ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
      have : ∀ w, G w * Gn w = ∫⁻ z, F (z, w) * Gn w ∂μ := fun w =>
        (lintegral_mul_const' (Gn w) (fun z => F (z, w)) (hGnfin w)).symm
      simp_rw [this]
      rw [lintegral_lintegral_swap]
      exact (((hF.comp measurable_swap).mul (hGn.comp measurable_fst)).aemeasurable :
        AEMeasurable (fun p : Ω × ℝ => F (p.2, p.1) * Gn p.1) (P.prod μ))
    have h3 : ∀ z, ∫⁻ w, F (z, w) * Gn w ∂P ≤
        (∫⁻ w, F (z, w) ^ 2 ∂P) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) := by
      intro z
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq P (p := 2) (q := 2) Real.HolderConjugate.two_two
        (f := fun w => F (z, w)) (g := Gn)
        (hF.comp measurable_prodMk_left).aemeasurable hGn.aemeasurable
      simpa [ENNReal.rpow_two, hN] using this
    have h4 : N ≤ M * N ^ (1 / 2 : ℝ) := by
      refine h1.trans ?_
      rw [h2]
      calc ∫⁻ z, ∫⁻ w, F (z, w) * Gn w ∂P ∂μ
          ≤ ∫⁻ z, (∫⁻ w, F (z, w) ^ 2 ∂P) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) ∂μ := lintegral_mono h3
        _ = M * N ^ (1 / 2 : ℝ) := by
          rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNfin.ne)]
    set x : ℝ≥0∞ := N ^ (1 / 2 : ℝ) with hx
    have hxN : N = x ^ 2 := by
      rw [hx, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    have hxfin : x ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNfin.ne
    have hxM : x ≤ M := by
      by_cases hx0 : x = 0
      · rw [hx0]; exact bot_le
      · rw [hxN, pow_two] at h4
        have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMtop hxfin) h4
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h5
        have hxpos : 0 < x.toReal := ENNReal.toReal_pos hx0 hxfin
        exact (ENNReal.toReal_le_toReal hxfin hMtop).1 (le_of_mul_le_mul_right h5 hxpos)
    rw [hxN]
    exact pow_le_pow_left' hxM 2
  have hmono : ∀ w, Monotone fun n : ℕ => (min (G w) n) ^ 2 := fun w a b hab =>
    pow_le_pow_left' (min_le_min le_rfl (by exact_mod_cast hab)) 2
  have hlim : Tendsto (fun n : ℕ => ∫⁻ w, (min (G w) n) ^ 2 ∂P) atTop (𝓝 (∫⁻ w, G w ^ 2 ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) (Eventually.of_forall hmono)
      (Eventually.of_forall fun w => ?_)
    · exact ((hGm.min measurable_const).pow_const 2).aemeasurable
    · have h1 : Tendsto (fun n : ℕ => min (G w) (n : ℝ≥0∞)) atTop (𝓝 (min (G w) ⊤)) :=
        (continuous_const.min continuous_id).tendsto _ |>.comp ENNReal.tendsto_nat_nhds_top
      rw [min_top_right] at h1
      exact (ENNReal.continuous_pow 2).tendsto _ |>.comp h1
  exact le_of_tendsto' hlim key

end HRS.MS.S111K4J01
