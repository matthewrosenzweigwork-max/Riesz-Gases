import HRS.Commutator.Whole.XLIAux39

/-!
# X-LI part 40: a general duality lemma
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma dual_gen {s : ℝ} (hs : 1 < s) (V : (𝔼 → ℝ≥0∞) → (𝔼 → ℝ≥0∞))
    (hVm : ∀ w, Measurable w → Measurable (V w)) {CV : ℝ≥0∞} (hCV : CV ≠ ⊤)
    (hV : ∀ w, Measurable w → ∫⁻ x, V w x ^ s.conjExponent ≤ CV * ∫⁻ x, w x ^ s.conjExponent)
    (T Hs : 𝔼 → ℝ≥0∞) (A : ℝ≥0∞) (hT : Measurable T) (hHs : Measurable Hs)
    (hfin : ∫⁻ x, T x ^ s ≠ ⊤)
    (hdual : ∀ w : 𝔼 → ℝ≥0∞, Measurable w → ∫⁻ x, T x * w x ≤ A * ∫⁻ x, Hs x * V w x) :
    ∫⁻ x, T x ^ s ≤ (CV ^ (1 / s.conjExponent) * A) ^ s * ∫⁻ x, Hs x ^ s := by
  set t : ℝ := s.conjExponent with ht
  have hconj : s.HolderConjugate t := Real.HolderConjugate.conjExponent hs
  have ht1 : 1 < t := (Real.holderConjugate_iff.1 hconj.symm).1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hst : 1 / s + 1 / t = 1 := by
    have := hconj.inv_add_inv_eq_one
    simpa [one_div] using this
  have hst2 : (s - 1) * t = s := by
    have h1 : 1 / t = 1 - 1 / s := by linarith
    have h2 : t = 1 / (1 - 1 / s) := by rw [← h1]; field_simp
    rw [h2]
    have : s - 1 ≠ 0 := by linarith
    field_simp
  set X : ℝ≥0∞ := ∫⁻ x, T x ^ s with hX
  set I : ℝ≥0∞ := ∫⁻ x, Hs x ^ s with hI
  set w : 𝔼 → ℝ≥0∞ := fun x => T x ^ (s - 1) with hw
  have hwm : Measurable w := hT.pow_const _
  have hTw : ∀ x, T x * w x = T x ^ s := by
    intro x
    simp only [hw]
    calc T x * T x ^ (s - 1) = T x ^ (1:ℝ) * T x ^ (s - 1) := by rw [ENNReal.rpow_one]
      _ = T x ^ ((1:ℝ) + (s - 1)) :=
          (ENNReal.rpow_add_of_nonneg 1 (s - 1) (by norm_num) (by linarith)).symm
      _ = T x ^ s := by congr 1; ring
  have hwt : ∀ x, w x ^ t = T x ^ s := by
    intro x
    simp only [hw]
    rw [← ENNReal.rpow_mul, hst2]
  have h1 : X ≤ A * ∫⁻ x, Hs x * V w x := by
    have := hdual w hwm
    simpa only [hTw] using this
  have h2 : ∫⁻ x, Hs x * V w x ≤ I ^ (1 / s) * (CV * X) ^ (1 / t) := by
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj (f := Hs) (g := V w)
      hHs.aemeasurable (hVm w hwm).aemeasurable
    refine hH.trans ?_
    gcongr
    refine (hV w hwm).trans ?_
    gcongr
    exact (lintegral_congr fun x => hwt x).le
  have h3 : X ≤ A * (I ^ (1 / s) * (CV ^ (1 / t) * X ^ (1 / t))) := by
    refine h1.trans ?_
    refine mul_le_mul_right ?_ _
    refine h2.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  by_cases hX0 : X = 0
  · rw [hX0]; simp
  have hXtop : X ≠ ⊤ := hfin
  have hsplit : X = X ^ (1 / s) * X ^ (1 / t) := by
    rw [← ENNReal.rpow_add _ _ hX0 hXtop, hst, ENNReal.rpow_one]
  have hpos : X ^ (1 / t) ≠ 0 := by
    intro h; rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with h | h
    · exact hX0 h.1
    · linarith [h.2, one_div_pos.2 ht0]
  have hfin2 : X ^ (1 / t) ≠ ⊤ := by
    intro h; rw [ENNReal.rpow_eq_top_iff] at h
    rcases h with h | h
    · linarith [h.2, one_div_pos.2 ht0]
    · exact hXtop h.1
  have h4 : X ^ (1 / s) ≤ (CV ^ (1 / t) * A) * I ^ (1 / s) := by
    have : X ^ (1 / s) * X ^ (1 / t) ≤ ((CV ^ (1 / t) * A) * I ^ (1 / s)) * X ^ (1 / t) := by
      calc X ^ (1 / s) * X ^ (1 / t) = X := hsplit.symm
        _ ≤ _ := h3
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left hpos hfin2).mp this
  calc X = (X ^ (1 / s)) ^ s := by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one]
    _ ≤ ((CV ^ (1 / t) * A) * I ^ (1 / s)) ^ s := ENNReal.rpow_le_rpow h4 hs0.le
    _ = (CV ^ (1 / t) * A) ^ s * I := by
        have hI' : (I ^ (1 / s)) ^ s = I := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one]
        rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, hI']


end HRS.Commutator.Whole.XLI
