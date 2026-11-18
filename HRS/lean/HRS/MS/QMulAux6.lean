import HRS.MS.QMulAux5

/-!
# MS-QMUL, part 6: Step S, the quantitative multiplier estimate on `QOk m`
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

theorem qm_card_sum (d m : ℕ) (X : ℝ≥0∞) :
    ∑ n ∈ Finset.range (m + 1), ∑ _i : Fin n → Fin d, X ≤
      ENNReal.ofReal (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) * X := by
  have e1 : ENNReal.ofReal (((d : ℝ) + 1) ^ m) = (((d + 1) ^ m : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; push_cast; rfl
  have h1 : ∀ n ∈ Finset.range (m + 1), ∑ _i : Fin n → Fin d, X ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ m) * X := by
    intro n hn
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, e1]
    refine mul_le_mul_left ?_ X
    exact_mod_cast (Nat.pow_le_pow_left (Nat.le_succ d) n).trans
      (Nat.pow_le_pow_right (Nat.succ_pos d) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)))
  calc _ ≤ ∑ n ∈ Finset.range (m + 1), ENNReal.ofReal (((d : ℝ) + 1) ^ m) * X :=
        Finset.sum_le_sum h1
    _ = ENNReal.ofReal (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) * X := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity), ← mul_assoc]
        congr 2
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp

theorem qm_stepS (d m : ℕ) : ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ (θ : Euc d → ℝ) (A : ℝ), ContDiff ℝ m θ →
    (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j θ x‖ ≤ A) → ∀ f : Euc d → ℂ, QOk m f →
      QOk m (fun x => (θ x : ℂ) * f x) ∧
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 (fun x => (θ x : ℂ) * f x) ξ‖ ^ 2) ≤
        ENNReal.ofReal (K2 * A ^ 2) * ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 f ξ‖ ^ 2) := by
  refine ⟨(2 : ℝ) ^ m * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) *
    (((2 : ℝ) ^ m * ((m : ℝ) + 1)) ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) * ((m : ℝ) + 1),
    by positivity, fun θ A hθ hA f hf => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hgOk := qm_QOk_mul hθ hA hf
  refine ⟨hgOk, ?_⟩
  have hSf := qm_upper hf
  have hper : ∀ n ≤ m, ∀ i : Fin n → Fin d,
      ∫⁻ x, ‖qm_pd i (fun y => (θ y : ℂ) * f y) x‖ₑ ^ 2 ≤
        ENNReal.ofReal ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) *
          ∑ l ∈ Finset.range (m + 1), ∑ i' : Fin l → Fin d, ∫⁻ x, ‖qm_pd i' f x‖ₑ ^ 2 := by
    intro n hn i
    calc _ ≤ ∫⁻ x, ENNReal.ofReal ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 *
          (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) *
          ∑ l ∈ Finset.range (m + 1), ∑ i' : Fin l → Fin d, ‖qm_pd i' f x‖ₑ ^ 2 :=
          lintegral_mono fun x => qm_pointwise hθ hA hf.1 hn i x
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun l hl => ?_
          have hl' : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
          rw [lintegral_finsetSum']
          exact fun i' _ => ((qm_continuous_pd hl' hf.1 i').measurable.enorm.pow_const 2).aemeasurable
        · intro l hl
          have hl' : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
          exact Finset.aemeasurable_fun_sum _ fun i' _ =>
            ((qm_continuous_pd hl' hf.1 i').measurable.enorm.pow_const 2).aemeasurable
  have h2m : (2 : ℝ≥0∞) ^ m = ENNReal.ofReal (2 ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have hm1 : ((m : ℝ≥0∞) + 1) = ENNReal.ofReal ((m : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp
  calc _ ≤ _ := qm_lower hgOk
    _ ≤ 2 ^ m * ∑ n ∈ Finset.range (m + 1), ∑ _i : Fin n → Fin d,
          (ENNReal.ofReal ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) *
          ∑ l ∈ Finset.range (m + 1), ∑ i' : Fin l → Fin d, ∫⁻ x, ‖qm_pd i' f x‖ₑ ^ 2) := by
        gcongr with n hn i
        exact hper n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) i
    _ ≤ 2 ^ m * (ENNReal.ofReal (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) *
          (ENNReal.ofReal ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) *
          (((m : ℝ≥0∞) + 1) * ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 f ξ‖ ^ 2)))) := by
        gcongr
        refine (qm_card_sum d m _).trans ?_
        gcongr
    _ = _ := by
        rw [h2m, hm1]
        calc _ = (ENNReal.ofReal (2 ^ m) * ENNReal.ofReal (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m) *
              ENNReal.ofReal ((2 ^ m * ((m : ℝ) + 1)) ^ 2 * A ^ 2 * (((m : ℝ) + 1) * ((d : ℝ) + 1) ^ m)) *
              ENNReal.ofReal ((m : ℝ) + 1)) * ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 f ξ‖ ^ 2) := by ring
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            ring

end HRS.MS.QMul
