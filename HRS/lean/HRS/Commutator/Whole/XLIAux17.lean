import HRS.Commutator.Whole.XLIAux16

/-!
# X-LI part 17: the `L^p(ℓ²)` bound for the majorants `YY`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- weighted Cauchy–Schwarz for series -/
lemma tsum_sq_le_weighted (w a : ℤ → ℝ≥0∞) :
    (∑' i, w i * a i) ^ 2 ≤ (∑' i, w i) * ∑' i, w i * a i ^ 2 := by
  have h := sq_lintegral_le (Measure.count : Measure ℤ) (f := w) (g := a)
    (measurable_of_countable w).aemeasurable (measurable_of_countable a).aemeasurable
  simpa only [lintegral_count] using h

section YY

variable (α : ℝ)

lemma wgt_ne_zero_le {n : ℤ} (h : wgt α n ≠ 0) : -2 ≤ n := by
  by_contra hc
  exact h (by unfold wgt; rw [if_neg hc])

/-- the total weight is finite for `α > 0` -/
lemma wgt_sum_ne_top (hα : 0 < α) : ∑' n : ℤ, wgt α n ≠ ⊤ := by
  have hinj : Function.Injective (fun i : ℕ => (-2 : ℤ) + (i : ℤ)) := fun a b h => by
    simpa using h
  have hsupp : Function.support (wgt α) ⊆ Set.range (fun i : ℕ => (-2 : ℤ) + (i : ℤ)) := by
    intro n hn
    have := wgt_ne_zero_le α hn
    exact ⟨(n + 2).toNat, by show (-2 : ℤ) + ((n + 2).toNat : ℤ) = n; omega⟩
  rw [← hinj.tsum_eq hsupp]
  set q : ℝ := ((2 : ℝ) ^ (1 : ℤ)) ^ (-α) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    rw [hq]
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ i : ℕ, wgt α ((-2 : ℤ) + (i : ℤ)) = ENNReal.ofReal (((2 : ℝ) ^ (-2 : ℤ)) ^ (-α) * q ^ i) := by
    intro i
    unfold wgt
    rw [if_pos (by omega), zpow_add₀ (by norm_num), Real.mul_rpow (by positivity) (by positivity)]
    congr 2
    rw [zpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hq, zpow_one,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)]
  · exact ENNReal.ofReal_ne_top
  · exact (summable_geometric_of_lt_one hq0.le hq1).mul_left _

/-- the function `h_m = |F_m| · Gs_m` -/
def hh (φ ψ : SchwartzMap 𝔼 ℂ) (m : ℤ) (y : 𝔼) : ℝ≥0∞ := ‖Fj α φ m y‖ₑ * Gs ψ m y

lemma hh_meas (φ ψ : SchwartzMap 𝔼 ℂ) (m : ℤ) : Measurable (hh α φ ψ m) :=
  (Fj_meas α φ m).enorm.mul (Gs_meas ψ m)

/-- the square function of the majorant -/
def QQ (φ ψ : SchwartzMap 𝔼 ℂ) (y : 𝔼) : ℝ≥0∞ := ∑' j : ℤ, hh α φ ψ j y ^ 2

lemma YY_eq_CvP (φ ψ : SchwartzMap 𝔼 ℂ) (k : ℤ) (x : 𝔼) :
    YY α φ ψ k x = CvP k (fun y => ∑' n : ℤ, wgt α n * hh α φ ψ (k + n) y) x := by
  rw [CvP_tsum k (H := fun n y => wgt α n * hh α φ ψ (k + n) y)
    (fun n => (measurable_const.mul (hh_meas α φ ψ (k + n)))) x]
  unfold YY XX
  refine tsum_congr fun n => ?_
  have hw : wgt α n ≠ ⊤ := by
    unfold wgt
    split_ifs
    · exact ENNReal.ofReal_ne_top
    · simp
  rw [CvP_const_mul k hw _ x]
  rfl

/-- **`L^p(ℓ²)` bound for the majorants** -/
lemma YY_sq_bound (hd : 1 ≤ d) (hα : 0 < α) {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ ψ : SchwartzMap 𝔼 ℂ,
      ∫⁻ x, (∑' k : ℤ, YY α φ ψ k x ^ 2) ^ s ≤ C * ∫⁻ x, QQ α φ ψ x ^ s := by
  obtain ⟨CE, hCE⟩ := E3pos hd hs
  have hs0 : 0 < s := by linarith
  set W : ℝ≥0∞ := ∑' n : ℤ, wgt α n with hW
  have hWne : W ≠ ⊤ := wgt_sum_ne_top α hα
  refine ⟨(CE : ℝ≥0∞) * (W * W) ^ s, ENNReal.mul_ne_top (by simp)
    (ENNReal.rpow_ne_top_of_nonneg hs0.le (ENNReal.mul_ne_top hWne hWne)), fun φ ψ => ?_⟩
  set H : ℤ → 𝔼 → ℝ≥0∞ := fun k y => ∑' n : ℤ, wgt α n * hh α φ ψ (k + n) y with hH
  have hHm : ∀ k, Measurable (H k) := fun k =>
    Measurable.ennreal_tsum fun n => measurable_const.mul (hh_meas α φ ψ (k + n))
  have hY : ∀ k x, YY α φ ψ k x = CvP k (H k) x := fun k x => YY_eq_CvP α φ ψ k x
  have hpt : ∀ y, ∑' k : ℤ, H k y ^ 2 ≤ (W * W) * QQ α φ ψ y := by
    intro y
    calc ∑' k : ℤ, H k y ^ 2
        ≤ ∑' k : ℤ, W * ∑' n : ℤ, wgt α n * hh α φ ψ (k + n) y ^ 2 :=
          ENNReal.tsum_le_tsum fun k => tsum_sq_le_weighted (wgt α) (fun n => hh α φ ψ (k + n) y)
      _ = W * ∑' k : ℤ, ∑' n : ℤ, wgt α n * hh α φ ψ (k + n) y ^ 2 := ENNReal.tsum_mul_left
      _ = W * ∑' n : ℤ, ∑' k : ℤ, wgt α n * hh α φ ψ (k + n) y ^ 2 := by
          rw [ENNReal.tsum_comm]
      _ = W * ∑' n : ℤ, wgt α n * QQ α φ ψ y := by
          congr 1
          refine tsum_congr fun n => ?_
          rw [ENNReal.tsum_mul_left]
          congr 1
          exact (Equiv.addRight n).tsum_eq (fun j : ℤ => hh α φ ψ j y ^ 2)
      _ = (W * W) * QQ α φ ψ y := by
          rw [ENNReal.tsum_mul_right]; ring
  calc ∫⁻ x, (∑' k : ℤ, YY α φ ψ k x ^ 2) ^ s
      = ∫⁻ x, (∑' k : ℤ, CvP k (H k) x ^ 2) ^ s := by
        refine lintegral_congr fun x => ?_
        simp_rw [hY]
    _ ≤ (CE : ℝ≥0∞) * ∫⁻ x, (∑' k : ℤ, H k x ^ 2) ^ s := hCE H hHm
    _ ≤ (CE : ℝ≥0∞) * ∫⁻ x, ((W * W) * QQ α φ ψ x) ^ s := by
        gcongr with x
        exact hpt x
    _ = (CE : ℝ≥0∞) * ∫⁻ x, (W * W) ^ s * QQ α φ ψ x ^ s := by
        congr 1
        refine lintegral_congr fun x => ?_
        exact ENNReal.mul_rpow_of_nonneg _ _ hs0.le
    _ = ((CE : ℝ≥0∞) * (W * W) ^ s) * ∫⁻ x, QQ α φ ψ x ^ s := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le
          (ENNReal.mul_ne_top hWne hWne)), mul_assoc]

end YY

end HRS.Commutator.Whole.XLI
