import HRS.MS.SA16Y3Hk2

/-!
# S.A.16 (SA16Y3) Hk3: `|∫ w Q^i(a w)| ≤ ½ (∫ k) ‖w‖_2^2` (packet P7, Hilbert corner)

`sa16y3_young_pair`: `∫ |w| (k ⋆ |w|) ≤ (∫ k) ∫ w²` (AM-GM on the product space).
`sa16y3_comm_pair`: `|∫ w (Q^i(aw) - a Q^i w)| ≤ (∫ k) ∫ w²`.
`sa16y3_Q_half`: `|∫ w Q^i(aw)| ≤ ½ (∫ k) ∫ w²` (skew-adjointness of `Q^i`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hk3
variable {d : ℕ} {s : ℝ}

lemma sa16y3_sq_int {w : Euc d → ℝ} (hw : IsCcInfty w) : Integrable (fun x => w x ^ 2) := by
  have : (fun x => w x ^ 2) = w * w := by funext x; simp [sq]
  rw [this]
  exact (hw.1.continuous.mul hw.1.continuous).integrable_of_hasCompactSupport (hw.2.mul_left)

lemma sa16y3_young_pair {k w : Euc d → ℝ} (hk : Integrable k) (hk0 : ∀ z, 0 ≤ k z) (hw : IsCcInfty w) :
    Integrable (fun x => |w x| * ∫ z, k z * |w (x - z)|) ∧
      ∫ x, |w x| * ∫ z, k z * |w (x - z)| ≤ (∫ z, k z) * ∫ x, w x ^ 2 := by
  have hw2 := sa16y3_sq_int hw
  have hD : Integrable (fun p : Euc d × Euc d => w p.1 ^ 2 * k p.2) ((volume : Measure (Euc d)).prod volume) :=
    hw2.mul_prod hk
  have hE : Integrable (fun p : Euc d × Euc d => k p.2 * w (p.1 - p.2) ^ 2)
      ((volume : Measure (Euc d)).prod volume) := by
    have := hk.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hw2 (μ := (volume : Measure (Euc d)))
    simpa using this
  have hwc : Continuous w := hw.1.continuous
  set H : Euc d × Euc d → ℝ := fun p => |w p.1| * (k p.2 * |w (p.1 - p.2)|) with hHdef
  have hHm : AEStronglyMeasurable H ((volume : Measure (Euc d)).prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => k p.2 * |w (p.1 - p.2)|)
        ((volume : Measure (Euc d)).prod volume) := by
      have := hk.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
        (hwc.abs.aestronglyMeasurable) (μ := (volume : Measure (Euc d)))
      simpa using this
    exact (hwc.abs.comp continuous_fst).aestronglyMeasurable.mul h1
  have hHb : ∀ p : Euc d × Euc d, ‖H p‖ ≤ (1 / 2) * (w p.1 ^ 2 * k p.2 + k p.2 * w (p.1 - p.2) ^ 2) := by
    intro p
    have hk0' := hk0 p.2
    simp only [hHdef, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg hk0' (abs_nonneg _)))]
    have h1 := sq_nonneg (|w p.1| - |w (p.1 - p.2)|)
    have e1 : |w p.1| ^ 2 = w p.1 ^ 2 := sq_abs _
    have e2 : |w (p.1 - p.2)| ^ 2 = w (p.1 - p.2) ^ 2 := sq_abs _
    have key : |w p.1| * (k p.2 * |w (p.1 - p.2)|) ≤
        1 / 2 * (|w p.1| ^ 2 * k p.2 + k p.2 * |w (p.1 - p.2)| ^ 2) := by
      nlinarith [mul_nonneg hk0' h1]
    rw [e1, e2] at key
    exact key
  have hDE : Integrable (fun p : Euc d × Euc d => (1 / 2) * (w p.1 ^ 2 * k p.2 + k p.2 * w (p.1 - p.2) ^ 2))
      ((volume : Measure (Euc d)).prod volume) := (hD.add hE).const_mul _
  have hH : Integrable H ((volume : Measure (Euc d)).prod volume) :=
    Integrable.mono' hDE hHm (Eventually.of_forall hHb)
  have hinner : ∀ x : Euc d, |w x| * ∫ z, k z * |w (x - z)| = ∫ z, H (x, z) := fun x => by
    simp only [hHdef]; rw [integral_const_mul]
  have hG : Integrable (fun x => |w x| * ∫ z, k z * |w (x - z)|) := by
    have := hH.integral_prod_left
    exact this.congr (Eventually.of_forall fun x => (hinner x).symm)
  refine ⟨hG, ?_⟩
  simp_rw [hinner]
  rw [← integral_prod _ hH]
  have hDi : ∫ p : Euc d × Euc d, w p.1 ^ 2 * k p.2 ∂((volume : Measure (Euc d)).prod volume) =
      (∫ x, w x ^ 2) * ∫ z, k z := integral_prod_mul (fun x => w x ^ 2) k
  have hEi : ∫ p : Euc d × Euc d, k p.2 * w (p.1 - p.2) ^ 2 ∂((volume : Measure (Euc d)).prod volume) =
      (∫ z, k z) * ∫ x, w x ^ 2 := by
    rw [integral_prod _ hE]
    have hE' : Integrable (Function.uncurry fun (x z : Euc d) => k z * w (x - z) ^ 2)
        ((volume : Measure (Euc d)).prod volume) := hE
    rw [integral_integral_swap hE']
    have hsh : ∀ z : Euc d, ∫ x, w (x - z) ^ 2 = ∫ x, w x ^ 2 := fun z =>
      integral_sub_right_eq_self (fun x => w x ^ 2) z
    simp_rw [integral_const_mul, hsh]
    rw [integral_mul_const]
  calc ∫ p : Euc d × Euc d, H p ∂((volume : Measure (Euc d)).prod volume)
      ≤ ∫ p : Euc d × Euc d, (1 / 2) * (w p.1 ^ 2 * k p.2 + k p.2 * w (p.1 - p.2) ^ 2)
          ∂((volume : Measure (Euc d)).prod volume) :=
        integral_mono hH hDE fun p => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hHb p)
    _ = (∫ z, k z) * ∫ x, w x ^ 2 := by
        rw [integral_const_mul, integral_add hD hE, hDi, hEi]; ring

theorem sa16y3_comm_pair (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) {a w : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : IsCcInfty w) {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hB : ∀ y, |a y| ≤ B)
    (hL : ∀ y, ‖fderiv ℝ a y‖ ≤ L) (i : Fin d) :
    |∫ x, w x * (sa16y3_Q s i (fun y => a y * w y) x - a x * sa16y3_Q s i w x)| ≤
      (∫ z : Euc d, sa16y3_kk s B L z) * ∫ x, w x ^ 2 := by
  obtain ⟨hG, hle⟩ := sa16y3_young_pair (sa16y3_kk_integrable hd hs0 hsd hθ B L)
    (sa16y3_kk_nonneg hs0 hB0 hL0) hw
  refine (abs_integral_le_integral_abs).trans (le_trans ?_ hle)
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hG (Eventually.of_forall fun x => ?_)
  exact (abs_mul _ _).le.trans
    (mul_le_mul_of_nonneg_left (sa16y3_comm_bound hd hs0 hsd hθ ha hw hB0 hL0 hB hL i x) (abs_nonneg _))

theorem sa16y3_Q_half (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : (d : ℝ) < s + 1) {a w : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : IsCcInfty w) {B L : ℝ} (hB0 : 0 ≤ B) (hL0 : 0 ≤ L) (hB : ∀ y, |a y| ≤ B)
    (hL : ∀ y, ‖fderiv ℝ a y‖ ≤ L) (i : Fin d) :
    |∫ x, w x * sa16y3_Q s i (fun y => a y * w y) x| ≤
      (1 / 2) * ((∫ z : Euc d, sa16y3_kk s B L z) * ∫ x, w x ^ 2) := by
  have hf := sa16y3_bmul_cc ha hw
  have hskew := sa16y3_Q_skew hd hs0 hsd hw hf i
  have hQ1 := (sa16y3_Q_smooth hs0 hsd hf i).continuous
  have hQ2 := (sa16y3_Q_smooth hs0 hsd hw i).continuous
  have hi1 : Integrable (fun x => w x * sa16y3_Q s i (fun y => a y * w y) x) :=
    (hw.1.continuous.mul hQ1).integrable_of_hasCompactSupport hw.2.mul_right
  have hi2 : Integrable (fun x => w x * (a x * sa16y3_Q s i w x)) :=
    (hw.1.continuous.mul (ha.continuous.mul hQ2)).integrable_of_hasCompactSupport hw.2.mul_right
  have h2 : ∫ x, w x * (a x * sa16y3_Q s i w x) = -∫ x, w x * sa16y3_Q s i (fun y => a y * w y) x := by
    have : ∫ x, w x * (a x * sa16y3_Q s i w x) = ∫ x, sa16y3_Q s i w x * (a x * w x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      ring
    rw [this, hskew]; ring
  have h3 : ∫ x, w x * (sa16y3_Q s i (fun y => a y * w y) x - a x * sa16y3_Q s i w x) =
      2 * ∫ x, w x * sa16y3_Q s i (fun y => a y * w y) x := by
    simp_rw [mul_sub]
    rw [integral_sub hi1 hi2, h2]; ring
  have h4 := sa16y3_comm_pair hd hs0 hsd hθ ha hw hB0 hL0 hB hL i
  rw [h3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h4
  linarith

end Hk3

end HRS.Whole.AppendixA.Phase2SA16R
