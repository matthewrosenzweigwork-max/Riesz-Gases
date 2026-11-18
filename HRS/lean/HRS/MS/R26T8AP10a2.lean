import HRS.MS.R26T8AP00b
import HRS.MS.S82P2Defs

/-!
# S8.2 T8A P10a (part 2): the regularised Riesz kernel `(|w|²+ε²)^(-s/2)`
Derivative, bounds and `ε → 0` limits; coordinates of `gradient` and of `rieszKernelGrad`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

def r26t8a_keps (s ε : ℝ) (w : Euc d) : ℝ := (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2)

/-- `∂_j` of the regularised kernel. -/
def r26t8a_dkeps (s ε : ℝ) (w : Euc d) (j : Fin d) : ℝ :=
  -s * w j * (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)

theorem r26t8a_keps_hasFDerivAt (s : ℝ) {ε : ℝ} (hε : 0 < ε) (w : Euc d) :
    HasFDerivAt (r26t8a_keps s ε)
      ((-s / 2 * (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * 2) • innerSL ℝ w) w := by
  have h1 : HasFDerivAt (fun w : Euc d => ‖w‖ ^ 2) ((2 : ℝ) • innerSL ℝ w) w := by
    convert (hasStrictFDerivAt_norm_sq w).hasFDerivAt using 1
    ext v
    simp
  have h2 := (h1.add_const (ε ^ 2)).rpow_const (p := -s / 2) (Or.inl (by positivity))
  refine h2.congr_fderiv ?_
  ext v
  simp
  ring

theorem r26t8a_fderiv_keps (s : ℝ) {ε : ℝ} (hε : 0 < ε) (w : Euc d) (j : Fin d) :
    fderiv ℝ (r26t8a_keps s ε) w (EuclideanSpace.single j 1) = r26t8a_dkeps s ε w j := by
  rw [(r26t8a_keps_hasFDerivAt s hε w).fderiv]
  simp [r26t8a_dkeps, EuclideanSpace.inner_single_right]
  ring

theorem r26t8a_keps_nonneg (s ε : ℝ) (w : Euc d) : 0 ≤ r26t8a_keps s ε w :=
  Real.rpow_nonneg (by positivity) _

theorem r26t8a_sq_rpow (w : Euc d) (p : ℝ) : (‖w‖ ^ 2) ^ p = ‖w‖ ^ (2 * p) := by
  rw [Real.rpow_mul (norm_nonneg _)]
  norm_cast

theorem r26t8a_keps_le_const {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) (w : Euc d) :
    r26t8a_keps s ε w ≤ (ε ^ 2) ^ (-s / 2) := by
  unfold r26t8a_keps
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖w‖]) (by linarith)

theorem r26t8a_keps_le {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) {w : Euc d} (hw : w ≠ 0) :
    r26t8a_keps s ε w ≤ ‖w‖ ^ (-s) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  unfold r26t8a_keps
  calc (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2) ≤ (‖w‖ ^ 2) ^ (-s / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
    _ = ‖w‖ ^ (-s) := by rw [r26t8a_sq_rpow]; congr 1; ring

theorem r26t8a_abs_coord_le (w : Euc d) (j : Fin d) : |w j| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w j
  rwa [Real.norm_eq_abs] at this

theorem r26t8a_dkeps_le {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) {w : Euc d} (hw : w ≠ 0)
    (j : Fin d) : |r26t8a_dkeps s ε w j| ≤ s * ‖w‖ ^ (-s - 1) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  unfold r26t8a_dkeps
  have h1 : (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) ≤ ‖w‖ ^ (-s - 2) := by
    calc (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) ≤ (‖w‖ ^ 2) ^ (-s / 2 - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
      _ = _ := by rw [r26t8a_sq_rpow]; congr 1; ring
  have h2 : 0 ≤ (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) := Real.rpow_nonneg (by positivity) _
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos hs, abs_of_nonneg h2]
  have h3 : ‖w‖ ^ (-s - 1) = ‖w‖ * ‖w‖ ^ (-s - 2) := by
    rw [← Real.rpow_one_add' hn.le (by linarith)]; congr 1; ring
  rw [h3, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (r26t8a_abs_coord_le w j) h1 h2 hn.le) hs.le

theorem r26t8a_dkeps_le_const {s : ℝ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) (w : Euc d) (j : Fin d) :
    |r26t8a_dkeps s ε w j| ≤ s * (ε ^ 2) ^ (-s / 2 - 1 / 2) := by
  unfold r26t8a_dkeps
  have hb : 0 < ‖w‖ ^ 2 + ε ^ 2 := by positivity
  have h2 : 0 ≤ (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) := Real.rpow_nonneg hb.le _
  have h1 : |w j| ≤ (‖w‖ ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) := by
    refine (r26t8a_abs_coord_le w j).trans ?_
    rw [Real.rpow_div_two_eq_sqrt _ hb.le]
    simp only [Real.rpow_one]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have h3 : (‖w‖ ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) * (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) =
      (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1 / 2) := by
    rw [← Real.rpow_add hb]; congr 1; ring
  have h4 : (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1 / 2) ≤ (ε ^ 2) ^ (-s / 2 - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖w‖]) (by linarith)
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos hs, abs_of_nonneg h2, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hs.le
  calc |w j| * (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) ≤
        (‖w‖ ^ 2 + ε ^ 2) ^ (1 / 2 : ℝ) * (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := h3
    _ ≤ _ := h4

theorem r26t8a_keps_continuous (s ε : ℝ) (hε : 0 < ε) : Continuous (r26t8a_keps (d := d) s ε) := by
  unfold r26t8a_keps
  exact (Continuous.rpow_const (by fun_prop) (fun w => Or.inl (by positivity)))

theorem r26t8a_dkeps_continuous (s ε : ℝ) (hε : 0 < ε) (j : Fin d) :
    Continuous (fun w : Euc d => r26t8a_dkeps s ε w j) := by
  unfold r26t8a_dkeps
  have h1 : Continuous fun w : Euc d => w j := (EuclideanSpace.proj j).continuous
  exact (continuous_const.mul h1).mul
    (Continuous.rpow_const (by fun_prop) (fun w => Or.inl (by positivity)))

theorem r26t8a_dkeps_neg (s ε : ℝ) (w : Euc d) (j : Fin d) :
    r26t8a_dkeps s ε (-w) j = - r26t8a_dkeps s ε w j := by
  simp [r26t8a_dkeps]

theorem r26t8a_keps_tendsto (s : ℝ) {w : Euc d} (hw : w ≠ 0) :
    Tendsto (fun ε : ℝ => r26t8a_keps s ε w) (𝓝[>] 0) (𝓝 (‖w‖ ^ (-s))) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hc : ContinuousAt (fun ε : ℝ => (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2)) 0 := by
    refine ContinuousAt.rpow_const (by fun_prop) (Or.inl (by positivity))
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have h2 : (‖w‖ ^ 2 + (0:ℝ) ^ 2) ^ (-s / 2) = ‖w‖ ^ (-s) := by
    rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, r26t8a_sq_rpow]; congr 1; ring
  rw [h2] at h
  exact h

theorem r26t8a_dkeps_tendsto (s : ℝ) {w : Euc d} (hw : w ≠ 0) (j : Fin d) :
    Tendsto (fun ε : ℝ => r26t8a_dkeps s ε w j) (𝓝[>] 0) (𝓝 (-s * w j * ‖w‖ ^ (-s - 2))) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hc : ContinuousAt (fun ε : ℝ => (‖w‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) 0 := by
    refine ContinuousAt.rpow_const (by fun_prop) (Or.inl (by positivity))
  have h := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).const_mul (-s * w j)
  have h2 : (‖w‖ ^ 2 + (0:ℝ) ^ 2) ^ (-s / 2 - 1) = ‖w‖ ^ (-s - 2) := by
    rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, r26t8a_sq_rpow]; congr 1; ring
  rw [h2] at h
  exact h

theorem r26t8a_gradient_coord (f : Euc d → ℝ) (w : Euc d) (j : Fin d) :
    (gradient f w) j = fderiv ℝ f w (EuclideanSpace.single j 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single j (1:ℝ))
    (y := fderiv ℝ f w)
  rw [real_inner_comm, EuclideanSpace.inner_single_left] at h
  simpa [gradient] using h

theorem r26t8a_rieszGrad_coord {s : ℝ} (hs : s ≠ 0) {w : Euc d} (hw : w ≠ 0) (j : Fin d) :
    (rieszKernelGrad d s w) j = -s * w j * ‖w‖ ^ (-s - 2) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 : HasFDerivAt (fun w : Euc d => ‖w‖ ^ 2) ((2 : ℝ) • innerSL ℝ w) w := by
    convert (hasStrictFDerivAt_norm_sq w).hasFDerivAt using 1
    ext v
    simp
  have h2 := h1.rpow_const (p := -s / 2) (Or.inl (by positivity))
  have hf : rieszKernel d s = fun w : Euc d => (‖w‖ ^ 2) ^ (-s / 2) := by
    funext w
    rw [rieszKernel, if_neg hs, r26t8a_sq_rpow]; congr 1; ring
  unfold rieszKernelGrad
  rw [r26t8a_gradient_coord, hf, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  have : ‖w‖ ^ (-s - 2) = (‖w‖ ^ 2) ^ (-s / 2 - 1) := by
    rw [r26t8a_sq_rpow]; congr 1; ring
  rw [this]
  ring

end HRS.MS.R26T8A
