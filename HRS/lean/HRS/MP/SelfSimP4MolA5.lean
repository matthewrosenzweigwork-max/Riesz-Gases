import HRS.MP.SelfSimP4MolA4

/-!
# MPP4MOL stage 5a (5): the Gaussian test functions `y ↦ G_v(x - y)` and their generator
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_innerL_norm_le (w : EucConfig d N) : ‖p4InnerL w‖ ≤ N * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [Real.norm_eq_abs]
  have := p4m_inner_bound w h
  linarith

theorem p4m_D1_norm_le {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    ‖fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) w‖ ≤ (1 / v) * p4Gauss d N v w * (N * ‖w‖) := by
  rw [p4m_fderiv_gauss hv, norm_smul, Real.norm_eq_abs]
  have hG := p4m_gauss_pos (d := d) (N := N) hv w
  have : |(-(1 / v) * p4Gauss d N v w)| = (1 / v) * p4Gauss d N v w := by
    rw [abs_of_nonpos (by have : 0 < 1 / v := by positivity
                          nlinarith)]
    ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (p4m_innerL_norm_le w) (by positivity)

theorem p4m_D2_norm_le {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    ‖fderiv ℝ (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) w‖ ≤
      (1 / v ^ 2) * p4Gauss d N v w * (N ^ 2 * ‖w‖ ^ 2) + (1 / v) * p4Gauss d N v w * N := by
  have hG := p4m_gauss_pos (d := d) (N := N) hv w
  set M := (1 / v ^ 2) * p4Gauss d N v w * (N ^ 2 * ‖w‖ ^ 2) + (1 / v) * p4Gauss d N v w * N with hM
  have hM0 : 0 ≤ M := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun h => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h' => ?_
  rw [Real.norm_eq_abs, p4m_fderiv2_gauss hv]
  have h1 := p4m_inner_bound w h
  have h2 := p4m_inner_bound w h'
  have h3 := p4m_inner_bound h h'
  have hv2 : 0 < 1 / v ^ 2 := by positivity
  have hv1 : 0 < 1 / v := by positivity
  calc |(1 / v ^ 2) * p4Gauss d N v w * (p4InnerL w h * p4InnerL w h') -
        (1 / v) * p4Gauss d N v w * p4InnerL h h'|
      ≤ |(1 / v ^ 2) * p4Gauss d N v w * (p4InnerL w h * p4InnerL w h')| +
        |(1 / v) * p4Gauss d N v w * p4InnerL h h'| := abs_sub _ _
    _ = (1 / v ^ 2) * p4Gauss d N v w * (|p4InnerL w h| * |p4InnerL w h'|) +
        (1 / v) * p4Gauss d N v w * |p4InnerL h h'| := by
        simp only [abs_mul, abs_of_pos hG, abs_of_pos hv1, abs_of_pos hv2]
    _ ≤ (1 / v ^ 2) * p4Gauss d N v w * ((N * (‖w‖ * ‖h‖)) * (N * (‖w‖ * ‖h'‖))) +
        (1 / v) * p4Gauss d N v w * (N * (‖h‖ * ‖h'‖)) := by
        gcongr
    _ = M * ‖h‖ * ‖h'‖ := by rw [hM]; ring

/-- The test function `y ↦ G_v(x - y)` as a translate of `G_v`. -/
theorem p4m_test_fun_eq (v : ℝ) (x : EucConfig d N) :
    (fun y => p4Gauss d N v (x - y)) = fun y => p4Gauss d N v (y + -x) := by
  funext y
  rw [← p4m_gauss_neg v (x - y)]
  congr 1
  abel

theorem p4m_fderiv_test {v : ℝ} (x y : EucConfig d N) :
    fderiv ℝ (fun y => p4Gauss d N v (x - y)) y = fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) (y + -x) := by
  rw [p4m_test_fun_eq]
  exact fderiv_comp_add_right (-x)

theorem p4m_fderiv2_test {v : ℝ} (x y : EucConfig d N) :
    fderiv ℝ (fderiv ℝ (fun y => p4Gauss d N v (x - y))) y =
      fderiv ℝ (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) (y + -x) := by
  have : fderiv ℝ (fun y => p4Gauss d N v (x - y)) =
      fun y => fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) (y + -x) := funext (p4m_fderiv_test x)
  rw [this]
  exact fderiv_comp_add_right (f := fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) (-x)

theorem p4m_test {v : ℝ} (hv : 0 < v) (x : EucConfig d N) :
    P4Test (fun y => p4Gauss d N v (x - y)) := by
  have hsm : ContDiff ℝ 2 (fun y : EucConfig d N => p4Gauss d N v (x - y)) :=
    (p4m_contDiff_gauss v).comp (contDiff_const.sub contDiff_id)
  refine ⟨hsm, ?_⟩
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  have hN : (0 : ℝ) ≤ N := by positivity
  refine ⟨C0 + (N / v) * ((1 + ‖x‖) * (C0 + C1) + C1) +
    ((1 / v ^ 2) * (N ^ 2 * C1) + (1 / v) * C0 * N), fun y => ⟨?_, ?_, ?_⟩⟩
  · have := p4m_gauss_le hv (x - y)
    rw [abs_of_pos (p4m_gauss_pos hv _)]
    have : 0 ≤ (N / v) * ((1 + ‖x‖) * (C0 + C1) + C1) := by positivity
    have : 0 ≤ (1 / v ^ 2) * (N ^ 2 * C1) + (1 / v) * C0 * N := by positivity
    have h0 := hb0 (x - y)
    simp only [pow_zero, one_mul] at h0
    linarith
  · rw [p4m_fderiv_test]
    set w := y + -x with hw
    have hG := p4m_gauss_pos (d := d) (N := N) hv w
    have h1 := p4m_D1_norm_le hv w
    have hy : ‖y‖ ≤ ‖w‖ + ‖x‖ := by
      calc ‖y‖ = ‖w + x‖ := by rw [hw]; congr 1; abel
        _ ≤ ‖w‖ + ‖x‖ := norm_add_le _ _
    have hq := p4m_norm_sq_le_q w
    have hq0 := p4m_q_nonneg w
    have hw0 := norm_nonneg w
    have h0 := hb0 w
    have h1' := hb1 w
    simp only [pow_zero, one_mul, pow_one] at h0 h1'
    have hw1 : ‖w‖ ≤ 1 + p4m_q w := by nlinarith
    calc ‖fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) w‖ * (1 + ‖y‖)
        ≤ ((1 / v) * p4Gauss d N v w * (N * ‖w‖)) * (1 + (‖w‖ + ‖x‖)) :=
          mul_le_mul h1 (by linarith) (by positivity) (by positivity)
      _ = (N / v) * ((1 + ‖x‖) * (p4Gauss d N v w * ‖w‖) + p4Gauss d N v w * ‖w‖ ^ 2) := by ring
      _ ≤ (N / v) * ((1 + ‖x‖) * (C0 + C1) + C1) := by
          gcongr
          · nlinarith [mul_le_mul_of_nonneg_left hw1 hG.le]
          · nlinarith [mul_le_mul_of_nonneg_left hq hG.le]
      _ ≤ _ := by
          have : 0 ≤ (1 / v ^ 2) * (N ^ 2 * C1) + (1 / v) * C0 * N := by positivity
          linarith
  · rw [p4m_fderiv2_test]
    set w := y + -x with hw
    have hG := p4m_gauss_pos (d := d) (N := N) hv w
    have h1 := p4m_D2_norm_le hv w
    have hq := p4m_norm_sq_le_q w
    have h0 := hb0 w
    have h1' := hb1 w
    simp only [pow_zero, one_mul, pow_one] at h0 h1'
    have hGq : p4Gauss d N v w * ‖w‖ ^ 2 ≤ C1 := by nlinarith [mul_le_mul_of_nonneg_left hq hG.le]
    have : 0 ≤ C0 + (N / v) * ((1 + ‖x‖) * (C0 + C1) + C1) := by positivity
    calc _ ≤ _ := h1
      _ ≤ (1 / v ^ 2) * (N ^ 2 * C1) + (1 / v) * C0 * N := by
          have e : (1 / v ^ 2) * p4Gauss d N v w * (N ^ 2 * ‖w‖ ^ 2) =
              (1 / v ^ 2) * (N ^ 2 * (p4Gauss d N v w * ‖w‖ ^ 2)) := by ring
          rw [e]
          gcongr
      _ ≤ _ := by linarith

theorem p4m_inner_neg_left (w h : EucConfig d N) : p4InnerL (-w) h = -p4InnerL w h := by
  rw [p4m_inner_comm, map_neg, p4m_inner_comm]

theorem p4m_sum_basis_sq (w : EucConfig d N) :
    ∑ k : Fin N × Fin d, (p4InnerL w (configBasis d N k)) ^ 2 = p4m_q w := by
  rw [p4m_q_eq]
  exact Finset.sum_congr rfl fun k _ => by rw [p4m_inner_single]

/-- The generator applied to the Gaussian test function. -/
theorem p4m_gen_gauss {v : ℝ} (hv : 0 < v) (θ : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (r : ℝ)
    (x y : EucConfig d N) :
    p4Gen θ b r (fun y => p4Gauss d N v (x - y)) y =
      p4Gauss d N v (x - y) *
        (θ * (p4m_q (x - y) / v ^ 2 - ((N * d : ℕ) : ℝ) / v) + p4InnerL (x - y) (b r y) / v) := by
  unfold p4Gen
  rw [p4m_fderiv_test]
  simp only [p4m_fderiv2_test, p4m_fderiv_gauss hv]
  set w := y + -x with hw
  have hxy : x - y = -w := by rw [hw]; abel
  have e1 : ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) w
      (configBasis d N k) (configBasis d N k) =
      (1 / v ^ 2) * p4Gauss d N v w * p4m_q w - (1 / v) * p4Gauss d N v w * ((N * d : ℕ) : ℝ) := by
    simp only [p4m_fderiv2_gauss hv, p4m_inner_single_left, p4m_inner_single]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    · congr 1
      rw [← p4m_sum_basis_sq w]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [p4m_inner_single]
      exact (sq _).symm
    · congr 1
      simp [p4m_inner_single_left, p4m_inner_single, p4m_basis_apply, Finset.card_univ]
  rw [e1, hxy, p4m_gauss_neg, p4m_q_neg]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, p4m_inner_neg_left]
  ring

end HRS.MP.SelfSimP4Mol
