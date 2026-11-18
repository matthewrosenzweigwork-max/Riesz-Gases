import HRS.MP.SelfSimP4MolF1

/-!
# MPP4MOL stage 5c (11): pointwise bounds for the cut-off error terms
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_gauss_norm_E {v : ℝ} (hv : 0 < v) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ w : EucConfig d N, p4Gauss d N v w * (1 + ‖w‖) ≤ c * p4m_E (1 / (4 * v)) w := by
  have hc := p4m_cst_pos (d := d) (N := N) hv
  refine ⟨p4m_cst d N v * (2 + 4 * v), by positivity, fun w => ?_⟩
  have hb : (0 : ℝ) < 1 / (2 * v) := by positivity
  have hp := p4m_E_poly_bound (d := d) (N := N) hb 1 w
  have e1 : -(1 / (2 * v) / 2) = -(1 / (4 * v)) := by field_simp; ring
  rw [e1] at hp
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_mul] at hp
  have e2 : 2 / (1 / (2 * v)) = 4 * v := by field_simp; ring
  rw [e2] at hp
  have hE0 : 0 < p4m_E (1 / (4 * v)) w := p4m_E_pos _ _
  have hE1 : p4m_E (1 / (4 * v)) w ≤ 1 := by
    unfold p4m_E
    rw [Real.exp_le_one_iff]
    have := p4m_q_nonneg w
    have : 0 ≤ 1 / (4 * v) * p4m_q w := by positivity
    linarith
  have hq : p4m_q w * p4m_E (1 / (4 * v)) w ≤ 4 * v := by
    have : p4m_E (1 / (4 * v)) w = Real.exp (-(1 / (4 * v)) * p4m_q w) := rfl
    rw [this]; exact hp
  have hn : ‖w‖ ≤ 1 + p4m_q w := by
    have := p4m_norm_sq_le_q w
    nlinarith [sq_nonneg (‖w‖ - 1), norm_nonneg w]
  have hsplit : p4m_E (1 / (4 * v)) w * p4m_E (1 / (4 * v)) w = p4m_E (1 / (2 * v)) w := by
    simp only [p4m_E, ← Real.exp_add]; congr 1; field_simp; ring
  rw [p4m_gauss_eq_E hv, ← hsplit]
  have h3 : (1 + ‖w‖) * p4m_E (1 / (4 * v)) w ≤ 2 + 4 * v := by
    have : (1 + ‖w‖) * p4m_E (1 / (4 * v)) w ≤ (2 + p4m_q w) * p4m_E (1 / (4 * v)) w :=
      mul_le_mul_of_nonneg_right (by linarith) hE0.le
    nlinarith
  calc p4m_cst d N v * (p4m_E (1 / (4 * v)) w * p4m_E (1 / (4 * v)) w) * (1 + ‖w‖)
      = p4m_cst d N v * p4m_E (1 / (4 * v)) w * ((1 + ‖w‖) * p4m_E (1 / (4 * v)) w) := by ring
    _ ≤ p4m_cst d N v * p4m_E (1 / (4 * v)) w * (2 + 4 * v) := by gcongr
    _ = _ := by ring

theorem p4m_integrable_E_sub {v : ℝ} (hv : 0 < v) (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν]
    (x : EucConfig d N) {a : ℝ} (ha : 0 ≤ a) : Integrable (fun y => p4m_E a (x - y)) ν := by
  refine Integrable.of_bound ((p4m_continuous_E a).comp (continuous_const.sub continuous_id)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (p4m_E_pos _ _).le]
  unfold p4m_E
  rw [Real.exp_le_one_iff]
  have := p4m_q_nonneg (x - y)
  have : 0 ≤ a * p4m_q (x - y) := by positivity
  linarith

/-- Pointwise bound for the flux `J_k = θ ∂_k u - B_k` by the weight `W`. -/
theorem p4m_J_bound {v : ℝ} (hv : 0 < v) (θ : ℝ) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν], Integrable p4m_q ν →
      ∀ (b : EucConfig d N → EucConfig d N), (∀ y, ‖b y‖ ≤ B + K * ‖y‖) → Continuous b →
      ∀ (k : Fin N × Fin d) (x : EucConfig d N),
      |θ * p4m_gu v ν k x - p4m_B v ν b k x| ≤
        A * ((1 + ‖x‖) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν) := by
  obtain ⟨c, hc0, hc⟩ := p4m_gauss_norm_E (d := d) (N := N) hv
  refine ⟨c * (|θ| / v + B + K), by positivity, fun ν _ hm b hbg hbc k x => ?_⟩
  have hb0 : (0 : ℝ) ≤ 1 / (4 * v) := by positivity
  have hE := p4m_integrable_E_sub hv ν x hb0
  obtain ⟨A1, hA1, hA1'⟩ := p4m_gk_bound hv (d := d) (N := N) k
  have hg1 : Integrable (fun y => -(1 / v) * p4Gauss d N v (x - y) * (x - y) k.1 k.2) ν :=
    p4m_integrable_lin hm (φ := fun y => p4m_gk v y k x)
      (((p4m_gk_cont v k).comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
      (fun y => hA1' x y)
  have hg2 := p4m_integrable_hB hv hm hbc hB hK hbg k x
  have hJ : θ * p4m_gu v ν k x - p4m_B v ν b k x =
      ∫ y, (θ * (-(1 / v) * p4Gauss d N v (x - y) * (x - y) k.1 k.2) -
        p4Gauss d N v (x - y) * b y k.1 k.2) ∂ν := by
    rw [integral_sub (hg1.const_mul θ) hg2, integral_const_mul]
    rfl
  rw [hJ]
  have hmul : ∫ y, (c * (|θ| / v + B + K)) * ((1 + ‖x‖) * p4m_E (1 / (4 * v)) (x - y)) ∂ν =
      (c * (|θ| / v + B + K)) * ((1 + ‖x‖) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν) := by
    rw [integral_const_mul, integral_const_mul]
  rw [← hmul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((hE.const_mul (1 + ‖x‖)).const_mul _)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  set w := x - y with hw
  have hG := p4m_gauss_pos (d := d) (N := N) hv w
  have hcw := hc w
  have hn0 := norm_nonneg w
  have hE0 := p4m_E_pos (d := d) (N := N) (1 / (4 * v)) w
  have hGle : p4Gauss d N v w ≤ c * p4m_E (1 / (4 * v)) w := by nlinarith
  have hGn : p4Gauss d N v w * ‖w‖ ≤ c * p4m_E (1 / (4 * v)) w := by nlinarith
  have hwk : |w k.1 k.2| ≤ ‖w‖ := p4m_coord_abs_le_norm w k
  have hbk : |b y k.1 k.2| ≤ B + K * ‖y‖ := (p4m_coord_abs_le_norm (b y) k).trans (hbg y)
  have hy : ‖y‖ ≤ ‖x‖ + ‖w‖ := by
    have : y = x - w := by rw [hw]; abel
    calc ‖y‖ = ‖x - w‖ := by rw [← this]
      _ ≤ ‖x‖ + ‖w‖ := norm_sub_le _ _
  have hx0 := norm_nonneg x
  have t1 : |θ * (-(1 / v) * p4Gauss d N v w * w k.1 k.2)| ≤ |θ| / v * (c * p4m_E (1 / (4 * v)) w) := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / v), abs_of_pos hG]
    calc |θ| * (1 / v * p4Gauss d N v w * |w k.1 k.2|) ≤ |θ| * (1 / v * p4Gauss d N v w * ‖w‖) := by gcongr
      _ = |θ| / v * (p4Gauss d N v w * ‖w‖) := by ring
      _ ≤ _ := by gcongr
  have t2 : |p4Gauss d N v w * b y k.1 k.2| ≤ (B + K * ‖x‖) * (c * p4m_E (1 / (4 * v)) w) +
      K * (c * p4m_E (1 / (4 * v)) w) := by
    rw [abs_mul, abs_of_pos hG]
    calc p4Gauss d N v w * |b y k.1 k.2| ≤ p4Gauss d N v w * (B + K * ‖y‖) := by gcongr
      _ ≤ p4Gauss d N v w * (B + K * ‖x‖ + K * ‖w‖) := by
          exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hy hK]) hG.le
      _ = (B + K * ‖x‖) * p4Gauss d N v w + K * (p4Gauss d N v w * ‖w‖) := by ring
      _ ≤ _ := by gcongr
  have hsub : |θ * (-(1 / v) * p4Gauss d N v w * w k.1 k.2) - p4Gauss d N v w * b y k.1 k.2| ≤
      |θ * (-(1 / v) * p4Gauss d N v w * w k.1 k.2)| + |p4Gauss d N v w * b y k.1 k.2| := abs_sub _ _
  have hfin : |θ| / v * (c * p4m_E (1 / (4 * v)) w) + ((B + K * ‖x‖) * (c * p4m_E (1 / (4 * v)) w) +
      K * (c * p4m_E (1 / (4 * v)) w)) ≤
      c * (|θ| / v + B + K) * ((1 + ‖x‖) * p4m_E (1 / (4 * v)) w) := by
    have h0 : 0 ≤ c * p4m_E (1 / (4 * v)) w := by positivity
    have : 0 ≤ |θ| / v := by positivity
    nlinarith [mul_nonneg h0 (mul_nonneg hK hx0), mul_nonneg h0 (mul_nonneg hB hx0), mul_nonneg h0 (mul_nonneg this hx0)]
  linarith

end HRS.MP.SelfSimP4Mol
