import HRS.MP.SelfSimP4MolD4

/-!
# MPP4MOL stage 5b/5c (5): the abstract time-dependent data, joint continuity, and `∂_t u`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

section
variable {v : ℝ}

theorem p4m_ha_bound_unif {v : ℝ} (hv : 0 < v) (θ : ℝ) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ b : EucConfig d N → EucConfig d N, (∀ y, ‖b y‖ ≤ B + K * ‖y‖) →
      ∀ x y, |p4m_ha v θ b x y| ≤ A * (1 + ‖y‖) := by
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  obtain ⟨C2, hC2, hb2⟩ := p4m_gauss_norm_le (d := d) (N := N) hv
  have hn0 : (0 : ℝ) ≤ ((N * d : ℕ) : ℝ) := by positivity
  refine ⟨|θ| * (C1 / v ^ 2 + ((N * d : ℕ) : ℝ) * C0 / v) + (N / v) * C2 * (B + K), by positivity, fun b hbg x y => ?_⟩
  set w := x - y with hw
  have hG := p4m_gauss_pos (d := d) (N := N) hv w
  have h0 := hb0 w
  have h1 := hb1 w
  have h2 := hb2 w
  simp only [pow_zero, one_mul, pow_one] at h0 h1
  have hq := p4m_q_nonneg w
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  unfold p4m_ha
  rw [← hw]
  have hP := p4m_inner_bound w (b y)
  have hby := hbg y
  have hbn : ‖b y‖ ≤ (B + K) * (1 + ‖y‖) := by nlinarith
  -- two terms
  have t1 : |p4Gauss d N v w * (θ * (p4m_q w / v ^ 2 - ((N * d : ℕ) : ℝ) / v))| ≤
      |θ| * (C1 / v ^ 2 + ((N * d : ℕ) : ℝ) * C0 / v) := by
    rw [abs_mul, abs_of_pos hG, abs_mul, mul_left_comm]
    have : |p4m_q w / v ^ 2 - ((N * d : ℕ) : ℝ) / v| ≤ p4m_q w / v ^ 2 + ((N * d : ℕ) : ℝ) / v := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    calc |θ| * (p4Gauss d N v w * |p4m_q w / v ^ 2 - ((N * d : ℕ) : ℝ) / v|)
        ≤ |θ| * (p4Gauss d N v w * (p4m_q w / v ^ 2 + ((N * d : ℕ) : ℝ) / v)) := by gcongr
      _ = |θ| * ((p4m_q w * p4Gauss d N v w) / v ^ 2 + ((N * d : ℕ) : ℝ) * p4Gauss d N v w / v) := by ring
      _ ≤ _ := by gcongr
  have t2 : |p4Gauss d N v w * (p4InnerL w (b y) / v)| ≤ (N / v) * C2 * (B + K) * (1 + ‖y‖) := by
    rw [abs_mul, abs_of_pos hG, abs_div, abs_of_pos hv]
    calc p4Gauss d N v w * (|p4InnerL w (b y)| / v)
        ≤ p4Gauss d N v w * ((N * (‖w‖ * ‖b y‖)) / v) := by gcongr
      _ = (N / v) * (p4Gauss d N v w * ‖w‖) * ‖b y‖ := by ring
      _ ≤ (N / v) * C2 * ((B + K) * (1 + ‖y‖)) := by gcongr
      _ = _ := by ring
  have hsplit : p4Gauss d N v w * (θ * (p4m_q w / v ^ 2 - ((N * d : ℕ) : ℝ) / v) + p4InnerL w (b y) / v) =
      p4Gauss d N v w * (θ * (p4m_q w / v ^ 2 - ((N * d : ℕ) : ℝ) / v)) +
        p4Gauss d N v w * (p4InnerL w (b y) / v) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have : 0 ≤ |θ| * (C1 / v ^ 2 + ((N * d : ℕ) : ℝ) * C0 / v) := by positivity
  nlinarith

theorem p4m_hB_bound_unif (hv : 0 < v) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (k : Fin N × Fin d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ b : EucConfig d N → EucConfig d N, (∀ y, ‖b y‖ ≤ B + K * ‖y‖) →
      ∀ x y : EucConfig d N, |p4Gauss d N v (x - y) * b y k.1 k.2| ≤ A * (1 + ‖y‖) := by
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  refine ⟨C0 * (B + K), by positivity, fun b hbg x y => ?_⟩
  have hG := p4m_gauss_pos (d := d) (N := N) hv (x - y)
  have h0 := hb0 (x - y)
  simp only [pow_zero, one_mul] at h0
  have h1 := p4m_coord_abs_le_norm (b y) k
  have h2 := hbg y
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  rw [abs_mul, abs_of_pos hG]
  calc p4Gauss d N v (x - y) * |b y k.1 k.2| ≤ C0 * (B + K * ‖y‖) := by
        apply mul_le_mul h0 (h1.trans h2) (abs_nonneg _) hC0
    _ ≤ C0 * ((B + K) * (1 + ‖y‖)) := by gcongr; nlinarith
    _ = _ := by ring

end

end HRS.MP.SelfSimP4Mol
