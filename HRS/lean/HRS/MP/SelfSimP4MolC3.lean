import HRS.MP.SelfSimP4MolC2

/-!
# MPP4MOL stage 5b (3): the integration-by-parts identity for the time derivative of `u`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_ha_decomp (v θ : ℝ) (b : EucConfig d N → EucConfig d N) (x y : EucConfig d N) :
    p4m_ha v θ b x y =
      θ * ∑ k : Fin N × Fin d, ((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y) -
        ∑ k : Fin N × Fin d, b y k.1 k.2 * p4m_gk v y k x := by
  have hq : p4m_q (x - y) = ∑ k : Fin N × Fin d, (x - y) k.1 k.2 ^ 2 := p4m_q_eq _
  have hP : p4InnerL (x - y) (b y) = ∑ k : Fin N × Fin d, (x - y) k.1 k.2 * b y k.1 k.2 := p4m_inner_eq _ _
  have hn : (((N * d : ℕ) : ℝ)) = ∑ _k : Fin N × Fin d, (1 : ℝ) := by simp
  unfold p4m_ha p4m_gk
  rw [hq, hP, hn]
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem p4m_ha_cont {v θ : ℝ} {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) :
    Continuous (fun p : EucConfig d N × EucConfig d N => p4m_ha v θ b p.1 p.2) := by
  unfold p4m_ha
  have hw : Continuous (fun p : EucConfig d N × EucConfig d N => p.1 - p.2) := continuous_fst.sub continuous_snd
  refine ((p4m_continuous_gauss v).comp hw).mul ?_
  refine (continuous_const.mul ((p4m_continuous_q.comp hw).div_const _ |>.sub continuous_const)).add ?_
  refine Continuous.div_const ?_ _
  exact (p4m_continuous_innerL.comp hw).clm_apply (hbc.comp continuous_snd)

theorem p4m_gauss_norm_le {v : ℝ} (hv : 0 < v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EucConfig d N, p4Gauss d N v w * ‖w‖ ≤ C := by
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  refine ⟨C0 + C1, by positivity, fun w => ?_⟩
  have hG := p4m_gauss_pos (d := d) (N := N) hv w
  have h0 := hb0 w
  have h1 := hb1 w
  simp only [pow_zero, one_mul, pow_one] at h0 h1
  have hw1 : ‖w‖ ≤ 1 + p4m_q w := p4m_norm_le_q_add w
  nlinarith [mul_le_mul_of_nonneg_left hw1 hG.le]

theorem p4m_ha_bound {v : ℝ} (hv : 0 < v) (θ : ℝ) {b : EucConfig d N → EucConfig d N} {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y, |p4m_ha v θ b x y| ≤ A * (1 + ‖y‖) := by
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  obtain ⟨C2, hC2, hb2⟩ := p4m_gauss_norm_le (d := d) (N := N) hv
  have hn0 : (0 : ℝ) ≤ ((N * d : ℕ) : ℝ) := by positivity
  refine ⟨|θ| * (C1 / v ^ 2 + ((N * d : ℕ) : ℝ) * C0 / v) + (N / v) * C2 * (B + K), by positivity, fun x y => ?_⟩
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

end HRS.MP.SelfSimP4Mol
