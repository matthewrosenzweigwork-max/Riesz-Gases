import HRS.MP.SelfSimP4MolD1

/-!
# MPP4MOL stage 5c (2): continuity in `x` (fixed law), the Young term `T` and its integral
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_integrable_norm [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) :
    Integrable (fun y : EucConfig d N => ‖y‖) ν := by
  refine ((integrable_const 1).add hm).mono' continuous_norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (norm_nonneg y)]
  exact p4m_norm_le_q_add y

theorem p4m_integrable_lin_bound [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (A : ℝ) :
    Integrable (fun y : EucConfig d N => A * (1 + ‖y‖)) ν :=
  ((integrable_const 1).add (p4m_integrable_norm hm)).const_mul A

theorem p4m_cont_x [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {φ : EucConfig d N → EucConfig d N → ℝ}
    (hc : Continuous (fun p : EucConfig d N × EucConfig d N => φ p.1 p.2))
    {A : ℝ} (hb : ∀ x y, |φ x y| ≤ A * (1 + ‖y‖)) :
    Continuous (fun x => ∫ y, φ x y ∂ν) := by
  refine continuous_of_dominated (bound := fun y => A * (1 + ‖y‖)) ?_ ?_ (p4m_integrable_lin_bound hm A) ?_
  · intro x
    exact (hc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb x y
  · exact Filter.Eventually.of_forall fun y => hc.comp (Continuous.prodMk continuous_id continuous_const)

theorem p4m_cont_u (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) :
    Continuous (p4Mol v ν) := by
  have hw : Continuous (fun p : EucConfig d N × EucConfig d N => p.1 - p.2) := continuous_fst.sub continuous_snd
  refine p4m_cont_x hm (φ := fun x y => p4Gauss d N v (x - y)) ((p4m_continuous_gauss v).comp hw)
    (A := p4m_cst d N v) fun x y => ?_
  rw [abs_of_pos (p4m_gauss_pos hv _)]
  have := p4m_gauss_le hv (x - y)
  have := p4m_cst_pos (d := d) (N := N) hv
  nlinarith [norm_nonneg y]

theorem p4m_cont_gu (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (k : Fin N × Fin d) :
    Continuous (p4m_gu v ν k) := by
  obtain ⟨A, hA0, hA⟩ := p4m_gk_bound hv (d := d) (N := N) k
  exact p4m_cont_x hm (φ := fun x y => p4m_gk v y k x) (p4m_gk_cont v k) hA

theorem p4m_cont_B (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (k : Fin N × Fin d) : Continuous (p4m_B v ν b k) := by
  obtain ⟨A, hA0, hA⟩ := p4m_hB_bound hv hB hK hbg k
  exact p4m_cont_x hm (φ := fun x y => p4Gauss d N v (x - y) * b y k.1 k.2) (p4m_hB_cont v hbc k) hA

theorem p4m_cont_a (hv : 0 < v) (θ : ℝ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) : Continuous (p4m_a v θ ν b) := by
  obtain ⟨A, hA0, hA⟩ := p4m_ha_bound hv θ hB hK hbg
  exact p4m_cont_x hm (φ := fun x y => p4m_ha v θ b x y) (p4m_ha_cont hbc) hA

/-- The Young term `T(x) = ∫ G(x-y) ∑_k (b_k(y) - b_k(x))² dν(y)`. -/
def p4m_T (v : ℝ) (ν : Measure (EucConfig d N)) (b : EucConfig d N → EucConfig d N) (x : EucConfig d N) : ℝ :=
  ∫ y, p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2 ∂ν

/-- `∫ q(x-y) G(x-y) dν(y)`. -/
def p4m_Q (v : ℝ) (ν : Measure (EucConfig d N)) (x : EucConfig d N) : ℝ :=
  ∫ y, p4m_q (x - y) * p4Gauss d N v (x - y) ∂ν

theorem p4m_sum_sq_le {b : EucConfig d N → EucConfig d N} {Kl : ℝ≥0} (hbl : LipschitzWith Kl b)
    (x y : EucConfig d N) :
    ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2 ≤ N * (Kl : ℝ) ^ 2 * p4m_q (x - y) := by
  have h1 : ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2 = p4m_q (b y - b x) := by
    rw [p4m_q_eq]; rfl
  rw [h1]
  have h2 := p4m_q_le (b y - b x)
  have h3 : ‖b y - b x‖ ≤ Kl * ‖y - x‖ := by
    have := hbl.dist_le_mul y x
    simpa [dist_eq_norm] using this
  have h4 : ‖y - x‖ ^ 2 ≤ p4m_q (x - y) := by
    rw [norm_sub_rev]; exact p4m_norm_sq_le_q _
  have h5 : ‖b y - b x‖ ^ 2 ≤ (Kl : ℝ) ^ 2 * p4m_q (x - y) := by
    calc ‖b y - b x‖ ^ 2 ≤ ((Kl : ℝ) * ‖y - x‖) ^ 2 := by gcongr
      _ = (Kl : ℝ) ^ 2 * ‖y - x‖ ^ 2 := by ring
      _ ≤ _ := by gcongr
  calc p4m_q (b y - b x) ≤ N * ‖b y - b x‖ ^ 2 := h2
    _ ≤ N * ((Kl : ℝ) ^ 2 * p4m_q (x - y)) := by gcongr
    _ = _ := by ring

theorem p4m_T_le_Q (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} {Kl : ℝ≥0} (hbl : LipschitzWith Kl b)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖)
    (x : EucConfig d N) : p4m_T v ν b x ≤ N * (Kl : ℝ) ^ 2 * p4m_Q v ν x := by
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  have hbc : Continuous b := hbl.continuous
  have hKn : (0 : ℝ) ≤ N * (Kl : ℝ) ^ 2 := by positivity
  have hcq : Continuous (fun y : EucConfig d N => p4m_q (x - y) * p4Gauss d N v (x - y)) :=
    (p4m_continuous_q.comp (continuous_const.sub continuous_id)).mul
      ((p4m_continuous_gauss v).comp (continuous_const.sub continuous_id))
  have hi2 : Integrable (fun y : EucConfig d N => p4m_q (x - y) * p4Gauss d N v (x - y)) ν :=
    Integrable.of_bound hcq.aestronglyMeasurable C1 (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (p4m_q_nonneg _) (p4m_gauss_pos hv _).le)]
      have := hb1 (x - y)
      simpa using this)
  have hcs : Continuous (fun y : EucConfig d N => p4Gauss d N v (x - y) *
      ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2) := by
    refine ((p4m_continuous_gauss v).comp (continuous_const.sub continuous_id)).mul ?_
    refine continuous_finset_sum _ fun k _ => ?_
    exact (((p4m_continuous_coord k).comp hbc).sub continuous_const).pow 2
  have hle : ∀ y : EucConfig d N, p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2 ≤
      N * (Kl : ℝ) ^ 2 * (p4m_q (x - y) * p4Gauss d N v (x - y)) := by
    intro y
    have h := p4m_sum_sq_le hbl x y
    have hG := p4m_gauss_pos (d := d) (N := N) hv (x - y)
    nlinarith [mul_le_mul_of_nonneg_left h hG.le]
  have hi1 : Integrable (fun y : EucConfig d N => p4Gauss d N v (x - y) *
      ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2) ν := by
    refine Integrable.of_bound hcs.aestronglyMeasurable (N * (Kl : ℝ) ^ 2 * C1) (Filter.Eventually.of_forall fun y => ?_)
    have hnn : 0 ≤ p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2 :=
      mul_nonneg (p4m_gauss_pos hv _).le (Finset.sum_nonneg fun k _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    refine (hle y).trans ?_
    have := hb1 (x - y)
    simp only [pow_one] at this
    exact mul_le_mul_of_nonneg_left this hKn
  unfold p4m_T p4m_Q
  rw [← integral_const_mul]
  exact integral_mono hi1 (hi2.const_mul _) hle

theorem p4m_Q_prod (hv : 0 < v) [IsProbabilityMeasure ν] :
    Integrable (fun p : EucConfig d N × EucConfig d N =>
      p4m_q (p.1 - p.2) * p4Gauss d N v (p.1 - p.2)) ((volume : Measure (EucConfig d N)).prod ν) := by
  have hk : Integrable (fun w : EucConfig d N => p4m_q w * p4Gauss d N v w) volume := by
    simpa using p4m_integrable_poly_gauss (d := d) (N := N) hv 1
  have := p4m_prod_integrable (ν := ν) hk (integrable_const (1 : ℝ))
  simpa using this

theorem p4m_Q_integrable (hv : 0 < v) [IsProbabilityMeasure ν] : Integrable (p4m_Q v ν) volume :=
  (p4m_Q_prod hv).integral_prod_left

theorem p4m_Q_integral (hv : 0 < v) [IsProbabilityMeasure ν] :
    ∫ x, p4m_Q v ν x = ((N * d : ℕ) : ℝ) * v := by
  have h := integral_integral_swap (μ := (volume : Measure (EucConfig d N))) (ν := ν)
    (f := fun x y => p4m_q (x - y) * p4Gauss d N v (x - y)) (p4m_Q_prod hv)
  unfold p4m_Q
  rw [h]
  have : ∀ y : EucConfig d N, ∫ x, p4m_q (x - y) * p4Gauss d N v (x - y) = ((N * d : ℕ) : ℝ) * v := by
    intro y
    rw [integral_sub_right_eq_self (fun w : EucConfig d N => p4m_q w * p4Gauss d N v w) y]
    exact p4m_integral_q_gauss hv
  simp only [this]
  simp

end

end HRS.MP.SelfSimP4Mol
