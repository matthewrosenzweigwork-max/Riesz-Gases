import HRS.MP.SelfSimP4Gibbs

/-!
# MP-SSP4JENSEN: `p4_initial_jensen` (Jensen bound for the mollified initial free energy)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4j_`.  Theorem `p4_initial_jensen_proof`, tied to
`HRS.MP.SelfSimP4.p4_initial_jensen`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory Set
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

variable {d N : ℕ}

/-! ### The quadratic form and the Gaussian kernel -/

/-- `Φ(x) = ∑_i ‖x_i‖²`. -/
def p4j_Phi (x : EucConfig d N) : ℝ := ∑ i, ‖x i‖ ^ 2

theorem p4j_Phi_nonneg (x : EucConfig d N) : 0 ≤ p4j_Phi x := Finset.sum_nonneg fun i _ => sq_nonneg _

theorem p4j_Phi_continuous : Continuous (p4j_Phi : EucConfig d N → ℝ) := by
  unfold p4j_Phi; fun_prop

theorem p4j_Phi_neg (x : EucConfig d N) : p4j_Phi (-x) = p4j_Phi x := by
  simp [p4j_Phi]

theorem p4j_Phi_smul (c : ℝ) (x : EucConfig d N) : p4j_Phi (c • x) = c ^ 2 * p4j_Phi x := by
  simp only [p4j_Phi, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem p4j_Phi_add_le (x y : EucConfig d N) : p4j_Phi (x + y) ≤ 2 * p4j_Phi x + 2 * p4j_Phi y := by
  unfold p4j_Phi
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (x i) (y i)
  have h0 := norm_nonneg (x i + y i)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖x i‖ - ‖y i‖), norm_nonneg (x i), norm_nonneg (y i)]

theorem p4j_norm_sq_le_Phi (x : EucConfig d N) : ‖x‖ ^ 2 ≤ p4j_Phi x := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have : ‖x‖ = 0 := by simp [Subsingleton.elim x 0]
    simp [this, p4j_Phi]
  · have hle : ‖x‖ ≤ Real.sqrt (p4j_Phi x) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖x‖ ^ 2 ≤ Real.sqrt (p4j_Phi x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = p4j_Phi x := Real.sq_sqrt (p4j_Phi_nonneg x)

theorem p4j_Phi_le_norm_sq (x : EucConfig d N) : p4j_Phi x ≤ N * ‖x‖ ^ 2 := by
  calc p4j_Phi x ≤ ∑ _i : Fin N, ‖x‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
    _ = N * ‖x‖ ^ 2 := by simp

/-- The normalising constant of the Gaussian. -/
def p4j_c (d N : ℕ) (v : ℝ) : ℝ := (2 * Real.pi * v) ^ (-((N * d : ℕ) : ℝ) / 2)

theorem p4j_gauss_eq (v : ℝ) (w : EucConfig d N) :
    p4Gauss d N v w = p4j_c d N v * Real.exp (-(p4j_Phi w) / (2 * v)) := rfl

theorem p4j_c_pos {v : ℝ} (hv : 0 < v) : 0 < p4j_c d N v := by
  unfold p4j_c
  have : 0 < 2 * Real.pi * v := by positivity
  positivity

theorem p4j_gauss_pos {v : ℝ} (hv : 0 < v) (w : EucConfig d N) : 0 < p4Gauss d N v w :=
  mul_pos (p4j_c_pos hv) (Real.exp_pos _)

theorem p4j_gauss_le {v : ℝ} (hv : 0 < v) (w : EucConfig d N) : p4Gauss d N v w ≤ p4j_c d N v := by
  rw [p4j_gauss_eq]
  have : Real.exp (-(p4j_Phi w) / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := p4j_Phi_nonneg w
    have : 0 ≤ p4j_Phi w / (2 * v) := by positivity
    linarith [neg_div (2 * v) (p4j_Phi w)]
  nlinarith [p4j_c_pos (d := d) (N := N) hv]

theorem p4j_gauss_neg (v : ℝ) (w : EucConfig d N) : p4Gauss d N v (-w) = p4Gauss d N v w := by
  rw [p4j_gauss_eq, p4j_gauss_eq, p4j_Phi_neg]

theorem p4j_gauss_continuous (v : ℝ) : Continuous (p4Gauss d N v : EucConfig d N → ℝ) := by
  unfold p4Gauss; fun_prop

theorem p4j_gauss_measurable (v : ℝ) : Measurable (p4Gauss d N v : EucConfig d N → ℝ) :=
  (p4j_gauss_continuous v).measurable

/-! ### Gaussian integrals -/

theorem p4j_vol_pi : (volume : Measure (EucConfig d N)) = Measure.pi fun _ : Fin N => (volume : Measure (Euc d)) :=
  rfl

theorem p4j_exp_eq_prod (a : ℝ) (w : EucConfig d N) :
    Real.exp (-a * p4j_Phi w) = ∏ i, Real.exp (-a * ‖w i‖ ^ 2) := by
  rw [p4j_Phi, Finset.mul_sum, ← Real.exp_sum]

theorem p4j_integrable_exp {a : ℝ} (ha : 0 < a) :
    Integrable (fun w : EucConfig d N => Real.exp (-a * p4j_Phi w)) := by
  have h : Integrable (fun w : EucConfig d N => ∏ i, Real.exp (-a * ‖w i‖ ^ 2))
      (Measure.pi fun _ : Fin N => (volume : Measure (Euc d))) :=
    Integrable.fintype_prod (f := fun _ : Fin N => fun x : Euc d => Real.exp (-a * ‖x‖ ^ 2))
      (μ := fun _ => (volume : Measure (Euc d))) fun i => by
        have := p4g_integrable_gauss d ha
        simpa [neg_mul] using this
  rw [p4j_vol_pi]
  exact h.congr (Eventually.of_forall fun w => (p4j_exp_eq_prod a w).symm)

theorem p4j_integral_exp {a : ℝ} (ha : 0 < a) :
    ∫ w : EucConfig d N, Real.exp (-a * p4j_Phi w) = (Real.pi / a) ^ (((N * d : ℕ) : ℝ) / 2) := by
  have h1 : ∫ w : EucConfig d N, ∏ i, Real.exp (-a * ‖w i‖ ^ 2) =
      ∏ _i : Fin N, ∫ x : Euc d, Real.exp (-a * ‖x‖ ^ 2) :=
    integral_fintype_prod_volume_eq_prod (fun _ : Fin N => fun x : Euc d => Real.exp (-a * ‖x‖ ^ 2))
  simp_rw [← p4j_exp_eq_prod] at h1
  rw [h1]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ha, finrank_euclideanSpace_fin,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem p4j_integral_gauss {v : ℝ} (hv : 0 < v) : ∫ w : EucConfig d N, p4Gauss d N v w = 1 := by
  have h : ∀ w : EucConfig d N, p4Gauss d N v w =
      p4j_c d N v * Real.exp (-(1 / (2 * v)) * p4j_Phi w) := fun w => by
    rw [p4j_gauss_eq]; congr 2; ring
  simp_rw [h]
  rw [integral_const_mul, p4j_integral_exp (by positivity)]
  unfold p4j_c
  have h2 : Real.pi / (1 / (2 * v)) = 2 * Real.pi * v := by field_simp
  rw [h2, ← Real.rpow_add (by positivity)]
  have : -((N * d : ℕ) : ℝ) / 2 + ((N * d : ℕ) : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero]

theorem p4j_integrable_gauss {v : ℝ} (hv : 0 < v) : Integrable (p4Gauss d N v : EucConfig d N → ℝ) := by
  have h : ∀ w : EucConfig d N, p4Gauss d N v w =
      p4j_c d N v * Real.exp (-(1 / (2 * v)) * p4j_Phi w) := fun w => by
    rw [p4j_gauss_eq]; congr 2; ring
  rw [show (p4Gauss d N v : EucConfig d N → ℝ) = fun w => p4j_c d N v *
    Real.exp (-(1 / (2 * v)) * p4j_Phi w) from funext h]
  exact (p4j_integrable_exp (by positivity)).const_mul _


/-- The Gaussian second moment `∫ G_v Φ`. -/
def p4j_m (d N : ℕ) (v : ℝ) : ℝ := ∫ w : EucConfig d N, p4Gauss d N v w * p4j_Phi w

theorem p4j_integrable_gauss_Phi {v : ℝ} (hv : 0 < v) :
    Integrable (fun w : EucConfig d N => p4Gauss d N v w * p4j_Phi w) := by
  have hb : Integrable (fun w : EucConfig d N => (4 * v * p4j_c d N v) *
      Real.exp (-(1 / (4 * v)) * p4j_Phi w)) :=
    (p4j_integrable_exp (by positivity)).const_mul _
  refine hb.mono' (((p4j_gauss_continuous v).mul p4j_Phi_continuous).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  have hP := p4j_Phi_nonneg w
  have hc := p4j_c_pos (d := d) (N := N) hv
  rw [Real.norm_of_nonneg (mul_nonneg (p4j_gauss_pos hv w).le hP), p4j_gauss_eq]
  have ht : p4j_Phi w / (4 * v) ≤ Real.exp (p4j_Phi w / (4 * v)) := by
    have := Real.add_one_le_exp (p4j_Phi w / (4 * v)); linarith
  have h4 : p4j_Phi w ≤ 4 * v * Real.exp (p4j_Phi w / (4 * v)) := by
    have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 4 * v)
    have e : 4 * v * (p4j_Phi w / (4 * v)) = p4j_Phi w := by field_simp
    linarith
  calc p4j_c d N v * Real.exp (-(p4j_Phi w) / (2 * v)) * p4j_Phi w
      ≤ p4j_c d N v * Real.exp (-(p4j_Phi w) / (2 * v)) * (4 * v * Real.exp (p4j_Phi w / (4 * v))) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (4 * v * p4j_c d N v) * Real.exp (-(1 / (4 * v)) * p4j_Phi w) := by
        have : Real.exp (-(p4j_Phi w) / (2 * v)) * Real.exp (p4j_Phi w / (4 * v)) =
            Real.exp (-(1 / (4 * v)) * p4j_Phi w) := by
          rw [← Real.exp_add]; congr 1; field_simp; ring
        calc p4j_c d N v * Real.exp (-(p4j_Phi w) / (2 * v)) * (4 * v * Real.exp (p4j_Phi w / (4 * v)))
            = (4 * v * p4j_c d N v) * (Real.exp (-(p4j_Phi w) / (2 * v)) *
                Real.exp (p4j_Phi w / (4 * v))) := by ring
          _ = _ := by rw [this]

theorem p4j_m_scaling {v : ℝ} (hv : 0 < v) : p4j_m d N v = v * p4j_m d N 1 := by
  set R : ℝ := Real.sqrt v with hR
  have hR0 : 0 < R := Real.sqrt_pos.2 hv
  have hRR : R ^ 2 = v := Real.sq_sqrt hv.le
  have key : ∀ z : EucConfig d N, p4Gauss d N v (R • z) =
      (p4j_c d N v / p4j_c d N 1) * p4Gauss d N 1 z := by
    intro z
    have hc1 := p4j_c_pos (d := d) (N := N) one_pos
    rw [p4j_gauss_eq, p4j_gauss_eq, p4j_Phi_smul, hRR]
    have : -(v * p4j_Phi z) / (2 * v) = -(p4j_Phi z) / (2 * 1) := by field_simp
    rw [this]
    field_simp
  have hA := Measure.integral_comp_smul (volume : Measure (EucConfig d N))
    (fun w : EucConfig d N => p4Gauss d N v w) R
  have hB := Measure.integral_comp_smul (volume : Measure (EucConfig d N))
    (fun w : EucConfig d N => p4Gauss d N v w * p4j_Phi w) R
  simp only [key] at hA
  rw [integral_const_mul, p4j_integral_gauss one_pos, p4j_integral_gauss hv] at hA
  have hB' : ∫ z : EucConfig d N, p4Gauss d N v (R • z) * p4j_Phi (R • z) =
      (p4j_c d N v / p4j_c d N 1) * (v * p4j_m d N 1) := by
    have : ∀ z : EucConfig d N, p4Gauss d N v (R • z) * p4j_Phi (R • z) =
        ((p4j_c d N v / p4j_c d N 1) * v) * (p4Gauss d N 1 z * p4j_Phi z) := fun z => by
      rw [key, p4j_Phi_smul, hRR]; ring
    simp_rw [this]
    rw [integral_const_mul]
    unfold p4j_m
    ring
  rw [hB'] at hB
  have hpos : 0 < p4j_c d N v / p4j_c d N 1 := div_pos (p4j_c_pos hv) (p4j_c_pos one_pos)
  have hA' : |(R ^ Module.finrank ℝ (EucConfig d N))⁻¹| = p4j_c d N v / p4j_c d N 1 := by
    simpa using hA.symm
  rw [hA', smul_eq_mul] at hB
  unfold p4j_m
  have := mul_left_cancel₀ hpos.ne' hB
  unfold p4j_m at this
  linarith


/-! ### Potential estimates -/

theorem p4j_innerL_apply (y w : EucConfig d N) : p4InnerL y w = ∑ i, inner ℝ (y i) (w i) := by
  simp [p4InnerL, ContinuousLinearMap.sum_apply]

theorem p4j_innerL_bound (y w : EucConfig d N) : |p4InnerL y w| ≤ N * ‖y‖ * ‖w‖ := by
  rw [p4j_innerL_apply]
  calc |∑ i, inner ℝ (y i) (w i)| ≤ ∑ i, |inner ℝ (y i) (w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ‖y‖ * ‖w‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |inner ℝ (y i) (w i)| ≤ ‖y i‖ * ‖w i‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖y‖ * ‖w‖ := mul_le_mul (norm_le_pi_norm y i) (norm_le_pi_norm w i) (norm_nonneg _)
            (norm_nonneg _)
    _ = N * ‖y‖ * ‖w‖ := by simp [mul_assoc]

theorem p4j_innerL_sub (y y' w : EucConfig d N) : p4InnerL (y - y') w = p4InnerL y w - p4InnerL y' w := by
  rw [p4j_innerL_apply, p4j_innerL_apply, p4j_innerL_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [inner_sub_left]

theorem p4j_innerL_continuous (w : EucConfig d N) : Continuous fun y : EucConfig d N => p4InnerL y w := by
  simp_rw [p4j_innerL_apply]
  fun_prop

theorem p4j_descent {V : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ}
    (hT : 0 ≤ T) (hV : P4PotHyp V b T) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x w : EucConfig d N,
      |V 0 (x + w) - V 0 x + p4InnerL (b 0 x) w| ≤ κ * p4j_Phi w := by
  obtain ⟨K, hK⟩ := hV.lip
  have hK0 : LipschitzWith K (b 0) := hK 0 ⟨le_rfl, hT⟩
  refine ⟨N * K, by positivity, fun x w => ?_⟩
  set g : ℝ → ℝ := fun s => V 0 (x + s • w) with hg
  set g' : ℝ → ℝ := fun s => -(p4InnerL (b 0 (x + s • w)) w) with hg'
  have hd : ∀ s : ℝ, HasDerivAt g (g' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add x
    have := (hV.grad 0 (x + s • w)).comp_hasDerivAt s h1
    simp only [hg, hg']
    exact this
  have hc : Continuous g' := by
    have h1 : Continuous fun s : ℝ => b 0 (x + s • w) :=
      hV.cont_b.comp (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const)))
    simp only [hg']
    exact ((p4j_innerL_continuous w).comp h1).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  have hg1 : g 1 = V 0 (x + w) := by simp [hg]
  have hg0 : g 0 = V 0 x := by simp [hg]
  have hdiff : V 0 (x + w) - V 0 x + p4InnerL (b 0 x) w =
      ∫ s in (0 : ℝ)..1, (g' s + p4InnerL (b 0 x) w) := by
    rw [intervalIntegral.integral_add (hc.intervalIntegrable 0 1) intervalIntegrable_const, hftc, hg1, hg0]
    simp
  rw [hdiff]
  have hbd : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖g' s + p4InnerL (b 0 x) w‖ ≤ N * K * ‖w‖ ^ 2 * s := by
    intro s hs
    have e : g' s + p4InnerL (b 0 x) w = p4InnerL (b 0 x - b 0 (x + s • w)) w := by
      rw [p4j_innerL_sub]; simp only [hg']; ring
    rw [e, Real.norm_eq_abs]
    refine (p4j_innerL_bound _ _).trans ?_
    have hl : ‖b 0 x - b 0 (x + s • w)‖ ≤ K * (s * ‖w‖) := by
      have := hK0.dist_le_mul x (x + s • w)
      rw [dist_eq_norm, dist_eq_norm] at this
      have e2 : ‖x - (x + s • w)‖ = s * ‖w‖ := by
        rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
      rwa [e2] at this
    calc (N : ℝ) * ‖b 0 x - b 0 (x + s • w)‖ * ‖w‖ ≤ N * (K * (s * ‖w‖)) * ‖w‖ := by gcongr
      _ = N * K * ‖w‖ ^ 2 * s := by ring
  have hint : IntervalIntegrable (fun s : ℝ => (N : ℝ) * K * ‖w‖ ^ 2 * s) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have h1 := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hbd) hint
  have h2 : ∫ s in (0 : ℝ)..1, (N : ℝ) * K * ‖w‖ ^ 2 * s = N * K * ‖w‖ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [h2] at h1
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  have := p4j_norm_sq_le_Phi w
  have hNK : 0 ≤ (N : ℝ) * K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hNK]

theorem p4j_quad_growth {V : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ}
    (hT : 0 ≤ T) (hV : P4PotHyp V b T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |V 0 x| ≤ C * (1 + p4j_Phi x) := by
  obtain ⟨κ, hκ, hdesc⟩ := p4j_descent hT hV
  set B : ℝ := N * ‖b 0 0‖ with hB
  refine ⟨|V 0 0| + κ + B, by positivity, fun x => ?_⟩
  have h := hdesc 0 x
  rw [zero_add] at h
  have hI : |p4InnerL (b 0 0) x| ≤ B * (1 + p4j_Phi x) := by
    refine (p4j_innerL_bound _ _).trans ?_
    have h1 : ‖x‖ ≤ 1 + p4j_Phi x := by
      have := p4j_norm_sq_le_Phi x
      nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
    calc (N : ℝ) * ‖b 0 0‖ * ‖x‖ ≤ N * ‖b 0 0‖ * (1 + p4j_Phi x) := by gcongr
      _ = B * (1 + p4j_Phi x) := by rw [hB]
  have hP := p4j_Phi_nonneg x
  have h2 : |V 0 x - V 0 0| ≤ |V 0 x - V 0 0 + p4InnerL (b 0 0) x| + |p4InnerL (b 0 0) x| := by
    have := abs_sub (V 0 x - V 0 0 + p4InnerL (b 0 0) x) (p4InnerL (b 0 0) x)
    simpa using this
  have h3 : |V 0 x| ≤ |V 0 0| + |V 0 x - V 0 0| := by
    have := abs_add_le (V 0 0) (V 0 x - V 0 0)
    simpa using this
  have hA : 0 ≤ |V 0 0| := abs_nonneg _
  nlinarith [mul_nonneg hA hP, mul_nonneg hκ hP]

theorem p4j_symm_bound {V : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ}
    (hT : 0 ≤ T) (hV : P4PotHyp V b T) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x w : EucConfig d N, V 0 (x + w) + V 0 (x - w) ≤ 2 * V 0 x + 2 * κ * p4j_Phi w := by
  obtain ⟨κ, hκ, hdesc⟩ := p4j_descent hT hV
  refine ⟨κ, hκ, fun x w => ?_⟩
  have h1 := (abs_le.1 (hdesc x w)).2
  have h2 := (abs_le.1 (hdesc x (-w))).2
  have e : x + -w = x - w := by abel
  rw [map_neg, p4j_Phi_neg, e] at h2
  linarith


/-! ### Gibbs weights with a Gaussian majorant -/

/-- A positive measurable weight with a Gaussian majorant. -/
structure P4JWeight (G : EucConfig d N → ℝ) : Prop where
  meas : Measurable G
  pos : ∀ x, 0 < G x
  gauss : ∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ x, G x ≤ M * Real.exp (-(c * ‖x‖ ^ 2))

theorem p4j_weight_of_conf {θ : ℝ} (hθ : 0 < θ) {V0 : EucConfig d N → ℝ} (hV0 : Continuous V0)
    {c C : ℝ} (hc : 0 < c) (hconf : ∀ x, c * ‖x‖ ^ 2 - C ≤ V0 x) :
    P4JWeight (p4GibbsOf θ V0) where
  meas := p4g_gibbsOf_meas θ hV0.measurable
  pos := fun _ => Real.exp_pos _
  gauss := ⟨Real.exp (θ⁻¹ * C), θ⁻¹ * c, Real.exp_pos _, by positivity, fun x => by
    unfold p4GibbsOf
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h := hconf x
    have hi : 0 < θ⁻¹ := inv_pos.2 hθ
    nlinarith⟩

theorem P4JWeight.Z_lt_top {G : EucConfig d N → ℝ} (hG : P4JWeight G) : gibbsPartitionW G < ⊤ := by
  obtain ⟨M, c, hM, hc, hb⟩ := hG.gauss
  unfold gibbsPartitionW
  have hint : Integrable (fun Ξ : EucConfig d N => M * Real.exp (-(c * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := c) hc).const_mul _
  exact lt_of_le_of_lt (lintegral_mono fun Ξ => ENNReal.ofReal_le_ofReal (hb Ξ)) hint.lintegral_lt_top

theorem P4JWeight.Z_pos {G : EucConfig d N → ℝ} (hG : P4JWeight G) : 0 < gibbsPartitionW G :=
  p4g_lintegral_pos_of_pos hG.meas hG.pos

theorem P4JWeight.ref_prob {G : EucConfig d N → ℝ} (hG : P4JWeight G) :
    IsProbabilityMeasure (gibbsRefW G) :=
  p4g_ref_prob G hG.meas hG.Z_pos.ne' hG.Z_lt_top.ne

theorem p4j_klDiv_ne_top_of_entropy {G : EucConfig d N → ℝ} {μ : Measure (EucConfig d N)}
    (hfin : gibbsEntropyW G μ < ⊤) : klDiv μ (gibbsRefW G) ≠ ⊤ := by
  intro h
  have : gibbsEntropyW G μ = ⊤ := by
    unfold gibbsEntropyW relEntropy
    rw [h]
    exact EReal.top_sub_coe _
  rw [this] at hfin
  exact lt_irrefl _ hfin

theorem p4j_moment {G : EucConfig d N → ℝ} (hG : P4JWeight G) (μ : Measure (EucConfig d N))
    [IsProbabilityMeasure μ] (hKL : klDiv μ (gibbsRefW G) ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤ := by
  obtain ⟨M, c0, hM, hc0, hb⟩ := hG.gauss
  haveI hQ := hG.ref_prob
  have hZ0 := hG.Z_pos.ne'
  have hZt := hG.Z_lt_top.ne
  set c : ℝ := c0 / 2 with hc
  have hcpos : 0 < c := by positivity
  set F : EucConfig d N → ℝ := fun x => c * ‖x‖ ^ 2 with hF
  have hFm : Measurable F := (measurable_norm.pow_const 2).const_mul _
  have hF0 : ∀ x, 0 ≤ F x := fun x => by positivity
  have hJ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) * ENNReal.ofReal (G x) < ⊤ := by
    have hint : Integrable (fun Ξ : EucConfig d N => M * Real.exp (-(c * ‖Ξ‖ ^ 2))) volume :=
      (p4g_integrable_gauss_pi (c := c) hcpos).const_mul _
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint.lintegral_lt_top
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp (F x) * G x ≤ Real.exp (F x) * (M * Real.exp (-(c0 * ‖x‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hb x) (Real.exp_pos _).le
      _ = M * Real.exp (-(c * ‖x‖ ^ 2)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          simp only [hF, hc]; ring
  set J := ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) * ENNReal.ofReal (G x) with hJdef
  have hQint : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂(gibbsRefW G) =
      (gibbsPartitionW G)⁻¹ * J := by
    unfold gibbsRefW
    rw [lintegral_smul_measure, smul_eq_mul,
      lintegral_withDensity_eq_lintegral_mul _ hG.meas.ennreal_ofReal
        (show Measurable fun a => ENNReal.ofReal (Real.exp (F a)) from
          (Real.measurable_exp.comp hFm).ennreal_ofReal)]
    congr 1
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
  have hfinJ : (gibbsPartitionW G)⁻¹ * J ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ0) hJ.ne
  set q : ℝ := ((gibbsPartitionW G)⁻¹ * J).toReal with hq
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hK : 0 ≤ Real.log (1 + q) := Real.log_nonneg (by linarith)
  have hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (F x)) ∂(gibbsRefW G) ≤
      ENNReal.ofReal (Real.exp (Real.log (1 + q))) := by
    rw [hQint, Real.exp_log (by linarith), ← ENNReal.ofReal_toReal hfinJ]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hdv := dv_lintegral (gibbsRefW G) μ hKL hFm hF0 hK hZ
  have hlt : ∫⁻ x, ENNReal.ofReal (F x) ∂μ < ⊤ :=
    lt_of_le_of_lt hdv (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hKL, ENNReal.ofReal_lt_top⟩)
  have hrew : ∀ x : EucConfig d N, ENNReal.ofReal (‖x‖ ^ 2) =
      ENNReal.ofReal (1 / c) * ENNReal.ofReal (F x) := fun x => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hF]
    field_simp
  simp_rw [hrew]
  rw [lintegral_const_mul _ hFm.ennreal_ofReal]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt


/-! ### Densities of measures of finite entropy -/

theorem p4j_ref_eq {G : EucConfig d N → ℝ} (hG : P4JWeight G) :
    gibbsRefW G = (volume : Measure (EucConfig d N)).withDensity
      (fun x => (gibbsPartitionW G)⁻¹ * ENNReal.ofReal (G x)) := by
  unfold gibbsRefW
  have := withDensity_smul (μ := (volume : Measure (EucConfig d N))) (gibbsPartitionW G)⁻¹
    hG.meas.ennreal_ofReal
  rw [← this]
  rfl

theorem p4j_density_eq_ref {G : EucConfig d N → ℝ} (hG : P4JWeight G) {ρ : EucConfig d N → ℝ}
    (hρ : Measurable ρ) :
    (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)) =
      (gibbsRefW G).withDensity
        (fun x => ENNReal.ofReal (ρ x) * (gibbsPartitionW G * (ENNReal.ofReal (G x))⁻¹)) := by
  have hZ0 := hG.Z_pos.ne'
  have hZt := hG.Z_lt_top.ne
  have hwm := hG.meas.ennreal_ofReal
  have hfm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ
  have key : (volume : Measure (EucConfig d N)).withDensity
      (fun x => ((gibbsPartitionW G)⁻¹ * ENNReal.ofReal (G x)) *
        (ENNReal.ofReal (ρ x) * (gibbsPartitionW G * (ENNReal.ofReal (G x))⁻¹))) =
      ((volume : Measure (EucConfig d N)).withDensity
        (fun x => (gibbsPartitionW G)⁻¹ * ENNReal.ofReal (G x))).withDensity
        (fun x => ENNReal.ofReal (ρ x) * (gibbsPartitionW G * (ENNReal.ofReal (G x))⁻¹)) :=
    withDensity_mul _ (measurable_const.mul hwm) (hfm.mul (measurable_const.mul hwm.inv))
  rw [p4j_ref_eq hG, ← key]
  congr 1
  funext x
  have h1 : ENNReal.ofReal (G x) ≠ 0 := (ENNReal.ofReal_pos.2 (hG.pos x)).ne'
  have h2 : ENNReal.ofReal (G x) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ENNReal.ofReal (ρ x) = ENNReal.ofReal (ρ x) * (((gibbsPartitionW G)⁻¹ * gibbsPartitionW G) *
        (ENNReal.ofReal (G x) * (ENNReal.ofReal (G x))⁻¹)) := by
        rw [ENNReal.inv_mul_cancel hZ0 hZt, ENNReal.mul_inv_cancel h1 h2]; simp
    _ = _ := by ring

theorem p4j_llr_density {θ : ℝ} {W : EucConfig d N → ℝ} (hG : P4JWeight (p4GibbsOf θ W))
    {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    ∀ᵐ x ∂((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))),
      llr ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)))
        (gibbsRefW (p4GibbsOf θ W)) x =
      Real.log (ρ x) + Real.log (gibbsPartitionW (p4GibbsOf θ W)).toReal + θ⁻¹ * W x := by
  set G := p4GibbsOf θ W with hGdef
  have hZ0 := hG.Z_pos.ne'
  have hZt := hG.Z_lt_top.ne
  have hac : (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)) ≪
      gibbsRefW G := by
    rw [p4j_density_eq_ref hG hρ]
    exact withDensity_absolutelyContinuous _ _
  haveI : IsProbabilityMeasure (gibbsRefW G) := hG.ref_prob
  have hwm := hG.meas.ennreal_ofReal
  have hrn0 := Measure.rnDeriv_withDensity (gibbsRefW G)
    (f := fun x => ENNReal.ofReal (ρ x) * (gibbsPartitionW G * (ENNReal.ofReal (G x))⁻¹))
    ((ENNReal.measurable_ofReal.comp hρ).mul (measurable_const.mul hwm.inv))
  rw [← p4j_density_eq_ref hG hρ] at hrn0
  have hrn' := hac.ae_le hrn0
  have hpos : ∀ᵐ x ∂((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))),
      0 < ρ x := by
    rw [ae_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ)]
    refine Eventually.of_forall fun x hx => ?_
    rcases (hρ0 x).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) hx
  filter_upwards [hrn', hpos] with x hx hpx
  unfold llr
  rw [hx]
  have hw : ENNReal.ofReal (G x) = ENNReal.ofReal (Real.exp (-(θ⁻¹) * W x)) := rfl
  have e1 : (ENNReal.ofReal (ρ x) * (gibbsPartitionW G * (ENNReal.ofReal (G x))⁻¹)).toReal =
      ρ x * ((gibbsPartitionW G).toReal * (Real.exp (-(θ⁻¹) * W x))⁻¹) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, hw, ENNReal.toReal_ofReal (hρ0 x),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [e1]
  have hZr : 0 < (gibbsPartitionW G).toReal := ENNReal.toReal_pos hZ0 hZt
  rw [Real.log_mul hpx.ne' (mul_pos hZr (inv_pos.2 (Real.exp_pos _))).ne', Real.log_mul hZr.ne'
    (inv_pos.2 (Real.exp_pos _)).ne', Real.log_inv, Real.log_exp]
  ring


theorem p4j_integrable_of_lintegral {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (h : ∫⁻ x, ENNReal.ofReal (ρ x) = 1) : Integrable ρ (volume : Measure (EucConfig d N)) := by
  refine ⟨hρ.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hρ0), h]
  exact ENNReal.one_lt_top

theorem p4j_integral_of_lintegral {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (h : ∫⁻ x, ENNReal.ofReal (ρ x) = 1) : ∫ x, ρ x = 1 := by
  have := ofReal_integral_eq_lintegral_ofReal (p4j_integrable_of_lintegral hρ hρ0 h) (ae_of_all _ hρ0)
  rw [h] at this
  have h0 : 0 ≤ ∫ x, ρ x := integral_nonneg hρ0
  rwa [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one] at this

theorem p4j_integral_dMeas {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : EucConfig d N → ℝ) :
    ∫ y, f y ∂((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))) =
      ∫ x, ρ x * f x := by
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 y)]

theorem p4j_integrable_dMeas_iff {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : EucConfig d N → ℝ) :
    Integrable f ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))) ↔
      Integrable (fun x => ρ x * f x) (volume : Measure (EucConfig d N)) := by
  rw [integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 y)]

theorem p4j_density {θ : ℝ} {W : EucConfig d N → ℝ} (hG : P4JWeight (p4GibbsOf θ W))
    {μ : Measure (EucConfig d N)} [IsProbabilityMeasure μ]
    (hKL : klDiv μ (gibbsRefW (p4GibbsOf θ W)) ≠ ⊤) :
    ∃ ρ : EucConfig d N → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      μ = (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)) ∧
      ∫⁻ x, ENNReal.ofReal (ρ x) = 1 ∧
      Integrable (fun x => ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) ∧
      gibbsEntropyW (p4GibbsOf θ W) μ =
        ((∫ x, (ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) : ℝ) : EReal) := by
  set G := p4GibbsOf θ W with hGdef
  have hZ0 := hG.Z_pos.ne'
  have hZt := hG.Z_lt_top.ne
  haveI : IsProbabilityMeasure (gibbsRefW G) := hG.ref_prob
  have hac : μ ≪ gibbsRefW G := by
    by_contra hna; exact hKL (klDiv_of_not_ac hna)
  have hint : Integrable (llr μ (gibbsRefW G)) μ := by
    by_contra hni; exact hKL (klDiv_of_not_integrable hni)
  have hrefac : gibbsRefW G ≪ (volume : Measure (EucConfig d N)) := p4g_ref_ac G
  have hac2 : μ ≪ (volume : Measure (EucConfig d N)) := hac.trans hrefac
  set ρ : EucConfig d N → ℝ := fun x => (μ.rnDeriv volume x).toReal with hρdef
  have hρ : Measurable ρ := (Measure.measurable_rnDeriv μ volume).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ENNReal.toReal_nonneg
  have hμeq : μ = (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x)) := by
    have h1 : μ = (volume : Measure (EucConfig d N)).withDensity (μ.rnDeriv volume) :=
      (Measure.withDensity_rnDeriv_eq μ volume hac2).symm
    conv_lhs => rw [h1]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ volume] with x hx
    simp only [hρdef]
    rw [ENNReal.ofReal_toReal hx.ne]
  have hρ1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1 := by
    have h1 : ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))) univ =
        ∫⁻ x, ENNReal.ofReal (ρ x) := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← h1, ← hμeq, measure_univ]
  have hρi := p4j_integrable_of_lintegral hρ hρ0 hρ1
  have hllr := p4j_llr_density hG hρ hρ0
  set Lz : ℝ := Real.log (gibbsPartitionW G).toReal with hLz
  have hint' := hint
  rw [hμeq] at hint'
  have hℓ : Integrable (fun x => Real.log (ρ x) + Lz + θ⁻¹ * W x)
      ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    hint'.congr (by filter_upwards [hllr] with x hx using hx)
  have hℓ' := (p4j_integrable_dMeas_iff hρ hρ0 _).1 hℓ
  have hsm : ∀ x, ρ x * (Real.log (ρ x) + Lz + θ⁻¹ * W x) =
      (ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) + Lz * ρ x := fun x => by ring
  have hΦ : Integrable (fun x => ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) volume := by
    have : Integrable (fun x => ((ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) + Lz * ρ x) - Lz * ρ x)
        volume := Integrable.sub (hℓ'.congr (ae_of_all _ hsm)) (hρi.const_mul Lz)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; ring
  refine ⟨ρ, hρ, hρ0, hμeq, hρ1, hΦ, ?_⟩
  haveI hμP : IsProbabilityMeasure μ := inferInstance
  rw [p4g_entropy_eq hG.meas hZ0 hZt μ hKL]
  refine congrArg (fun r : ℝ => (r : EReal)) ?_
  rw [hμeq, integral_congr_ae hllr, p4j_integral_dMeas hρ hρ0]
  have e : ∫ x, ρ x * (Real.log (ρ x) + Lz + θ⁻¹ * W x) =
      ∫ x, ((ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * W x)) + Lz * ρ x) :=
    integral_congr_ae (ae_of_all _ hsm)
  rw [e, integral_add hΦ (hρi.const_mul Lz), integral_const_mul, p4j_integral_of_lintegral hρ hρ0 hρ1]
  ring


/-! ### The mollification as a convolution -/

section Mol

variable {v : ℝ}

theorem p4j_gauss_sub_comm (v : ℝ) (x y : EucConfig d N) :
    p4Gauss d N v (x - y) = p4Gauss d N v (y - x) := by
  rw [← neg_sub, p4j_gauss_neg]

theorem p4j_integrable_gauss_sub_x (hv : 0 < v) (y : EucConfig d N) :
    Integrable (fun x : EucConfig d N => p4Gauss d N v (x - y)) :=
  (p4j_integrable_gauss hv).comp_sub_right y

theorem p4j_integral_gauss_sub_x (hv : 0 < v) (y : EucConfig d N) :
    ∫ x : EucConfig d N, p4Gauss d N v (x - y) = 1 := by
  rw [integral_sub_right_eq_self (fun w : EucConfig d N => p4Gauss d N v w) y, p4j_integral_gauss hv]

theorem p4j_integrable_gauss_sub_y (hv : 0 < v) (x : EucConfig d N) :
    Integrable (fun y : EucConfig d N => p4Gauss d N v (x - y)) := by
  simp_rw [p4j_gauss_sub_comm v x]
  exact p4j_integrable_gauss_sub_x hv x

theorem p4j_integral_gauss_sub_y (hv : 0 < v) (x : EucConfig d N) :
    ∫ y : EucConfig d N, p4Gauss d N v (x - y) = 1 := by
  simp_rw [p4j_gauss_sub_comm v x]
  exact p4j_integral_gauss_sub_x hv x

theorem p4j_gauss_sub_continuous (v : ℝ) :
    Continuous fun p : EucConfig d N × EucConfig d N => p4Gauss d N v (p.1 - p.2) :=
  (p4j_gauss_continuous v).comp (continuous_fst.sub continuous_snd)

theorem p4j_mol_eq (hv : 0 < v) {ρ : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (x : EucConfig d N) :
    p4Mol v ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))) x =
      ∫ y, p4Gauss d N v (x - y) * ρ y := by
  unfold p4Mol
  rw [p4j_integral_dMeas hρ hρ0 (fun y => p4Gauss d N v (x - y))]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring

theorem p4j_mol_continuous (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    Continuous (p4Mol v μ) := by
  unfold p4Mol
  refine continuous_of_dominated (bound := fun _ => p4j_c d N v) (fun x => ?_) (fun x => ?_)
    (integrable_const _) (ae_of_all _ fun y => ?_)
  · exact ((p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine ae_of_all _ fun y => ?_
    rw [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]
    exact p4j_gauss_le hv _
  · exact (p4j_gauss_continuous v).comp (continuous_id.sub continuous_const)

theorem p4j_mol_le (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (x : EucConfig d N) : p4Mol v μ x ≤ p4j_c d N v := by
  unfold p4Mol
  calc ∫ y, p4Gauss d N v (x - y) ∂μ ≤ ∫ _y, p4j_c d N v ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun y => (p4j_gauss_pos hv _).le) (integrable_const _)
          (ae_of_all _ fun y => p4j_gauss_le hv _)
    _ = p4j_c d N v := by simp

/-- Lower bound of the mollification. -/
theorem p4j_mol_lower (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) (x : EucConfig d N) :
    p4j_c d N v * Real.exp (-(p4j_Phi x + ∫ y, p4j_Phi y ∂μ) / v) ≤ p4Mol v μ x := by
  set m₂ : ℝ := ∫ y, p4j_Phi y ∂μ with hm₂
  have hcv := p4j_c_pos (d := d) (N := N) hv
  -- pointwise lower bound of the kernel
  have hker : ∀ y : EucConfig d N, p4j_c d N v * Real.exp (-(p4j_Phi x + p4j_Phi y) / v) ≤
      p4Gauss d N v (x - y) := by
    intro y
    rw [p4j_gauss_eq]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hcv.le
    have h := p4j_Phi_add_le x (-y)
    rw [p4j_Phi_neg, ← sub_eq_add_neg] at h
    have h2 : p4j_Phi (x - y) / (2 * v) ≤ (p4j_Phi x + p4j_Phi y) / v := by
      rw [div_le_div_iff₀ (by positivity) hv]
      nlinarith [p4j_Phi_nonneg (x - y)]
    have : -(p4j_Phi (x - y)) / (2 * v) = -(p4j_Phi (x - y) / (2 * v)) := by ring
    rw [this, neg_div]
    linarith
  -- Jensen for the exponential
  have hfi : Integrable (fun y : EucConfig d N => -(p4j_Phi y) / v) μ := by
    simpa [neg_div] using (hΦ.div_const v).neg
  have hexp : Integrable (fun y : EucConfig d N => Real.exp (-(p4j_Phi y) / v)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (Real.measurable_exp.comp ((p4j_Phi_continuous.measurable.neg).div_const v)).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have := p4j_Phi_nonneg y
    have : 0 ≤ p4j_Phi y / v := by positivity
    rw [neg_div]; linarith
  have hJ := convexOn_exp.map_integral_le (μ := μ) (f := fun y : EucConfig d N => -(p4j_Phi y) / v)
    Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => mem_univ _) hfi hexp
  have hint : ∫ y, -(p4j_Phi y) / v ∂μ = -m₂ / v := by
    simp only [neg_div]
    rw [integral_neg, integral_div]
  rw [hint] at hJ
  unfold p4Mol
  have hI1 : Integrable (fun y : EucConfig d N => p4Gauss d N v (x - y)) μ :=
    Integrable.of_bound ((p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (p4j_c d N v) (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]; exact p4j_gauss_le hv _)
  have hlow : ∫ y, p4j_c d N v * Real.exp (-(p4j_Phi x) / v) * Real.exp (-(p4j_Phi y) / v) ∂μ ≤
      ∫ y, p4Gauss d N v (x - y) ∂μ := by
    refine integral_mono (hexp.const_mul _) hI1 fun y => ?_
    refine (le_of_eq ?_).trans (hker y)
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine le_trans ?_ hlow
  rw [integral_const_mul]
  have e : -(p4j_Phi x + m₂) / v = -(p4j_Phi x) / v + -m₂ / v := by ring
  rw [e, Real.exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left hJ (by positivity)



theorem p4j_transport (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    {h : EucConfig d N → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, ENNReal.ofReal (p4Mol v μ x) * h x =
      ∫⁻ y, (∫⁻ w, ENNReal.ofReal (p4Gauss d N v w) * h (y + w)) ∂μ := by
  have hI1 : ∀ x : EucConfig d N, Integrable (fun y : EucConfig d N => p4Gauss d N v (x - y)) μ :=
    fun x => Integrable.of_bound
      ((p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (p4j_c d N v) (ae_of_all _ fun y => by
        rw [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]; exact p4j_gauss_le hv _)
  have hu : ∀ x, ENNReal.ofReal (p4Mol v μ x) = ∫⁻ y, ENNReal.ofReal (p4Gauss d N v (x - y)) ∂μ :=
    fun x => ofReal_integral_eq_lintegral_ofReal (hI1 x)
      (ae_of_all _ fun y => (p4j_gauss_pos hv _).le)
  have hF : Measurable (Function.uncurry fun (x y : EucConfig d N) =>
      ENNReal.ofReal (p4Gauss d N v (x - y)) * h x) :=
    (ENNReal.measurable_ofReal.comp (p4j_gauss_sub_continuous v).measurable).mul (hh.comp measurable_fst)
  calc ∫⁻ x, ENNReal.ofReal (p4Mol v μ x) * h x
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (p4Gauss d N v (x - y)) * h x ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [hu x]
        exact (lintegral_mul_const (f := fun y => ENNReal.ofReal (p4Gauss d N v (x - y))) (h x)
          (ENNReal.measurable_ofReal.comp
            ((p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)).measurable)).symm
    _ = ∫⁻ y, (∫⁻ x, ENNReal.ofReal (p4Gauss d N v (x - y)) * h x ∂volume) ∂μ :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ y, (∫⁻ w, ENNReal.ofReal (p4Gauss d N v w) * h (y + w)) ∂μ := by
        refine lintegral_congr fun y => ?_
        have := lintegral_add_left_eq_self (μ := (volume : Measure (EucConfig d N)))
          (fun x => ENNReal.ofReal (p4Gauss d N v (x - y)) * h x) y
        rw [← this]
        refine lintegral_congr fun w => ?_
        rw [add_sub_cancel_left]

theorem p4j_lintegral_gauss_poly (hv : 0 < v) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (a + 2 * p4j_Phi w) =
      ENNReal.ofReal (a + 2 * p4j_m d N v) := by
  have hint : Integrable (fun w : EucConfig d N => p4Gauss d N v w * (a + 2 * p4j_Phi w)) := by
    have : (fun w : EucConfig d N => p4Gauss d N v w * (a + 2 * p4j_Phi w)) =
        fun w => a * p4Gauss d N v w + 2 * (p4Gauss d N v w * p4j_Phi w) := by
      funext w; ring
    rw [this]
    exact ((p4j_integrable_gauss hv).const_mul a).add ((p4j_integrable_gauss_Phi hv).const_mul 2)
  have h1 : ∀ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (a + 2 * p4j_Phi w) =
      ENNReal.ofReal (p4Gauss d N v w * (a + 2 * p4j_Phi w)) := fun w =>
    (ENNReal.ofReal_mul (p4j_gauss_pos hv w).le).symm
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by
    have := p4j_Phi_nonneg w
    exact mul_nonneg (p4j_gauss_pos hv w).le (by positivity))]
  congr 1
  have : (fun w : EucConfig d N => p4Gauss d N v w * (a + 2 * p4j_Phi w)) =
      fun w => a * p4Gauss d N v w + 2 * (p4Gauss d N v w * p4j_Phi w) := by
    funext w; ring
  rw [this, integral_add ((p4j_integrable_gauss hv).const_mul a)
    ((p4j_integrable_gauss_Phi hv).const_mul 2), integral_const_mul, integral_const_mul,
    p4j_integral_gauss hv]
  unfold p4j_m
  ring

theorem p4j_mol_moment (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) :
    ∫⁻ x, ENNReal.ofReal (p4Mol v μ x) * ENNReal.ofReal (1 + p4j_Phi x) ≤
      ENNReal.ofReal (1 + 2 * ∫ y, p4j_Phi y ∂μ + 2 * p4j_m d N v) := by
  rw [p4j_transport hv μ (h := fun x => ENNReal.ofReal (1 + p4j_Phi x))
    (ENNReal.measurable_ofReal.comp (measurable_const.add p4j_Phi_continuous.measurable))]
  calc ∫⁻ y, (∫⁻ w, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (1 + p4j_Phi (y + w))) ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal ((1 + 2 * p4j_Phi y) + 2 * p4j_m d N v) ∂μ := by
        refine lintegral_mono fun y => ?_
        rw [← p4j_lintegral_gauss_poly hv (by have := p4j_Phi_nonneg y; positivity)]
        refine lintegral_mono fun w => ?_
        refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
        have := p4j_Phi_add_le y w
        linarith
    _ = ENNReal.ofReal (1 + 2 * ∫ y, p4j_Phi y ∂μ + 2 * p4j_m d N v) := by
        have hm : 0 ≤ p4j_m d N v := integral_nonneg fun w =>
          mul_nonneg (p4j_gauss_pos hv w).le (p4j_Phi_nonneg w)
        have hi : Integrable (fun y : EucConfig d N => (1 + 2 * p4j_Phi y) + 2 * p4j_m d N v) μ :=
          ((integrable_const 1).add (hΦ.const_mul 2)).add (integrable_const _)
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => by
          have := p4j_Phi_nonneg y; positivity)]
        congr 1
        have h2 : Integrable (fun y : EucConfig d N => (1 : ℝ) + 2 * p4j_Phi y) μ :=
          (integrable_const 1).add (hΦ.const_mul 2)
        rw [integral_add h2 (integrable_const _), integral_add (integrable_const (1 : ℝ)) (hΦ.const_mul 2),
          integral_const_mul]
        simp

theorem p4j_lintegral_gauss_lin (hv : 0 < v) {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) :
    ∫⁻ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (a + k * p4j_Phi w) =
      ENNReal.ofReal (a + k * p4j_m d N v) := by
  have hrw : (fun w : EucConfig d N => p4Gauss d N v w * (a + k * p4j_Phi w)) =
      fun w => a * p4Gauss d N v w + k * (p4Gauss d N v w * p4j_Phi w) := by
    funext w; ring
  have hint : Integrable (fun w : EucConfig d N => p4Gauss d N v w * (a + k * p4j_Phi w)) := by
    rw [hrw]
    exact ((p4j_integrable_gauss hv).const_mul a).add ((p4j_integrable_gauss_Phi hv).const_mul k)
  have h1 : ∀ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (a + k * p4j_Phi w) =
      ENNReal.ofReal (p4Gauss d N v w * (a + k * p4j_Phi w)) := fun w =>
    (ENNReal.ofReal_mul (p4j_gauss_pos hv w).le).symm
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w =>
    mul_nonneg (p4j_gauss_pos hv w).le (add_nonneg ha (mul_nonneg hk (p4j_Phi_nonneg w))))]
  congr 1
  rw [hrw, integral_add ((p4j_integrable_gauss hv).const_mul a)
    ((p4j_integrable_gauss_Phi hv).const_mul k), integral_const_mul, integral_const_mul,
    p4j_integral_gauss hv]
  unfold p4j_m
  ring

theorem p4j_pot_inner (hv : 0 < v) {W : EucConfig d N → ℝ} (hW : Continuous W) (hW0 : ∀ x, 0 ≤ W x)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hsym : ∀ x w : EucConfig d N, W (x + w) + W (x - w) ≤ 2 * W x + 2 * κ * p4j_Phi w)
    (y : EucConfig d N) :
    ∫⁻ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (W (y + w)) ≤
      ENNReal.ofReal (W y + κ * p4j_m d N v) := by
  haveI : (volume : Measure (EucConfig d N)).IsNegInvariant := Measure.pi.isNegInvariant _
  set f : EucConfig d N → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (W (y + w)) with hf
  have hfm : Measurable f :=
    (ENNReal.measurable_ofReal.comp (p4j_gauss_measurable v)).mul
      (ENNReal.measurable_ofReal.comp (hW.comp (continuous_const.add continuous_id)).measurable)
  have hneg : ∫⁻ w : EucConfig d N,
      ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (W (y - w)) = ∫⁻ w, f w := by
    rw [← (Measure.measurePreserving_neg (volume : Measure (EucConfig d N))).lintegral_comp hfm]
    refine lintegral_congr fun w => ?_
    simp only [hf, p4j_gauss_neg, sub_eq_add_neg]
  have hf2m : Measurable fun w : EucConfig d N =>
      ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (W (y - w)) :=
    (ENNReal.measurable_ofReal.comp (p4j_gauss_measurable v)).mul
      (ENNReal.measurable_ofReal.comp (hW.comp (continuous_const.sub continuous_id)).measurable)
  have h2 : 2 * ∫⁻ w, f w ≤ 2 * ENNReal.ofReal (W y + κ * p4j_m d N v) := by
    have hr : (2 : ℝ≥0∞) * ENNReal.ofReal (W y + κ * p4j_m d N v) =
        ENNReal.ofReal (2 * W y + 2 * κ * p4j_m d N v) := by
      have : 2 * W y + 2 * κ * p4j_m d N v = 2 * (W y + κ * p4j_m d N v) := by ring
      rw [this, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp
    calc 2 * ∫⁻ w, f w
        = (∫⁻ w, f w) + (∫⁻ w : EucConfig d N,
            ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (W (y - w))) := by rw [hneg, two_mul]
      _ = ∫⁻ w : EucConfig d N, (f w + ENNReal.ofReal (p4Gauss d N v w) * ENNReal.ofReal (W (y - w))) :=
          (lintegral_add_left hfm _).symm
      _ ≤ ∫⁻ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) *
            ENNReal.ofReal (2 * W y + 2 * κ * p4j_Phi w) := by
          refine lintegral_mono fun w => ?_
          simp only [hf]
          rw [← mul_add, ← ENNReal.ofReal_add (hW0 _) (hW0 _)]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hsym y w))
      _ = ENNReal.ofReal (2 * W y + (2 * κ) * p4j_m d N v) :=
          p4j_lintegral_gauss_lin hv (by have := hW0 y; positivity) (by positivity)
      _ = 2 * ENNReal.ofReal (W y + κ * p4j_m d N v) := by rw [hr]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h2

theorem p4j_pot_lintegral (hv : 0 < v) {W : EucConfig d N → ℝ} (hW : Continuous W)
    (hW0 : ∀ x, 0 ≤ W x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsym : ∀ x w : EucConfig d N, W (x + w) + W (x - w) ≤ 2 * W x + 2 * κ * p4j_Phi w)
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    ∫⁻ x, ENNReal.ofReal (p4Mol v μ x) * ENNReal.ofReal (W x) ≤
      ∫⁻ y, ENNReal.ofReal (W y + κ * p4j_m d N v) ∂μ := by
  rw [p4j_transport hv μ (h := fun x => ENNReal.ofReal (W x))
    (ENNReal.measurable_ofReal.comp hW.measurable)]
  exact lintegral_mono fun y => p4j_pot_inner hv hW hW0 hκ hsym y

theorem p4j_mol_lintegral_one (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    ∫⁻ x, ENNReal.ofReal (p4Mol v μ x) = 1 := by
  have h := p4j_transport hv μ (h := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [mul_one] at h
  rw [h]
  have hg : ∫⁻ w : EucConfig d N, ENNReal.ofReal (p4Gauss d N v w) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (p4j_integrable_gauss hv)
      (ae_of_all _ fun w => (p4j_gauss_pos hv w).le), p4j_integral_gauss hv]
    simp
  simp only [hg]
  simp

theorem p4j_mol_integrable (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] :
    Integrable (p4Mol v μ) ∧ ∫ x, p4Mol v μ x = 1 := by
  have hnn : ∀ x, 0 ≤ p4Mol v μ x := fun x =>
    integral_nonneg fun y => (p4j_gauss_pos hv _).le
  have hone := p4j_mol_lintegral_one hv μ
  have hI : Integrable (p4Mol v μ) := by
    refine ⟨(p4j_mol_continuous hv μ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hone]
    exact ENNReal.one_lt_top
  refine ⟨hI, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnn)
  rw [hone] at this
  have h0 : 0 ≤ ∫ x, p4Mol v μ x := integral_nonneg hnn
  rwa [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one] at this

theorem p4j_mol_Phi_integrable (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) :
    Integrable (fun x => p4Mol v μ x * (1 + p4j_Phi x)) := by
  have hnn : ∀ x, 0 ≤ p4Mol v μ x * (1 + p4j_Phi x) := fun x =>
    mul_nonneg (integral_nonneg fun y => (p4j_gauss_pos hv _).le)
      (by have := p4j_Phi_nonneg x; positivity)
  refine ⟨((p4j_mol_continuous hv μ).mul (continuous_const.add p4j_Phi_continuous)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt (p4j_mol_moment hv μ hΦ) ENNReal.ofReal_lt_top)
  refine lintegral_congr fun x => ?_
  exact ENNReal.ofReal_mul (integral_nonneg fun y => (p4j_gauss_pos hv _).le)

theorem p4j_pot_real (hv : 0 < v) {V : EucConfig d N → ℝ} (hVc : Continuous V) {C0 : ℝ}
    (hC0 : ∀ x, 0 ≤ V x + C0) {κ : ℝ} (hκ : 0 ≤ κ)
    (hsym : ∀ x w : EucConfig d N, V (x + w) + V (x - w) ≤ 2 * V x + 2 * κ * p4j_Phi w)
    {C : ℝ} (hq : ∀ x, |V x| ≤ C * (1 + p4j_Phi x))
    (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ] (hVμ : Integrable V μ)
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) :
    Integrable (fun x => p4Mol v μ x * V x) ∧
      ∫ x, p4Mol v μ x * V x ≤ ∫ y, V y ∂μ + κ * p4j_m d N v := by
  have hnn : ∀ x, 0 ≤ p4Mol v μ x := fun x => integral_nonneg fun y => (p4j_gauss_pos hv _).le
  obtain ⟨huI, hu1⟩ := p4j_mol_integrable hv μ
  have hI : Integrable (fun x => p4Mol v μ x * V x) := by
    refine Integrable.mono' ((p4j_mol_Phi_integrable hv μ hΦ).const_mul C)
      ((p4j_mol_continuous hv μ).mul hVc).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hnn x)]
    calc p4Mol v μ x * ‖V x‖ ≤ p4Mol v μ x * (C * (1 + p4j_Phi x)) :=
          mul_le_mul_of_nonneg_left (by simpa using hq x) (hnn x)
      _ = C * (p4Mol v μ x * (1 + p4j_Phi x)) := by ring
  refine ⟨hI, ?_⟩
  set W : EucConfig d N → ℝ := fun x => V x + C0 with hW
  have hWc : Continuous W := hVc.add continuous_const
  have hsymW : ∀ x w : EucConfig d N, W (x + w) + W (x - w) ≤ 2 * W x + 2 * κ * p4j_Phi w := by
    intro x w
    have := hsym x w
    simp only [hW]; linarith
  have hmain := p4j_pot_lintegral hv hWc hC0 hκ hsymW μ
  have hmeas : ∀ x, ENNReal.ofReal (p4Mol v μ x) * ENNReal.ofReal (W x) =
      ENNReal.ofReal (p4Mol v μ x * W x) := fun x => (ENNReal.ofReal_mul (hnn x)).symm
  simp_rw [hmeas] at hmain
  have hWi : Integrable (fun x => p4Mol v μ x * W x) := by
    have : (fun x => p4Mol v μ x * W x) = fun x => p4Mol v μ x * V x + C0 * p4Mol v μ x := by
      funext x; simp only [hW]; ring
    rw [this]; exact hI.add (huI.const_mul C0)
  have hWint : ∫ x, p4Mol v μ x * W x = (∫ x, p4Mol v μ x * V x) + C0 := by
    have : (fun x => p4Mol v μ x * W x) = fun x => p4Mol v μ x * V x + C0 * p4Mol v μ x := by
      funext x; simp only [hW]; ring
    have hA : Integrable (fun x => p4Mol v μ x * V x) := hI
    have hB : Integrable (fun x => C0 * p4Mol v μ x) := huI.const_mul C0
    rw [this, integral_add hA hB, integral_const_mul, hu1]; ring
  have hRi : Integrable (fun y => W y + κ * p4j_m d N v) μ :=
    (hVμ.add (integrable_const _)).add (integrable_const _)
  have hR0 : ∀ y, 0 ≤ W y + κ * p4j_m d N v := fun y => by
    have hm : 0 ≤ p4j_m d N v := integral_nonneg fun w =>
      mul_nonneg (p4j_gauss_pos hv w).le (p4j_Phi_nonneg w)
    have := hC0 y
    simp only [hW]; positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hRi (ae_of_all _ hR0),
    ← ofReal_integral_eq_lintegral_ofReal hWi (ae_of_all _ fun x => mul_nonneg (hnn x)
      (by have := hC0 x; simpa [hW] using this))] at hmain
  have hmain' := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hR0)).1 hmain
  have hRe : ∫ y, (W y + κ * p4j_m d N v) ∂μ = ∫ y, V y ∂μ + C0 + κ * p4j_m d N v := by
    simp only [hW]
    have hA : Integrable (fun y => V y + C0) μ := hVμ.add (integrable_const C0)
    have hB : Integrable (fun _ : EucConfig d N => κ * p4j_m d N v) μ := integrable_const _
    have hC : Integrable (fun _ : EucConfig d N => C0) μ := integrable_const C0
    rw [integral_add hA hB, integral_add hVμ hC]
    simp
  rw [hRe, hWint] at hmain'
  linarith

/-! ### Jensen for the entropy density -/

theorem p4j_tangent {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) : a * Real.log m + a - m ≤ a * Real.log a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp; linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hm ha')
    rw [Real.log_div hm.ne' ha'.ne'] at h
    have e : a * (m / a - 1) = m - a := by field_simp
    have h2 : a * (Real.log m - Real.log a) ≤ m - a := by
      rw [← e]; exact mul_le_mul_of_nonneg_left h ha'.le
    rw [mul_sub] at h2
    linarith

/-- The convolution of a density with the Gaussian kernel. -/
def p4j_conv (v : ℝ) (ρ : EucConfig d N → ℝ) (x : EucConfig d N) : ℝ :=
  ∫ y, p4Gauss d N v (x - y) * ρ y

theorem p4j_conv_prod_integrable (hv : 0 < v) {f : EucConfig d N → ℝ} (hf : Integrable f) :
    Integrable (Function.uncurry fun x y : EucConfig d N => p4Gauss d N v (x - y) * f y)
      ((volume : Measure (EucConfig d N)).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y : EucConfig d N => p4Gauss d N v (x - y) * f y)
      ((volume : Measure (EucConfig d N)).prod volume) :=
    ((p4j_gauss_sub_continuous v).aestronglyMeasurable).mul (hf.aestronglyMeasurable.comp_snd)
  refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · exact (p4j_integrable_gauss_sub_x hv y).mul_const (f y)
  · have e : (fun y => ∫ x, ‖(Function.uncurry fun x y : EucConfig d N =>
        p4Gauss d N v (x - y) * f y) (x, y)‖) = fun y => ‖f y‖ := by
      funext y
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [integral_mul_const]
      have : ∫ x : EucConfig d N, ‖p4Gauss d N v (x - y)‖ = 1 := by
        rw [← p4j_integral_gauss_sub_x hv y]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]
      rw [this, one_mul]
    rw [e]; exact hf.norm

theorem p4j_convolve (hv : 0 < v) {f : EucConfig d N → ℝ} (hf : Integrable f) :
    ∫ x : EucConfig d N, p4j_conv v f x = ∫ y, f y := by
  have hint := p4j_conv_prod_integrable hv hf
  unfold p4j_conv
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [integral_mul_const, p4j_integral_gauss_sub_x hv y, one_mul]

theorem p4j_jensen_pointwise (hv : 0 < v) {ρ : EucConfig d N → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hL : Integrable (fun y => ρ y * Real.log (ρ y)))
    (x : EucConfig d N) (hm0 : 0 < p4j_conv v ρ x) :
    p4j_conv v ρ x * Real.log (p4j_conv v ρ x) ≤
      ∫ y, p4Gauss d N v (x - y) * (ρ y * Real.log (ρ y)) := by
  set m : ℝ := p4j_conv v ρ x with hm
  have hmr : m = ∫ y, p4Gauss d N v (x - y) * ρ y := rfl
  have hpc : Continuous fun y : EucConfig d N => p4Gauss d N v (x - y) :=
    (p4j_gauss_continuous v).comp (continuous_const.sub continuous_id)
  have hbd : ∀ᵐ y : EucConfig d N, ‖p4Gauss d N v (x - y)‖ ≤ p4j_c d N v := ae_of_all _ fun y => by
    rw [Real.norm_of_nonneg (p4j_gauss_pos hv _).le]; exact p4j_gauss_le hv _
  have i1 : Integrable (fun y => p4Gauss d N v (x - y) * ρ y) :=
    hρi.bdd_mul hpc.aestronglyMeasurable hbd
  have i2 : Integrable (fun y => p4Gauss d N v (x - y) * (ρ y * Real.log (ρ y))) :=
    hL.bdd_mul hpc.aestronglyMeasurable hbd
  have i3 := p4j_integrable_gauss_sub_y hv x
  have key : ∀ y, p4Gauss d N v (x - y) * (ρ y * Real.log m + ρ y - m) ≤
      p4Gauss d N v (x - y) * (ρ y * Real.log (ρ y)) :=
    fun y => mul_le_mul_of_nonneg_left (p4j_tangent (hρ0 y) hm0) (p4j_gauss_pos hv _).le
  have hrw : (fun y => p4Gauss d N v (x - y) * (ρ y * Real.log m + ρ y - m)) =
      fun y => Real.log m * (p4Gauss d N v (x - y) * ρ y) + p4Gauss d N v (x - y) * ρ y -
        m * p4Gauss d N v (x - y) := by
    funext y; ring
  have hA : Integrable (fun y => Real.log m * (p4Gauss d N v (x - y) * ρ y) +
      p4Gauss d N v (x - y) * ρ y) := (i1.const_mul _).add i1
  have hB' : Integrable (fun y => m * p4Gauss d N v (x - y)) := i3.const_mul _
  have hC' : Integrable (fun y => Real.log m * (p4Gauss d N v (x - y) * ρ y)) := i1.const_mul _
  have iL : Integrable (fun y => p4Gauss d N v (x - y) * (ρ y * Real.log m + ρ y - m)) := by
    rw [hrw]; exact hA.sub hB'
  have h := integral_mono iL i2 key
  have e : ∫ y, p4Gauss d N v (x - y) * (ρ y * Real.log m + ρ y - m) = m * Real.log m := by
    rw [hrw, integral_sub hA hB', integral_add hC' i1, integral_const_mul, integral_const_mul,
      ← hmr, p4j_integral_gauss_sub_y hv x]
    ring
  rw [e] at h
  exact h

theorem p4j_entropy_term_le (hv : 0 < v) {ρ : EucConfig d N → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ) (hL : Integrable (fun y => ρ y * Real.log (ρ y)))
    (hm0 : ∀ x, 0 < p4j_conv v ρ x)
    (hI : Integrable (fun x => p4j_conv v ρ x * Real.log (p4j_conv v ρ x))) :
    ∫ x, p4j_conv v ρ x * Real.log (p4j_conv v ρ x) ≤ ∫ y, ρ y * Real.log (ρ y) := by
  have hc := p4j_convolve hv hL
  have hint : Integrable (fun x => p4j_conv v (fun y => ρ y * Real.log (ρ y)) x) :=
    (p4j_conv_prod_integrable hv hL).integral_prod_left
  calc ∫ x, p4j_conv v ρ x * Real.log (p4j_conv v ρ x)
      ≤ ∫ x, p4j_conv v (fun y => ρ y * Real.log (ρ y)) x :=
        integral_mono hI hint (fun x => p4j_jensen_pointwise hv hρ0 hρi hL x (hm0 x))
    _ = ∫ y, ρ y * Real.log (ρ y) := hc

theorem p4j_mol_pos (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) (x : EucConfig d N) : 0 < p4Mol v μ x :=
  lt_of_lt_of_le (mul_pos (p4j_c_pos hv) (Real.exp_pos _)) (p4j_mol_lower hv μ hΦ x)

theorem p4j_mol_log_integrable (hv : 0 < v) (μ : Measure (EucConfig d N)) [IsProbabilityMeasure μ]
    (hΦ : Integrable (p4j_Phi : EucConfig d N → ℝ) μ) :
    Integrable (fun x => p4Mol v μ x * Real.log (p4Mol v μ x)) := by
  set M : ℝ := ∫ y, p4j_Phi y ∂μ with hMdef
  have hM : 0 ≤ M := integral_nonneg p4j_Phi_nonneg
  set c : ℝ := p4j_c d N v with hcdef
  have hc : 0 < c := p4j_c_pos hv
  set A : ℝ := |Real.log c| + (1 + M) / v with hA
  have hmeasu := (p4j_mol_continuous hv μ).measurable
  refine Integrable.mono' ((p4j_mol_Phi_integrable hv μ hΦ).const_mul A)
    (hmeasu.mul (Real.measurable_log.comp hmeasu)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hu0 := p4j_mol_pos hv μ hΦ x
  have hup := p4j_mol_le hv μ x
  have hlow := p4j_mol_lower hv μ hΦ x
  have hP := p4j_Phi_nonneg x
  set u : ℝ := p4Mol v μ x with hu
  have h1 : Real.log u ≤ Real.log c := Real.log_le_log hu0 hup
  have h2 : Real.log c + (-(p4j_Phi x + M) / v) ≤ Real.log u := by
    have := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlow
    rwa [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hq0 : 0 ≤ (p4j_Phi x + M) / v := div_nonneg (add_nonneg hP hM) hv.le
  have h3 : |Real.log u| ≤ |Real.log c| + (p4j_Phi x + M) / v := by
    rw [abs_le]
    have e : -(p4j_Phi x + M) / v = -((p4j_Phi x + M) / v) := by ring
    have := neg_abs_le (Real.log c)
    have := le_abs_self (Real.log c)
    constructor <;> linarith
  have h4 : (p4j_Phi x + M) / v ≤ (1 + M) / v * (1 + p4j_Phi x) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hv).2 (by nlinarith [mul_nonneg hM hP])
  have h5 : |Real.log c| ≤ |Real.log c| * (1 + p4j_Phi x) := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log c)) hP]
  have h6 : |Real.log u| ≤ A * (1 + p4j_Phi x) := by
    have : A * (1 + p4j_Phi x) = |Real.log c| * (1 + p4j_Phi x) + (1 + M) / v * (1 + p4j_Phi x) := by
      rw [hA]; ring
    linarith
  rw [norm_mul, Real.norm_of_nonneg hu0.le, Real.norm_eq_abs]
  calc u * |Real.log u| ≤ u * (A * (1 + p4j_Phi x)) := mul_le_mul_of_nonneg_left h6 hu0.le
    _ = A * (u * (1 + p4j_Phi x)) := by ring

theorem p4j_Phi_integrable {μ : Measure (EucConfig d N)} [IsProbabilityMeasure μ]
    (h : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ < ⊤) : Integrable (p4j_Phi : EucConfig d N → ℝ) μ := by
  refine ⟨p4j_Phi_continuous.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ p4j_Phi_nonneg)]
  have hm : Measurable fun x : EucConfig d N => ENNReal.ofReal (‖x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
  calc ∫⁻ x, ENNReal.ofReal (p4j_Phi x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (‖x‖ ^ 2) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
        exact ENNReal.ofReal_le_ofReal (p4j_Phi_le_norm_sq x)
    _ = ENNReal.ofReal (N : ℝ) * ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ := lintegral_const_mul _ hm
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

end Mol

theorem p4_initial_jensen_proof {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {μ₀ : Measure (EucConfig d N)} [IsProbabilityMeasure μ₀]
    (hfin : gibbsEntropyW (p4GibbsOf θ (V 0)) μ₀ < ⊤) :
    ∃ e : ℝ → ℝ, Tendsto e (𝓝[>] 0) (𝓝 0) ∧ ∀ v : ℝ, 0 < v →
      ((p4Free θ (V 0) (p4Mol v μ₀) : ℝ) : EReal) ≤ gibbsEntropyW (p4GibbsOf θ (V 0)) μ₀ + ((e v : ℝ) : EReal) := by
  obtain ⟨c0, C0, hc0, hconf⟩ := hV.conf
  have hconf0 : ∀ x, c0 * ‖x‖ ^ 2 - C0 ≤ V 0 x := fun x => hconf 0 ⟨le_rfl, hT⟩ x
  have hVc : Continuous (V 0) :=
    hV.cont_V.comp (continuous_const.prodMk continuous_id : Continuous fun x : EucConfig d N => ((0 : ℝ), x))
  have hG := p4j_weight_of_conf hθ hVc hc0 hconf0
  have hKL := p4j_klDiv_ne_top_of_entropy hfin
  have hmom := p4j_moment hG μ₀ hKL
  have hΦ := p4j_Phi_integrable hmom
  obtain ⟨ρ, hρ, hρ0, hμeq, hρ1, hρL, hEnt⟩ := p4j_density hG hKL
  obtain ⟨Cq, hCq0, hq⟩ := p4j_quad_growth hT hV
  obtain ⟨κ, hκ, hsym⟩ := p4j_symm_bound hT hV
  have hVμ : Integrable (V 0) μ₀ :=
    Integrable.mono' (((integrable_const (1 : ℝ)).add hΦ).const_mul Cq) hVc.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hq x)
  have hC0 : ∀ x, 0 ≤ V 0 x + C0 := fun x => by
    have := mul_nonneg hc0.le (sq_nonneg ‖x‖)
    have := hconf0 x
    linarith
  have hρi : Integrable ρ := p4j_integrable_of_lintegral hρ hρ0 hρ1
  have hρV : Integrable (fun x => ρ x * V 0 x) := by
    refine (p4j_integrable_dMeas_iff hρ hρ0 (V 0)).1 ?_
    rw [← hμeq]; exact hVμ
  have hL : Integrable (fun y => ρ y * Real.log (ρ y)) := by
    refine (hρL.sub (hρV.const_mul θ⁻¹)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have hint0 : ∫ x, (ρ x * Real.log (ρ x) + θ⁻¹ * (ρ x * V 0 x)) =
      (∫ x, ρ x * Real.log (ρ x)) + θ⁻¹ * ∫ x, ρ x * V 0 x := by
    have hB : Integrable (fun x => θ⁻¹ * (ρ x * V 0 x)) := hρV.const_mul θ⁻¹
    rw [integral_add hL hB, integral_const_mul]
  have hVint : ∫ y, V 0 y ∂μ₀ = ∫ x, ρ x * V 0 x := by
    rw [hμeq]; exact p4j_integral_dMeas hρ hρ0 (V 0)
  refine ⟨fun v => θ⁻¹ * κ * (v * p4j_m d N 1), ?_, fun v hv => ?_⟩
  · have hc : Continuous fun v : ℝ => θ⁻¹ * κ * (v * p4j_m d N 1) := by fun_prop
    have h0 : θ⁻¹ * κ * ((0 : ℝ) * p4j_m d N 1) = 0 := by simp
    have := hc.tendsto 0
    rw [h0] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · have hu : p4Mol v μ₀ = p4j_conv v ρ := by
      funext x
      rw [hμeq]; exact p4j_mol_eq hv hρ hρ0 x
    have hpos : ∀ x, 0 < p4j_conv v ρ x := fun x => hu ▸ p4j_mol_pos hv μ₀ hΦ x
    have hIlog : Integrable (fun x => p4j_conv v ρ x * Real.log (p4j_conv v ρ x)) := by
      rw [← hu]; exact p4j_mol_log_integrable hv μ₀ hΦ
    have hJ := p4j_entropy_term_le hv hρ0 hρi hL hpos hIlog
    obtain ⟨hPI, hPle⟩ := p4j_pot_real hv hVc hC0 hκ hsym hq μ₀ hVμ hΦ
    have hPI' : Integrable (fun x => p4Mol v μ₀ x * V 0 x / θ) := hPI.div_const θ
    have hIlog' : Integrable (fun x => p4Mol v μ₀ x * Real.log (p4Mol v μ₀ x)) := by
      rw [hu]; exact hIlog
    have hfree : p4Free θ (V 0) (p4Mol v μ₀) =
        (∫ x, p4Mol v μ₀ x * Real.log (p4Mol v μ₀ x)) + (∫ x, p4Mol v μ₀ x * V 0 x) / θ := by
      unfold p4Free
      rw [integral_add hIlog' hPI', integral_div]
    have hJ' : ∫ x, p4Mol v μ₀ x * Real.log (p4Mol v μ₀ x) ≤ ∫ y, ρ y * Real.log (ρ y) := by
      rw [hu]; exact hJ
    have hm : p4j_m d N v = v * p4j_m d N 1 := p4j_m_scaling hv
    have hmain : p4Free θ (V 0) (p4Mol v μ₀) ≤
        ((∫ x, ρ x * Real.log (ρ x)) + θ⁻¹ * ∫ x, ρ x * V 0 x) + θ⁻¹ * κ * (v * p4j_m d N 1) := by
      rw [hfree]
      rw [hVint, hm] at hPle
      have : (∫ x, p4Mol v μ₀ x * V 0 x) / θ ≤ θ⁻¹ * ((∫ x, ρ x * V 0 x) + κ * (v * p4j_m d N 1)) := by
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hPle (inv_pos.2 hθ).le
      have e : θ⁻¹ * ((∫ x, ρ x * V 0 x) + κ * (v * p4j_m d N 1)) =
          θ⁻¹ * (∫ x, ρ x * V 0 x) + θ⁻¹ * κ * (v * p4j_m d N 1) := by ring
      linarith
    rw [hEnt, ← EReal.coe_add, EReal.coe_le_coe_iff, hint0]
    exact hmain

example := (@p4_initial_jensen_proof : type_of% @HRS.MP.SelfSimP4.p4_initial_jensen)

end HRS.MP.SelfSimP4Impl
