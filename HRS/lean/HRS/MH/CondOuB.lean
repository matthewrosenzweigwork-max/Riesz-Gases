import HRS.MH.CondOuSpec

/-!
# `HRS.MH.CondOu.conditioned_ou_third_cumulant`: proof (packet (b))

With `c = e^{-λt}√v > 0`, `ν_t = μ ∗ γ` where `μ` is the law of `c|G₀|` and `γ` is a centred Gaussian.
The third central moment of `μ ∗ γ` equals that of `μ` (the Gaussian part is symmetric and independent).
For the half-normal law, `E|G| = 2K`, `E|G|³ = 4K`, `E G² = 1` with `K = (√(2π))⁻¹`, so the third central
moment is `c³ (16K³ - 2K) = 2c³K(8K² - 1) > 0`, because `8K² = 4/π > 1`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.CondOuP

open HRS HRS.Main

/-- The standard Gaussian density constant `(√(2π))⁻¹`. -/
noncomputable def gaussK : ℝ := (Real.sqrt (2 * Real.pi))⁻¹

lemma gaussK_pos : 0 < gaussK := by
  unfold gaussK; positivity

/-- `8 K² = 4/π > 1`. -/
lemma gaussK_eight : 1 < 8 * gaussK ^ 2 := by
  have hpi := Real.pi_lt_d2
  have hpos := Real.pi_pos
  have h2 : gaussK ^ 2 = (2 * Real.pi)⁻¹ := by
    unfold gaussK
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [h2, ← sub_pos]
  have e : 8 * (2 * Real.pi)⁻¹ - 1 = (4 - Real.pi) / Real.pi := by
    field_simp
    ring
  rw [e]
  apply div_pos _ hpos
  norm_num at hpi
  linarith

/-! ### Gaussian integrability -/

lemma gauss_integrable_abs_pow (μ : ℝ) (v : ℝ≥0) (j : ℕ) :
    Integrable (fun y : ℝ => |y| ^ j) (gaussianReal μ v) := by
  have h := (memLp_id_gaussianReal' (μ := μ) (v := v) (j : ℝ≥0∞) (ENNReal.natCast_ne_top j)).integrable_norm_pow'
  simpa [Real.norm_eq_abs] using h

lemma gauss_integrable_pow (μ : ℝ) (v : ℝ≥0) (j : ℕ) :
    Integrable (fun y : ℝ => y ^ j) (gaussianReal μ v) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal μ v))
  · refine (gauss_integrable_abs_pow μ v j).mono'
      (measurable_id.pow_const j).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    simp [norm_pow]

/-- Odd moments of a centred Gaussian vanish. -/
lemma gauss_odd3 (v : ℝ≥0) : ∫ y : ℝ, y ^ 3 ∂(gaussianReal 0 v) = 0 := by
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have h := integral_map (μ := gaussianReal 0 v) (φ := fun x : ℝ => -x) (f := fun y : ℝ => y ^ 3)
    measurable_neg.aemeasurable (measurable_id.pow_const 3).aestronglyMeasurable
  rw [hmap] at h
  have h2 : ∫ x : ℝ, (-x) ^ 3 ∂(gaussianReal 0 v) = - ∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 v) := by
    rw [← integral_neg]
    congr 1
    ext x
    ring
  linarith

/-- The facts about `gaussianLaw σ2` used for the Gaussian summand. -/
lemma gaussianLaw_facts (σ2 : ℝ) :
    IsProbabilityMeasure (gaussianLaw σ2) ∧
      (∀ j : ℕ, Integrable (fun y : ℝ => y ^ j) (gaussianLaw σ2)) ∧
      ∫ y, y ∂(gaussianLaw σ2) = 0 ∧ ∫ y, y ^ 3 ∂(gaussianLaw σ2) = 0 := by
  unfold gaussianLaw
  refine ⟨inferInstance, fun j => gauss_integrable_pow 0 _ j, ?_, gauss_odd3 _⟩
  exact integral_id_gaussianReal

/-! ### Standard Gaussian moments -/

lemma half_int_one : ∫ y in Set.Ioi (0 : ℝ), y ^ 1 * Real.exp (-(1 / 2) * y ^ 2) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_one, Real.rpow_two] at h
  norm_num [Real.rpow_neg_one, Real.Gamma_one] at h
  simpa using h

lemma half_int_three : ∫ y in Set.Ioi (0 : ℝ), y ^ 3 * Real.exp (-(1 / 2) * y ^ 2) = 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((3 : ℕ) : ℝ)) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  simp only [Real.rpow_natCast, Real.rpow_two] at h
  norm_num [Real.Gamma_two] at h
  simpa using h

lemma gauss_abs_pow_eq (j : ℕ) :
    ∫ z, |z| ^ j ∂(gaussianReal 0 1) =
      2 * gaussK * ∫ y in Set.Ioi (0 : ℝ), y ^ j * Real.exp (-(1 / 2) * y ^ 2) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpt : ∀ z : ℝ, gaussianPDFReal 0 1 z • |z| ^ j =
      gaussK * (|z| ^ j * Real.exp (-(1 / 2) * |z| ^ 2)) := by
    intro z
    rw [smul_eq_mul, gaussianPDFReal_def, gaussK, sq_abs]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have e : -z ^ 2 / 2 = -(1 / 2) * z ^ 2 := by ring
    rw [e]
    ring
  calc ∫ z, gaussianPDFReal 0 1 z • |z| ^ j
      = ∫ z, gaussK * (|z| ^ j * Real.exp (-(1 / 2) * |z| ^ 2)) := integral_congr_ae (ae_of_all _ hpt)
    _ = ∫ z, (fun y : ℝ => gaussK * (y ^ j * Real.exp (-(1 / 2) * y ^ 2))) |z| := rfl
    _ = 2 * ∫ y in Set.Ioi (0 : ℝ), gaussK * (y ^ j * Real.exp (-(1 / 2) * y ^ 2)) :=
        integral_comp_abs (f := fun y : ℝ => gaussK * (y ^ j * Real.exp (-(1 / 2) * y ^ 2)))
    _ = 2 * gaussK * ∫ y in Set.Ioi (0 : ℝ), y ^ j * Real.exp (-(1 / 2) * y ^ 2) := by
        rw [integral_const_mul]
        ring

lemma gauss_abs_one : ∫ z, |z| ^ 1 ∂(gaussianReal 0 1) = 2 * gaussK := by
  rw [gauss_abs_pow_eq 1, half_int_one, mul_one]

lemma gauss_abs_three : ∫ z, |z| ^ 3 ∂(gaussianReal 0 1) = 4 * gaussK := by
  rw [gauss_abs_pow_eq 3, half_int_three]
  ring

lemma gauss_sq_one : ∫ z : ℝ, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_eq_integral (μ := gaussianReal 0 1) (X := id) measurable_id.aemeasurable
  rw [variance_id_gaussianReal] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  simpa using h.symm

/-! ### The law of `c|G|` -/

lemma map_pow_integrable (c : ℝ) (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j) ((gaussianReal 0 1).map (fun z : ℝ => c * |z|)) := by
  rw [integrable_map_measure (g := fun x : ℝ => x ^ j) (by fun_prop : Measurable fun x : ℝ => x ^ j).aestronglyMeasurable
    (by fun_prop : Measurable fun z : ℝ => c * |z|).aemeasurable]
  refine ((gauss_integrable_abs_pow 0 1 j).const_mul (c ^ j)).congr (ae_of_all _ fun z => ?_)
  simp [mul_pow]

/-! ### Third central moment: general identities -/

/-- Shifted monomials are integrable. -/
lemma shift_pow_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ j : ℕ, Integrable (fun x : ℝ => x ^ j) μ) (m : ℝ) (k : ℕ) (hk : k ≤ 3) :
    Integrable (fun x : ℝ => (x - m) ^ k) μ := by
  interval_cases k
  · simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) μ)
  · exact ((hμ 1).sub (integrable_const m)).congr (ae_of_all _ fun x => by simp)
  · refine (((hμ 2).sub ((hμ 1).const_mul (2 * m))).add (integrable_const (m ^ 2))).congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · refine ((((hμ 3).sub ((hμ 2).const_mul (3 * m))).add ((hμ 1).const_mul (3 * m ^ 2))).sub
      (integrable_const (m ^ 3))).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- Expansion of the third central moment in raw moments. -/
lemma third_central_expand (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ : ∀ j : ℕ, Integrable (fun x : ℝ => x ^ j) ρ) :
    ∫ x, (x - ∫ y, y ∂ρ) ^ 3 ∂ρ =
      ∫ x, x ^ 3 ∂ρ - 3 * (∫ x, x ∂ρ) * (∫ x, x ^ 2 ∂ρ) + 2 * (∫ x, x ∂ρ) ^ 3 := by
  have i1 : Integrable (fun x : ℝ => x) ρ := by simpa using hρ 1
  have i2 := hρ 2
  have i3 := hρ 3
  set m := ∫ y, y ∂ρ with hm
  have e : ∀ x : ℝ, (x - m) ^ 3 = (x ^ 3 - 3 * m * x ^ 2 + 3 * m ^ 2 * x) - m ^ 3 :=
    fun x => by ring
  have iA : Integrable (fun x : ℝ => x ^ 3 - 3 * m * x ^ 2) ρ := i3.sub (i2.const_mul (3 * m))
  have iB : Integrable (fun x : ℝ => 3 * m ^ 2 * x) ρ := i1.const_mul (3 * m ^ 2)
  have iAB : Integrable (fun x : ℝ => x ^ 3 - 3 * m * x ^ 2 + 3 * m ^ 2 * x) ρ := iA.add iB
  simp only [e]
  rw [integral_sub iAB (integrable_const _), integral_add iA iB,
    integral_sub i3 (i2.const_mul _), integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul, ← hm, mul_one]
  ring

/-- Convolution with an independent centred Gaussian-type summand leaves the third central moment
unchanged. -/
theorem conv_third_eq (μ γ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ : ∀ j : ℕ, Integrable (fun x : ℝ => x ^ j) μ)
    (hγ : ∀ j : ℕ, Integrable (fun y : ℝ => y ^ j) γ)
    (h1 : ∫ y, y ∂γ = 0) (h3 : ∫ y, y ^ 3 ∂γ = 0) :
    thirdCentralMoment (Measure.conv μ γ) = ∫ x, (x - ∫ y, y ∂μ) ^ 3 ∂μ := by
  have hconv : ∀ g : ℝ → ℝ, Measurable g →
      ∫ z, g z ∂(Measure.conv μ γ) = ∫ p : ℝ × ℝ, g (p.1 + p.2) ∂(μ.prod γ) := by
    intro g hg
    unfold Measure.conv
    exact integral_map (measurable_fst.add measurable_snd).aemeasurable hg.aestronglyMeasurable
  set m := ∫ y, y ∂μ with hm
  have hx : Integrable (fun x : ℝ => x) μ := by simpa using hμ 1
  have hy : Integrable (fun y : ℝ => y) γ := by simpa using hγ 1
  have hz : ∫ x, (x - m) ∂μ = 0 := by
    rw [integral_sub hx (integrable_const _)]
    simp [hm]
  have ip1 : Integrable (fun p : ℝ × ℝ => p.1) (μ.prod γ) := by
    simpa using hx.mul_prod (integrable_const (1 : ℝ))
  have ip2 : Integrable (fun p : ℝ × ℝ => p.2) (μ.prod γ) := by
    simpa using (integrable_const (1 : ℝ)).mul_prod hy
  have f1 : ∫ p : ℝ × ℝ, p.1 ∂(μ.prod γ) = m := by
    have := integral_prod_mul (μ := μ) (ν := γ) (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ))
    simpa using this
  have f2 : ∫ p : ℝ × ℝ, p.2 ∂(μ.prod γ) = 0 := by
    have := integral_prod_mul (μ := μ) (ν := γ) (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y)
    simpa [h1] using this
  have hmean : ∫ y, y ∂(Measure.conv μ γ) = m := by
    rw [hconv (fun y => y) measurable_id]
    rw [integral_add ip1 ip2, f1, f2, add_zero]
  unfold thirdCentralMoment
  rw [hmean, hconv (fun z => (z - m) ^ 3) (by fun_prop)]
  have expand : ∀ p : ℝ × ℝ, (p.1 + p.2 - m) ^ 3 =
      (p.1 - m) ^ 3 * 1 + (3 * (p.1 - m) ^ 2) * p.2 + (3 * (p.1 - m)) * p.2 ^ 2 + 1 * p.2 ^ 3 :=
    fun p => by ring
  have sh3 := shift_pow_integrable μ hμ m 3 (by norm_num)
  have sh2 := shift_pow_integrable μ hμ m 2 (by norm_num)
  have sh1 : Integrable (fun x : ℝ => 3 * (x - m)) μ :=
    ((shift_pow_integrable μ hμ m 1 (by norm_num)).const_mul 3).congr (ae_of_all _ fun x => by simp)
  have J0 : Integrable (fun p : ℝ × ℝ => (p.1 - m) ^ 3 * 1) (μ.prod γ) :=
    sh3.mul_prod (integrable_const (1 : ℝ))
  have J1 : Integrable (fun p : ℝ × ℝ => (3 * (p.1 - m) ^ 2) * p.2) (μ.prod γ) :=
    (sh2.const_mul 3).mul_prod hy
  have J2 : Integrable (fun p : ℝ × ℝ => (3 * (p.1 - m)) * p.2 ^ 2) (μ.prod γ) :=
    sh1.mul_prod (hγ 2)
  have J3 : Integrable (fun p : ℝ × ℝ => 1 * p.2 ^ 3) (μ.prod γ) :=
    (integrable_const (1 : ℝ)).mul_prod (hγ 3)
  have Q : ∀ f g : ℝ → ℝ, ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂(μ.prod γ) =
      (∫ x, f x ∂μ) * ∫ y, g y ∂γ := fun f g => integral_prod_mul f g
  have K01 : Integrable (fun p : ℝ × ℝ => (p.1 - m) ^ 3 * 1 + 3 * (p.1 - m) ^ 2 * p.2) (μ.prod γ) :=
    J0.add J1
  have K012 : Integrable (fun p : ℝ × ℝ => (p.1 - m) ^ 3 * 1 + 3 * (p.1 - m) ^ 2 * p.2 +
      3 * (p.1 - m) * p.2 ^ 2) (μ.prod γ) := K01.add J2
  simp only [expand]
  rw [integral_add K012 J3, integral_add K01 J2, integral_add J0 J1,
    Q (fun x => (x - m) ^ 3) (fun _ => 1), Q (fun x => 3 * (x - m) ^ 2) (fun y => y),
    Q (fun x => 3 * (x - m)) (fun y => y ^ 2), Q (fun _ => 1) (fun y => y ^ 3)]
  have hz3 : ∫ x, 3 * (x - m) ∂μ = 0 := by
    rw [integral_const_mul, hz, mul_zero]
  rw [h1, h3, hz3]
  simp

/-! ### Assembly -/

lemma gauss_abs_one' : ∫ z, |z| ∂(gaussianReal 0 1) = 2 * gaussK := by
  simpa using gauss_abs_one

theorem conditioned_ou_third_cumulant_proof :
    type_of% @HRS.MH.CondOu.conditioned_ou_third_cumulant := by
  intro d hd s hs0 hsd β hβ k hk t _ht
  have hnn : 0 ≤ rieszCoeff d s k := HRS.PDE.rieszCoeff_nonneg (by omega) hs0 hsd k
  have hpos1 : 0 < 1 + β * rieszCoeff d s k := by nlinarith [mul_nonneg hβ.le hnn]
  have hc : 0 < Real.exp (-PDE.transientRate d s β k * t) * Real.sqrt (1 + β * rieszCoeff d s k)⁻¹ :=
    mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 (inv_pos.2 hpos1))
  unfold halfNormalMixtureLaw
  generalize hcdef : Real.exp (-PDE.transientRate d s β k * t) *
    Real.sqrt (1 + β * rieszCoeff d s k)⁻¹ = c at hc ⊢
  obtain ⟨hP, hγ, hγ1, hγ3⟩ := gaussianLaw_facts
    ((1 + β * rieszCoeff d s k)⁻¹ * (1 - Real.exp (-2 * PDE.transientRate d s β k * t)))
  have hφ : Measurable (fun z : ℝ => c * |z|) := by fun_prop
  rw [conv_third_eq _ _ (map_pow_integrable c) hγ hγ1 hγ3, third_central_expand _ (map_pow_integrable c)]
  have hm1 : ∫ x, x ∂((gaussianReal 0 1).map (fun z : ℝ => c * |z|)) = c * (2 * gaussK) := by
    rw [integral_map hφ.aemeasurable (by fun_prop : Measurable fun x : ℝ => x).aestronglyMeasurable,
      integral_const_mul, gauss_abs_one']
  have hm2 : ∫ x, x ^ 2 ∂((gaussianReal 0 1).map (fun z : ℝ => c * |z|)) = c ^ 2 := by
    rw [integral_map hφ.aemeasurable (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable]
    simp only [mul_pow, sq_abs]
    rw [integral_const_mul, gauss_sq_one, mul_one]
  have hm3 : ∫ x, x ^ 3 ∂((gaussianReal 0 1).map (fun z : ℝ => c * |z|)) = c ^ 3 * (4 * gaussK) := by
    rw [integral_map hφ.aemeasurable (by fun_prop : Measurable fun x : ℝ => x ^ 3).aestronglyMeasurable]
    simp only [mul_pow]
    rw [integral_const_mul, gauss_abs_three]
  rw [hm1, hm2, hm3]
  have h8 := gaussK_eight
  have hK := gaussK_pos
  have hcub : 0 < 16 * gaussK ^ 3 - 2 * gaussK := by nlinarith [mul_pos hK (sub_pos.2 h8)]
  have e : c ^ 3 * (4 * gaussK) - 3 * (c * (2 * gaussK)) * c ^ 2 + 2 * (c * (2 * gaussK)) ^ 3 =
      c ^ 3 * (16 * gaussK ^ 3 - 2 * gaussK) := by ring
  rw [e]
  exact mul_pos (pow_pos hc 3) hcub

end HRS.MH.CondOuP
