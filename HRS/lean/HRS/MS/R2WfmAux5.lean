import HRS.MS.R2WfmAux4

/-!
# HRS.MS.R2WfmAux5 -- `round2_weighted_field_moments` (S9.7), part 5: pathwise synthesis of the two functionals

Packet S97.  For every configuration `X`: `s97_emp_synth` (`r2EmpDistr`) and `s97_comm_synth` (`N·pairEnergy` of the commutator
kernel of `∇(⟨x⟩^P ψ)`) equal `∫ (A_ψ u - B_ψ v) dξ` with `u(ξ), v(ξ)` the same functional applied to the weighted plane waves
`s97_pw ξ 0`, `s97_pw ξ (-π/2)`.
-/

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

noncomputable section
namespace HRS.MS.R2Wfm
open HRS.Whole HRS.MS.R2Poly HRS.MS.Wr

variable {d : ℕ}

theorem s97_pe_lin {N : ℕ} (X : EucConfig d N) (μ : Measure (Euc d)) (a b : ℝ) (k0 k1 : Euc d → Euc d → ℝ)
    (h0 : ∀ x, Integrable (k0 x) μ) (h1 : ∀ x, Integrable (k1 x) μ)
    (H0 : Integrable (fun x => ∫ y, k0 x y ∂μ) μ) (H1 : Integrable (fun x => ∫ y, k1 x y ∂μ) μ) :
    pairEnergy (fun x y => a * k0 x y - b * k1 x y) X μ = a * pairEnergy k0 X μ - b * pairEnergy k1 X μ := by
  unfold pairEnergy
  have e1 : ∀ x, ∫ y, (a * k0 x y - b * k1 x y) ∂μ = a * ∫ y, k0 x y ∂μ - b * ∫ y, k1 x y ∂μ := fun x => by
    rw [integral_sub ((h0 x).const_mul a) ((h1 x).const_mul b), integral_const_mul, integral_const_mul]
  simp_rw [e1]
  rw [integral_sub (H0.const_mul a) (H1.const_mul b), integral_const_mul, integral_const_mul]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, mul_sub]
  ring

theorem s97_comm_synth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M C₀ c₀ Pw : ℝ}
    (hc : 0 < c₀) (hP : 0 ≤ Pw) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M)
    (hG : ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)) {N : ℕ} (X : EucConfig d N)
    (ψ : SchwartzMap (Euc d) ℝ) :
    (N : ℝ) * pairEnergy (commutatorKernel d s (fun x => gradient (fun z => jbracket z ^ Pw * ψ z) x)) X
        (HRS.Whole.withDensityReal ρ) =
      ∫ ξ, (s97_A ψ ξ * ((N : ℝ) * pairEnergy (s97_K s Pw ξ 0) X (HRS.Whole.withDensityReal ρ)) -
        s97_B ψ ξ * ((N : ℝ) * pairEnergy (s97_K s Pw ξ (-(Real.pi / 2))) X (HRS.Whole.withDensityReal ρ))) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hE1, hE2⟩ := s95_poly_integrable hd hs0 hs M C₀ c₀ hc hP ρ hρ hM hG 1 zero_le_one
    (s97_E s Pw) (s97_E_poly s Pw)
  have hKint : ∀ (ξ : Euc d) (φ0 : ℝ), (∀ x, Integrable (s97_K s Pw ξ φ0 x) μ) ∧
      Integrable (fun p : Euc d × Euc d => s97_K s Pw ξ φ0 p.1 p.2) (μ.prod μ) := by
    intro ξ φ0
    have := s95_poly_integrable hd hs0 hs M C₀ c₀ hc hP ρ hρ hM hG _
      (mul_nonneg (s97_Kc_nonneg Pw hP) (by positivity)) (s97_K s Pw ξ φ0) (s97_poly_kernel hs0 hP ξ φ0)
    exact this
  set g : Euc d → Euc d → Euc d → ℝ := fun ξ x y =>
    s97_A ψ ξ * s97_K s Pw ξ 0 x y - s97_B ψ ξ * s97_K s Pw ξ (-(Real.pi / 2)) x y with hg
  have hgm : Measurable (fun q : Euc d × Euc d × Euc d => g q.1 q.2.1 q.2.2) := by
    have hA : Measurable (fun q : Euc d × Euc d × Euc d => s97_A ψ q.1) := (s97_A_cont ψ).measurable.comp measurable_fst
    have hB : Measurable (fun q : Euc d × Euc d × Euc d => s97_B ψ q.1) := (s97_B_cont ψ).measurable.comp measurable_fst
    exact (hA.mul (s97_K_meas s Pw 0)).sub (hB.mul (s97_K_meas s Pw (-(Real.pi / 2))))
  set β : Euc d → ℝ := fun ξ => s97_Kc s Pw * ((1 + ‖ξ‖) ^ 2 * (|s97_A ψ ξ| + |s97_B ψ ξ|)) with hβ
  have hβi : Integrable β := (s97_AB_int ψ).const_mul _
  have hβ0 : ∀ ξ, 0 ≤ β ξ := fun ξ => mul_nonneg (s97_Kc_nonneg Pw hP) (by positivity)
  have hbd : ∀ ξ x y, |g ξ x y| ≤ β ξ * s97_E s Pw x y := by
    intro ξ x y
    have h0 := s97_K_bound hs0 hP ξ 0 x y
    have h1 := s97_K_bound hs0 hP ξ (-(Real.pi / 2)) x y
    have hE := s97_E_nonneg s Pw x y
    calc |g ξ x y| ≤ |s97_A ψ ξ * s97_K s Pw ξ 0 x y| + |s97_B ψ ξ * s97_K s Pw ξ (-(Real.pi / 2)) x y| := abs_sub _ _
      _ = |s97_A ψ ξ| * |s97_K s Pw ξ 0 x y| + |s97_B ψ ξ| * |s97_K s Pw ξ (-(Real.pi / 2)) x y| := by
          rw [abs_mul, abs_mul]
      _ ≤ |s97_A ψ ξ| * (s97_Kc s Pw * (1 + ‖ξ‖) ^ 2 * s97_E s Pw x y) +
          |s97_B ψ ξ| * (s97_Kc s Pw * (1 + ‖ξ‖) ^ 2 * s97_E s Pw x y) := by gcongr
      _ = β ξ * s97_E s Pw x y := by rw [hβ]; ring
  have hkernel : ∀ x y, commutatorKernel d s (fun x => gradient (fun z => jbracket z ^ Pw * ψ z) x) x y =
      ∫ ξ, g ξ x y := by
    intro x y
    rw [s97_comm_eq]
    set G := rieszKernelGrad d s (x - y)
    rw [s97_fderiv_phi ψ Pw x G, s97_fderiv_phi ψ Pw y G,
      ← integral_sub (s97_phi_int ψ Pw x G) (s97_phi_int ψ Pw y G)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hg, s97_K, s97_comm_eq]
    ring
  have hlin : ∀ ξ, pairEnergy (g ξ) X μ = s97_A ψ ξ * pairEnergy (s97_K s Pw ξ 0) X μ -
      s97_B ψ ξ * pairEnergy (s97_K s Pw ξ (-(Real.pi / 2))) X μ := by
    intro ξ
    exact s97_pe_lin X μ _ _ _ _ (hKint ξ 0).1 (hKint ξ _).1 (hKint ξ 0).2.integral_prod_left (hKint ξ _).2.integral_prod_left
  have hpe := s97_pe_integral X μ g hgm β hβi hβ0 (s97_E s Pw) (s97_E_nonneg s Pw)
    (s97_E_poly s Pw).measurable hE1 hE2 hbd
  have : pairEnergy (commutatorKernel d s (fun x => gradient (fun z => jbracket z ^ Pw * ψ z) x)) X μ =
      pairEnergy (fun x y => ∫ ξ, g ξ x y) X μ := by
    congr 1; funext x y; exact hkernel x y
  rw [this, hpe, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [hlin]; ring


theorem s97_pw_cont2 (Pw φ0 : ℝ) : Continuous (fun p : Euc d × Euc d => s97_pw Pw p.2 φ0 p.1) := by
  have h2 : Continuous (fun z : Euc d => jbracket z ^ Pw) :=
    (by unfold jbracket; fun_prop : Continuous fun z : Euc d => jbracket z).rpow_const
      (fun z => Or.inl (zero_lt_one.trans_le (s95_one_le_jb z)).ne')
  have h2' : Continuous (fun p : Euc d × Euc d => jbracket p.1 ^ Pw) := h2.comp continuous_fst
  unfold s97_pw
  fun_prop

theorem s97_pw_abs (Pw ξ φ0 x) : |s97_pw Pw (ξ : Euc d) φ0 (x : Euc d)| ≤ jbracket x ^ Pw := by
  unfold s97_pw
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (s97_jb_nonneg x) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (s97_jb_nonneg x) _) (Real.abs_cos_le_one _)

theorem s97_F_eq (ψ : SchwartzMap (Euc d) ℝ) (Pw : ℝ) (x ξ : Euc d) :
    s97_A ψ ξ * s97_pw Pw ξ 0 x - s97_B ψ ξ * s97_pw Pw ξ (-(Real.pi / 2)) x =
      jbracket x ^ Pw * (s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ) -
        s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)) := by
  simp only [s97_pw, add_zero]
  rw [show 2 * Real.pi * inner ℝ x ξ + -(Real.pi / 2) = 2 * Real.pi * inner ℝ x ξ - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two]
  ring

theorem s97_emp_synth (hd : 1 ≤ d) {C₀ c₀ Pw : ℝ} (hc : 0 < c₀) (hP : 0 ≤ Pw) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hG : ∀ x, ρ x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2))
    {N : ℕ} (hN : 0 < N) (X : EucConfig d N) (ψ : SchwartzMap (Euc d) ℝ) :
    r2EmpDistr (HRS.Whole.withDensityReal ρ) X (fun x => jbracket x ^ Pw * ψ x) =
      ∫ ξ, (s97_A ψ ξ * r2EmpDistr (HRS.Whole.withDensityReal ρ) X (s97_pw Pw ξ 0) -
        s97_B ψ ξ * r2EmpDistr (HRS.Whole.withDensityReal ρ) X (s97_pw Pw ξ (-(Real.pi / 2)))) := by
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set F : Euc d → Euc d → ℝ := fun x ξ => s97_A ψ ξ * s97_pw Pw ξ 0 x -
    s97_B ψ ξ * s97_pw Pw ξ (-(Real.pi / 2)) x with hF
  have hpwi : ∀ ξ φ0, Integrable (s97_pw Pw ξ φ0) μ := fun ξ φ0 =>
    s95_test_integrable d C₀ c₀ hc hP ρ hρ hG 1 zero_le_one _
      (s97_pw_cont2 Pw φ0 |>.comp (continuous_id.prodMk continuous_const) |>.measurable)
      (fun x => by simpa using s97_pw_abs Pw ξ φ0 x)
  have hwi : Integrable (fun x : Euc d => jbracket x ^ Pw) μ :=
    s95_test_integrable d C₀ c₀ hc hP ρ hρ hG 1 zero_le_one _ (s95_jb_meas.pow_const Pw) (fun x => by
      simp [abs_of_nonneg (Real.rpow_nonneg (s97_jb_nonneg x) _)])
  have hFm : Measurable (fun p : Euc d × Euc d => F p.1 p.2) := by
    have hA : Continuous (fun p : Euc d × Euc d => s97_A ψ p.2) := (s97_A_cont ψ).comp continuous_snd
    have hB : Continuous (fun p : Euc d × Euc d => s97_B ψ p.2) := (s97_B_cont ψ).comp continuous_snd
    exact ((hA.mul (s97_pw_cont2 Pw 0)).sub (hB.mul (s97_pw_cont2 Pw (-(Real.pi / 2))))).measurable
  have hABi : Integrable (fun ξ : Euc d => |s97_A ψ ξ| + |s97_B ψ ξ|) := by
    refine (s97_AB_int ψ).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · have := s97_A_cont ψ; have := s97_B_cont ψ
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · have : 1 ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith [norm_nonneg ξ]
      have h0 : 0 ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      nlinarith
  have hFi : Integrable (fun p : Euc d × Euc d => F p.1 p.2) (μ.prod volume) := by
    refine (hwi.mul_prod hABi).mono' hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simp only [hF, s97_F_eq]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (s97_jb_nonneg p.1) _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (s97_jb_nonneg p.1) _)
    have h3 := Real.abs_cos_le_one (2 * Real.pi * inner ℝ p.1 p.2)
    have h4 := Real.abs_sin_le_one (2 * Real.pi * inner ℝ p.1 p.2)
    calc _ ≤ |s97_A ψ p.2 * Real.cos (2 * Real.pi * inner ℝ p.1 p.2)| + |s97_B ψ p.2 * Real.sin (2 * Real.pi * inner ℝ p.1 p.2)| :=
          abs_sub _ _
      _ = |s97_A ψ p.2| * |Real.cos (2 * Real.pi * inner ℝ p.1 p.2)| + |s97_B ψ p.2| * |Real.sin (2 * Real.pi * inner ℝ p.1 p.2)| := by
          rw [abs_mul, abs_mul]
      _ ≤ |s97_A ψ p.2| + |s97_B ψ p.2| := by
          have := abs_nonneg (s97_A ψ p.2); have := abs_nonneg (s97_B ψ p.2)
          nlinarith
  have hFx : ∀ x, Integrable (fun ξ => F x ξ) := fun x => by
    simp only [hF, s97_F_eq]
    exact (s97_int1 ψ x).const_mul _
  have hpt1 : ∀ ξ, ∫ x, F x ξ ∂μ = s97_A ψ ξ * HRS.Whole.pair μ (s97_pw Pw ξ 0) -
      s97_B ψ ξ * HRS.Whole.pair μ (s97_pw Pw ξ (-(Real.pi / 2))) := by
    intro ξ
    unfold HRS.Whole.pair
    simp only [hF]
    rw [integral_sub ((hpwi ξ 0).const_mul _) ((hpwi ξ _).const_mul _), integral_const_mul, integral_const_mul]
  have hpt2 : ∀ ξ, s97_A ψ ξ * HRS.Whole.pair (HRS.Whole.empirical X) (s97_pw Pw ξ 0) -
      s97_B ψ ξ * HRS.Whole.pair (HRS.Whole.empirical X) (s97_pw Pw ξ (-(Real.pi / 2))) =
      (N : ℝ)⁻¹ * ∑ i, F (X i) ξ := by
    intro ξ
    simp only [hF, HRS.Whole.pair_empirical hN, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have i_p : Integrable (fun ξ => s97_A ψ ξ * HRS.Whole.pair μ (s97_pw Pw ξ 0) -
      s97_B ψ ξ * HRS.Whole.pair μ (s97_pw Pw ξ (-(Real.pi / 2)))) := by
    have := hFi.integral_prod_right
    simpa only [hpt1] using this
  have i_e : Integrable (fun ξ => s97_A ψ ξ * HRS.Whole.pair (HRS.Whole.empirical X) (s97_pw Pw ξ 0) -
      s97_B ψ ξ * HRS.Whole.pair (HRS.Whole.empirical X) (s97_pw Pw ξ (-(Real.pi / 2)))) := by
    simp_rw [hpt2]
    exact (integrable_finset_sum _ fun i _ => hFx (X i)).const_mul _
  -- the μ-pairing
  have hpair : HRS.Whole.pair μ (fun x => jbracket x ^ Pw * ψ x) = ∫ ξ, (s97_A ψ ξ * HRS.Whole.pair μ (s97_pw Pw ξ 0) -
      s97_B ψ ξ * HRS.Whole.pair μ (s97_pw Pw ξ (-(Real.pi / 2)))) := by
    unfold HRS.Whole.pair
    have h1 : ∀ x, jbracket x ^ Pw * ψ x = ∫ ξ, F x ξ := fun x => s97_val_phi ψ Pw x
    simp_rw [h1]
    rw [integral_integral_swap (f := fun x ξ => F x ξ) hFi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => hpt1 ξ)
  have hemp : HRS.Whole.pair (HRS.Whole.empirical X) (fun x => jbracket x ^ Pw * ψ x) = ∫ ξ, (s97_A ψ ξ * HRS.Whole.pair (HRS.Whole.empirical X) (s97_pw Pw ξ 0) -
      s97_B ψ ξ * HRS.Whole.pair (HRS.Whole.empirical X) (s97_pw Pw ξ (-(Real.pi / 2)))) := by
    rw [HRS.Whole.pair_empirical hN]
    have h1 : ∀ x, jbracket x ^ Pw * ψ x = ∫ ξ, F x ξ := fun x => s97_val_phi ψ Pw x
    simp_rw [h1]
    rw [← integral_finset_sum _ (fun i _ => hFx (X i)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hF, HRS.Whole.pair_empirical hN, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  unfold r2EmpDistr
  rw [hpair, hemp, ← integral_sub i_e i_p, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  ring

end HRS.MS.R2Wfm
end
