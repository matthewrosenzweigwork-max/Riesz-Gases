import HRS.MS.Fp81S21InitialUncentered10

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc MemCb)
open HRS.MS.R26T3

/-- Integrating the S4.7 corrector equation fixes its additive constant. The one-half
coefficient comes from the integrated commutator identity, with the uncentered double integral
kept explicit. -/
theorem fp81s21_initial_c0_identity
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {ψ χ : Euc p.d → ℝ} {Bχ : ℝ}
    (hχ : S47.S47Feat p.d p.s (R.ρ 0) p.γ ψ χ Bχ)
    (hψ : MemCb 1 ψ) :
    ∃ c0 : ℝ,
      c0 = p.γ * (∫ x, ψ x ∂(r26t3_mu R 0) -
        (1 / 2) * ∫ x, ∫ y,
          HRS.Whole.commutatorKernel p.d p.s (gradient χ) x y
            ∂(r26t3_mu R 0) ∂(r26t3_mu R 0)) ∧
      ∀ᵐ x ∂(volume : Measure (Euc p.d)),
        Laplacian.laplacian χ x - (p.a * p.β) * ⟪x, gradient χ x⟫ +
          ⟪E.Bd x + p.γ • gradient (HRS.Whole.convMeasure
            (HRS.Whole.rieszKernel p.d p.s) (r26t3_mu R 0)) x, gradient χ x⟫ -
          p.γ * ∫ y, HRS.Whole.commutatorKernel p.d p.s (gradient χ) x y
            ∂(r26t3_mu R 0) = -p.γ * ψ x + c0 := by
  let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ 0)
  let gen : Euc p.d → ℝ := HRS.Whole.weightedGen (R.ρ 0) χ
  let U : Euc p.d → ℝ := HRS.Whole.convMeasure (HRS.Whole.rieszKernel p.d p.s) μ
  let row : Euc p.d → ℝ := fun x => ∫ y,
    HRS.Whole.commutatorKernel p.d p.s (gradient χ) x y ∂μ
  let innerTerm : Euc p.d → ℝ := fun x => ⟪gradient χ x, gradient U x⟫
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    have hd2 : (p.d : ℝ) / 2 ≤ (p.d : ℝ) := by nlinarith
    exact lt_of_lt_of_le p.hs hd2
  have hT : S47.TRef p.d p.s (R.ρ 0) (p.a * p.β) E.C E.c E.BU E.BB E.Bd :=
    E.reference
  have hstarData := S47.s47_star p.hd p.hs0 hsd hγ hT hχ.smooth hχ.B1 hχ.B2 hχ.corr
  obtain ⟨c0, hstar⟩ := hstarData
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  letI : IsProbabilityMeasure μ := hμprob
  have hconst : ∫ x : Euc p.d, (c0 : ℝ) ∂μ = c0 := by simp
  have hμac : μ ≪ (volume : Measure (Euc p.d)) := by
    dsimp [μ, HRS.Whole.withDensityReal]
    exact withDensity_absolutelyContinuous _ _
  have hstarμ : ∀ᵐ x ∂μ,
      Laplacian.laplacian χ x - (p.a * p.β) * ⟪x, gradient χ x⟫ +
        ⟪E.Bd x + p.γ • gradient U x, gradient χ x⟫ - p.γ * row x =
        -p.γ * ψ x + c0 := hμac.ae_le hstar
  have hgenMean : ∫ x, gen x ∂μ = 0 := by
    dsimp [gen, μ]
    exact fp81s21_initial_integral_weightedGen_zero hT hχ.smooth hχ.B1 hχ.B2
  have hgenInt : Integrable gen μ := by
    exact hχ.r2.integrable one_le_two
  obtain ⟨Bψ, hBψ⟩ := hψ.2 0 (by omega)
  have hψbd : ∀ x, |ψ x| ≤ Bψ := by
    intro x
    have hx := hBψ (Set.mem_range_self x)
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
  have hψmeas : Measurable ψ := hψ.1.continuous.measurable
  have hψInt : Integrable ψ μ :=
    Integrable.of_bound hψmeas.aestronglyMeasurable Bψ
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hψbd x)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ.smooth
  have hB10 : 0 ≤ Bχ := (norm_nonneg _).trans (hχ.B1 0)
  let Λ : ℝ≥0 := ⟨Bχ, hB10⟩
  have hLip : LipschitzWith Λ (gradient χ) :=
    lipschitzWith_of_nnnorm_fderiv_le (hv1.differentiable (by norm_num)) (fun x => by
      have hx := hχ.B2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hφb : ∀ x : Euc p.d, 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 :=
    fun _ => ⟨by norm_num, by norm_num⟩
  have hφm : Measurable (fun _ : Euc p.d => (1 : ℝ)) := measurable_const
  let ν : Measure (Euc p.d) := μ.withDensity (fun _ : Euc p.d => ENNReal.ofReal (1 : ℝ))
  have hνeq : ν = μ.withDensity (fun _ : Euc p.d => ENNReal.ofReal (1 : ℝ)) := rfl
  obtain ⟨Bh, hBh0, hBh⟩ := S47.s47_Hbounds p.hd p.hs0 hsd hT hLip hφb hφm ν hνeq
  have hrowMeas : Measurable row := by
    have hh : Measurable (Function.uncurry
        (HRS.Whole.commutatorKernel p.d p.s (gradient χ))) :=
      HRS.MS.Comm.comm_meas (s := p.s) (gradient χ) hv1.continuous.measurable
    change Measurable (fun x => ∫ y,
      HRS.Whole.commutatorKernel p.d p.s (gradient χ) x y ∂μ)
    exact (hh.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hrowBound : ∀ x, |row x| ≤ Bh := by
    intro x
    exact (hBh x).1
  have hrowInt : Integrable row μ :=
    Integrable.of_bound hrowMeas.aestronglyMeasurable Bh
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hrowBound x)
  have hU2 : ContDiff ℝ 2 U := hT.Usmooth.of_le (by norm_num)
  have hInnerMeas : Measurable innerTerm := by
    change Measurable (fun x => ⟪gradient χ x, gradient U x⟫)
    exact ((hv1.continuous).inner (s45_contDiff_gradient hU2).continuous).measurable
  have hInnerBound : ∀ x, |innerTerm x| ≤ Bχ * E.BU := by
    intro x
    calc
      |innerTerm x| ≤ ‖gradient χ x‖ * ‖gradient U x‖ := abs_real_inner_le_norm _ _
      _ ≤ Bχ * E.BU := by
        calc
          _ ≤ Bχ * ‖gradient U x‖ :=
            mul_le_mul_of_nonneg_right (hχ.B1 x) (norm_nonneg _)
          _ ≤ Bχ * E.BU := mul_le_mul_of_nonneg_left (hT.gradU_le x) hB10
  have hInnerInt : Integrable innerTerm μ :=
    Integrable.of_bound hInnerMeas.aestronglyMeasurable (Bχ * E.BU)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hInnerBound x)
  have hstarGen : ∀ᵐ x ∂μ,
      gen x = p.γ * innerTerm x - p.γ * row x + p.γ * ψ x - c0 := by
    filter_upwards [hstarμ] with x hx
    have hg := S47.s47_gen_eq hT (χ := χ) x
    have hi : ⟪E.Bd x + p.γ • gradient U x, gradient χ x⟫ =
        ⟪E.Bd x, gradient χ x⟫ + p.γ * innerTerm x := by
      calc
        _ = ⟪E.Bd x, gradient χ x⟫ +
            ⟪p.γ • gradient U x, gradient χ x⟫ := inner_add_left _ _ _
        _ = ⟪E.Bd x, gradient χ x⟫ +
            p.γ * ⟪gradient U x, gradient χ x⟫ := by rw [real_inner_smul_left]
        _ = ⟪E.Bd x, gradient χ x⟫ + p.γ * innerTerm x := by
          have hs : ⟪gradient U x, gradient χ x⟫ = innerTerm x := by
            dsimp [innerTerm]
            exact real_inner_comm _ _
          rw [hs]
    dsimp [innerTerm, U] at hi
    have hx' := hx
    rw [hi] at hx'
    change HRS.Whole.weightedGen (R.ρ 0) χ x =
      p.γ * innerTerm x - p.γ * row x + p.γ * ψ x - c0
    rw [hg]
    have hqbd : ⟪(p.a * p.β) • x - E.Bd x, gradient χ x⟫ =
        (p.a * p.β) * ⟪x, gradient χ x⟫ - ⟪E.Bd x, gradient χ x⟫ := by
      rw [inner_sub_left, real_inner_smul_left]
    rw [hqbd]
    dsimp [gen, row, μ] at hg ⊢ hx'
    linarith
  have hrowEq : ∀ᵐ x ∂μ,
      row x = innerTerm x + ψ x - p.γ⁻¹ * gen x - p.γ⁻¹ * c0 := by
    filter_upwards [hstarGen] with x hx
    have hγne : p.γ ≠ 0 := hγ.ne'
    field_simp [hγne]
    linarith
  have hstarInt : Integrable gen μ := hgenInt
  have hlinear :
      ∫ x, gen x ∂μ =
        p.γ * (∫ x, innerTerm x ∂μ) - p.γ * (∫ x, row x ∂μ) +
          p.γ * (∫ x, ψ x ∂μ) - c0 := by
    have h1 : Integrable (fun x => p.γ * innerTerm x) μ := hInnerInt.const_mul _
    have h2 : Integrable (fun x => p.γ * row x) μ := hrowInt.const_mul _
    have h3 : Integrable (fun x => p.γ * ψ x) μ := hψInt.const_mul _
    have h12 : Integrable (fun x => p.γ * innerTerm x - p.γ * row x) μ := h1.sub h2
    have h123 : Integrable (fun x =>
        (p.γ * innerTerm x - p.γ * row x) + p.γ * ψ x) μ := h12.add h3
    have hI1 : (∫ x, p.γ * innerTerm x ∂μ) =
        p.γ * ∫ x, innerTerm x ∂μ := integral_const_mul p.γ innerTerm
    have hI2 : (∫ x, p.γ * row x ∂μ) =
        p.γ * ∫ x, row x ∂μ := integral_const_mul p.γ row
    have hI3 : (∫ x, p.γ * ψ x ∂μ) =
        p.γ * ∫ x, ψ x ∂μ := integral_const_mul p.γ ψ
    calc
      _ = ∫ x, (p.γ * innerTerm x - p.γ * row x + p.γ * ψ x - c0) ∂μ :=
        integral_congr_ae hstarGen
      _ = (∫ x, (p.γ * innerTerm x - p.γ * row x + p.γ * ψ x) ∂μ) -
          ∫ x, c0 ∂μ := integral_sub h123 (integrable_const c0)
      _ = p.γ * (∫ x, innerTerm x ∂μ) - p.γ * (∫ x, row x ∂μ) +
          p.γ * (∫ x, ψ x ∂μ) - c0 := by
        rw [integral_add h12 h3, integral_sub h1 h2]
        rw [hconst]
        rw [hI1]
        rw [hI2]
        rw [hI3]
  have hhalf := fp81s21_initial_integral_commutator_half
    p.hd hT p.hs0 hsd hχ.smooth hχ.B1 hχ.B2 hχ.r2
  have hrowDouble : (∫ x, row x ∂μ) =
      2 * ∫ x, innerTerm x ∂μ := by
    simpa [row, innerTerm, μ, U] using hhalf
  have hmean := hgenMean
  have hc0 : c0 = p.γ * ((∫ x, ψ x ∂μ) -
      (1 / 2) * ∫ x, ∫ y,
        HRS.Whole.commutatorKernel p.d p.s (gradient χ) x y ∂μ ∂μ) := by
    rw [hgenMean, hrowDouble] at hlinear
    have : c0 = p.γ * (∫ x, ψ x ∂μ) -
        p.γ * (∫ x, innerTerm x ∂μ) := by linarith [hlinear]
    have hdouble :
        (∫ x, ∫ y, HRS.Whole.commutatorKernel p.d p.s (gradient χ) x y ∂μ ∂μ) =
          2 * (∫ x, innerTerm x ∂μ) := by
      simpa [innerTerm, μ, U] using hhalf
    rw [hdouble]
    nlinarith
  refine ⟨c0, ?_, ?_⟩
  · simpa [μ, r26t3_mu] using hc0
  · simpa [U, row, μ, r26t3_mu] using hstar

#print axioms fp81s21_initial_c0_identity

end HRS.Fp81.S21

end
