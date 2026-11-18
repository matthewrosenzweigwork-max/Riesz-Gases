import HRS.MS.Fp81S21InitialUncentered8

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc)

/-- The reference commutator has twice the potential-gradient pairing. This follows by
integrating the pointwise S4.7 corrector identity and using the potential integration by parts. -/
theorem fp81s21_initial_integral_commutator_half
    {d : ℕ} {s q C c BU BB : ℝ} {ρ : Euc d → ℝ} {Bd : Euc d → Euc d}
    (hd : 2 ≤ d) (hT : S47.TRef d s ρ q C c BU BB Bd)
    (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    (hgen2 : MemLp (HRS.Whole.weightedGen ρ χ) 2 (HRS.Whole.withDensityReal ρ)) :
    ∫ x, ∫ y, HRS.Whole.commutatorKernel d s (gradient χ) x y
      ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) =
      2 * ∫ x, ⟪gradient χ x,
        gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s)
          (HRS.Whole.withDensityReal ρ)) x⟫ ∂(HRS.Whole.withDensityReal ρ) := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  let h : Euc d → Euc d → ℝ := HRS.Whole.commutatorKernel d s (gradient χ)
  let row : Euc d → ℝ := fun x => ∫ y, h x y ∂μ
  let innerTerm : Euc d → ℝ := fun x => ⟪gradient χ x,
    gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ) x⟫
  let rawTerm : Euc d → ℝ := fun x => ∫ y,
    HRS.Whole.rieszKernel d s (x - y) * HRS.Whole.weightedGen ρ χ y ∂μ
  have hμ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  letI : IsProbabilityMeasure μ := hμ
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  let Λ : ℝ≥0 := ⟨B2, hB20⟩
  have hLip : LipschitzWith Λ (gradient χ) :=
    lipschitzWith_of_nnnorm_fderiv_le (hv1.differentiable (by norm_num)) (fun x => by
      have hx := hB2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hrowMeas : Measurable row := by
    have hhm : Measurable (Function.uncurry h) :=
      HRS.MS.Comm.comm_meas (s := s) (gradient χ) hv1.continuous.measurable
    change Measurable (fun x => ∫ y, h x y ∂μ)
    exact (hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  have hφb : ∀ x : Euc d, 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 :=
    fun _ => ⟨by norm_num, by norm_num⟩
  have hφm : Measurable (fun _ : Euc d => (1 : ℝ)) := measurable_const
  let ν : Measure (Euc d) := μ.withDensity (fun _ : Euc d => ENNReal.ofReal (1 : ℝ))
  have hνeq : ν = μ.withDensity (fun _ : Euc d => ENNReal.ofReal (1 : ℝ)) := rfl
  obtain ⟨Bh, hBh0, hBh⟩ := S47.s47_Hbounds hd hs0 hsd hT hLip hφb hφm ν hνeq
  have hrowBound : ∀ x, |row x| ≤ Bh := by
    intro x
    exact (hBh x).1
  have hrowInt : Integrable row μ :=
    Integrable.of_bound hrowMeas.aestronglyMeasurable Bh
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hrowBound x)
  have hU2 : ContDiff ℝ 2
      (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ) :=
    hT.Usmooth.of_le (by norm_num)
  have hgradχc : Continuous (gradient χ) := hv1.continuous
  have hgradUc : Continuous
      (gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ)) :=
    (s45_contDiff_gradient hU2).continuous
  have hInnerMeas : Measurable innerTerm := by
    change Measurable (fun x => ⟪gradient χ x,
      gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ) x⟫)
    exact (hgradχc.inner hgradUc).measurable
  have hBU0 : 0 ≤ BU := hT.BU0
  have hInnerBound : ∀ x, |innerTerm x| ≤ B1 * BU := by
    intro x
    calc
      |innerTerm x| ≤ ‖gradient χ x‖ *
          ‖gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ) x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ B1 * BU := by
        calc
          _ ≤ B1 * ‖gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ) x‖ :=
            mul_le_mul_of_nonneg_right (hB1 x) (norm_nonneg _)
          _ ≤ B1 * BU := mul_le_mul_of_nonneg_left (hT.gradU_le x) hB10
  have hInnerInt : Integrable innerTerm μ :=
    Integrable.of_bound hInnerMeas.aestronglyMeasurable (B1 * BU)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hInnerBound x)
  have hPoint : ∀ x, row x = innerTerm x + rawTerm x := by
    intro x
    dsimp [row, innerTerm, rawTerm, h, μ]
    exact S47.s47_corr_identity hd hs0 hsd hT hχ hB1 hB2 x
  have hrawEq : rawTerm =ᵐ[μ] fun x => row x - innerTerm x := by
    filter_upwards with x
    rw [hPoint x]
    ring
  have hrawInt : Integrable rawTerm μ :=
    (hrowInt.sub hInnerInt).congr hrawEq.symm
  have hrowIntegral :
      (∫ x, row x ∂μ) = (∫ x, innerTerm x ∂μ) + ∫ x, rawTerm x ∂μ := by
    calc
      _ = ∫ x, innerTerm x + rawTerm x ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hPoint x)
      _ = _ := integral_add hInnerInt hrawInt
  have hSymm := fp81s21_initial_integral_kernel_gen_symm hT hs0 hsd hχ hB1 hB2 hgen2
  have hIBP := fp81s21_initial_ibp_potential hT hχ hB1 hB2
  have hSymm' : (∫ x, rawTerm x ∂μ) =
      ∫ x, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ x *
        HRS.Whole.weightedGen ρ χ x ∂μ := by
    simpa [rawTerm, μ] using hSymm
  have hIBP' : (∫ x, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ x *
      HRS.Whole.weightedGen ρ χ x ∂μ) = ∫ x, innerTerm x ∂μ := by
    simpa [innerTerm, μ] using hIBP
  calc
    ∫ x, ∫ y, HRS.Whole.commutatorKernel d s (gradient χ) x y ∂μ ∂μ =
        (∫ x, innerTerm x ∂μ) + ∫ x, rawTerm x ∂μ := by
      simpa [row, h, μ] using hrowIntegral
    _ = 2 * ∫ x, innerTerm x ∂μ := by
      rw [hSymm', hIBP']
      ring

#print axioms fp81s21_initial_integral_commutator_half

end HRS.Fp81.S21

end
