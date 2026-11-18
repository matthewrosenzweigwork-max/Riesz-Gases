import HRS.MS.Fp81S21InitialUncentered4

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
open HRS.MS.R26T3

/-- The weighted generator of a bounded-gradient, bounded-Hessian corrector has zero
reference mean. This extracts the `hmean` argument inside `S47.s47_cov_identity`, using
`S47.s47_ibp_mu` with the constant test function. -/
theorem fp81s21_initial_integral_weightedGen_zero
    {d : ℕ} {s q C c BU BB : ℝ} {ρ : Euc d → ℝ} {Bd : Euc d → Euc d}
    (hT : S47.TRef d s ρ q C c BU BB Bd)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) :
    ∫ y : Euc d, HRS.Whole.weightedGen ρ χ y
      ∂(HRS.Whole.withDensityReal ρ) = 0 := by
  have h := S47.s47_ibp_mu hT hχ hB1 hB2
    (φ := fun _ => (1 : ℝ)) contDiff_const (Bφ := 1) (Dφ := 0)
    (fun _ => by simp) (fun _ => by simp)
  simpa using h

/-- The normalized Gibbs integration-by-parts identity at the actual initial law, before any
particle mean is subtracted. This is `S47.s47_gibbs_ibp` with the constant configuration test. -/
theorem fp81s21_initial_gibbs_ibp_one
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (E : InitialSteinEnv R) (hγ : 0 < p.γ) {N : ℕ} (hN : 2 ≤ N)
    {ψ χ : Euc p.d → ℝ} {Bχ : ℝ}
    (hχ : S47.S47Feat p.d p.s (R.ρ 0) p.γ ψ χ Bχ) :
    ∫ X, (∑ k, S45.s45_div (gradient χ) (X k) -
      ((∑ i, (p.a * p.β * ⟪X i, gradient χ (X i)⟫ -
        (⟪E.Bd (X i), gradient χ (X i)⟫ +
          p.γ * ⟪gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel p.d p.s)
            (HRS.Whole.withDensityReal (R.ρ 0))) (X i), gradient χ (X i)⟫)) +
        p.γ * ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪HRS.Whole.rieszKernelGrad p.d p.s (X i - X j),
            gradient χ (X i) - gradient χ (X j)⟫)))) ∂(r26t3_Q R N) = 0 := by
  have hN1 : 1 ≤ N := by omega
  have hd1 : 1 ≤ p.d := Nat.le_trans (by omega) p.hd
  have hq : 0 < p.a * p.β := mul_pos p.ha p.hβ
  let G : EucConfig p.d N → ℝ := fun X =>
    (∑ k, S45.s45_div (gradient χ) (X k)) -
      ((∑ i, (p.a * p.β * ⟪X i, gradient χ (X i)⟫ -
        (⟪E.Bd (X i), gradient χ (X i)⟫ +
          p.γ * ⟪gradient (HRS.Whole.convMeasure (HRS.Whole.rieszKernel p.d p.s)
            (HRS.Whole.withDensityReal (R.ρ 0))) (X i), gradient χ (X i)⟫)) +
        p.γ * ((1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          ⟪HRS.Whole.rieszKernelGrad p.d p.s (X i - X j),
            gradient χ (X i) - gradient χ (X j)⟫)))
  have hP : IsProbabilityMeasure (S47.s47_P p.d p.s (R.ρ 0) p.γ N) :=
    (E.static N hN).prob
  have hg : Measurable (rieszKernel p.d p.s : Euc p.d → ℝ) :=
    S47.s47_kernel_measurable p.s
  have hV : Measurable (S47.s47_V0 p.d p.s (R.ρ 0) p.γ) :=
    (measurable_const.mul (Real.measurable_log.comp E.reference.smooth.continuous.measurable)).sub
      E.reference.Usmooth.continuous.measurable
  have hRaw := S47.s47_gibbs_ibp hd1 p.hs0 hq hγ E.reference hN1
    (s45_contDiff_gradient hχ.smooth) hχ.B1 hχ.B2
    (F := fun _ : EucConfig p.d N => (1 : ℝ)) contDiff_const
    (BF := 1) (DF := 0) (fun _ => by simp) (fun _ => by simp)
  have hRaw' : ∫ X, G X * Real.exp (-p.γ *
      HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel p.d p.s)
        (S47.s47_V0 p.d p.s (R.ρ 0) p.γ) X) = 0 := by
    simpa [G] using hRaw
  calc
    ∫ X, G X ∂(r26t3_Q R N) =
        ∫ X, G X ∂(S47.s47_P p.d p.s (R.ρ 0) p.γ N) := by
          rw [E.law_eq N]
    _ = (HRS.Whole.canonicalPartition (HRS.Whole.rieszKernel p.d p.s)
          (S47.s47_V0 p.d p.s (R.ρ 0) p.γ) N p.γ)⁻¹ *
        ∫ X, G X * Real.exp (-p.γ *
          HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel p.d p.s)
            (S47.s47_V0 p.d p.s (R.ρ 0) p.γ) X) :=
      S45.s45_integral_P hg hV hP G
    _ = 0 := by rw [hRaw']; simp

#print axioms fp81s21_initial_integral_weightedGen_zero
#print axioms fp81s21_initial_gibbs_ibp_one

end HRS.Fp81.S21

end
