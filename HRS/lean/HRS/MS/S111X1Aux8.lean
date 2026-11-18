import HRS.MS.S111X1Aux7

/-!
# S11.1 X1, part 8: the `L²(μ)` bound and the assembly of `S111CovCore` from the analytic input
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ} {s a β γ : ℝ} {ρ : Euc d → ℝ}

theorem X1Input.F_bound (h : X1Input d s a β γ ρ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d : ℝ) φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d : ℝ) ψ →
      |Fcov d s a β γ ρ r t φ ψ| ≤ B * Real.sqrt (∫ x, ψ x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  haveI := h.finite
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨cr, hcr, hen⟩ := h.energy r hr
  have cφ := x1_prop_classical (h.exist t ht φ hφ)
  have ht0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  set Uφ := fun u => propagatorW (x1C d s a β ρ) u t φ with hUφ
  set A : ℝ := Real.sqrt (∫ x, HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ γ (Uφ 0) x ^ 2 ∂μ) with hA
  set G : ℝ := ∫ u in Set.Icc (0 : ℝ) t, ∫ x, inner ℝ (gradient (Uφ u) x) (gradient (Uφ u) x) * ρ x
    with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg measurableSet_Icc fun u _ => integral_nonneg fun x =>
    mul_nonneg real_inner_self_nonneg (h.nonneg x)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨Real.sqrt cr * (A + 2 * |β⁻¹| * Real.sqrt G), by positivity, fun ψ hψ => ?_⟩
  have cψ := x1_prop_classical (h.exist r hr ψ hψ)
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) r := ⟨le_rfl, hr⟩
  set Uψ := fun u => propagatorW (x1C d s a β ρ) u r ψ with hUψ
  obtain ⟨en1, en2⟩ := hen ψ hψ Uψ cψ
  set X : ℝ := ∫ x, ψ x ^ 2 ∂μ with hX
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hsq : Real.sqrt (cr * X) = Real.sqrt cr * Real.sqrt X := Real.sqrt_mul hcr X
  unfold Fcov HRS.Whole.linearGaussianCov
  -- first term
  have T1 : |HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ γ
      (propagatorW (x1C d s a β ρ) 0 r ψ) (propagatorW (x1C d s a β ρ) 0 t φ)| ≤
      Real.sqrt cr * Real.sqrt X * A := by
    refine (x1_suscept_bound _ μ γ (x1_classical_memLp cψ hr0 μ)).trans ?_
    rw [← hsq]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt en1) hA0
  -- second term
  have hN := x1_noise_sq_le cψ cφ h.int h.nonneg
  set Nmix := ∫ u in Set.Icc (0 : ℝ) (min r t), ∫ x,
    inner ℝ (gradient (Uψ u) x) (gradient (Uφ u) x) * ρ x with hNmix
  have hNψ : (0 : ℝ) ≤ ∫ u in Set.Icc (0 : ℝ) r, ∫ x,
      inner ℝ (gradient (Uψ u) x) (gradient (Uψ u) x) * ρ x :=
    setIntegral_nonneg measurableSet_Icc fun u _ => integral_nonneg fun x =>
      mul_nonneg real_inner_self_nonneg (h.nonneg x)
  have hN2 : Nmix ^ 2 ≤ cr * X * G :=
    hN.trans (mul_le_mul_of_nonneg_right en2 hG0)
  have hN3 : |Nmix| ≤ Real.sqrt cr * Real.sqrt X * Real.sqrt G := by
    rw [← hsq, ← Real.sqrt_mul (mul_nonneg hcr hX0)]
    exact Real.abs_le_sqrt hN2
  have T2 : |noiseCovW (x1C d s a β ρ) β⁻¹ r t ψ φ| ≤
      2 * |β⁻¹| * (Real.sqrt cr * Real.sqrt X * Real.sqrt G) := by
    unfold HRS.Whole.noiseCovW
    have : (∫ u in Set.Icc (0 : ℝ) (min r t), ∫ x,
        inner ℝ (gradient (propagatorW (x1C d s a β ρ) u r ψ) x)
          (gradient (propagatorW (x1C d s a β ρ) u t φ) x) * (x1C d s a β ρ).ρ u x) = Nmix := rfl
    rw [this, abs_mul, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left hN3 (by positivity)
  calc _ ≤ |HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ γ
        (propagatorW (x1C d s a β ρ) 0 r ψ) (propagatorW (x1C d s a β ρ) 0 t φ)| +
        |noiseCovW (x1C d s a β ρ) β⁻¹ r t ψ φ| := abs_add_le _ _
    _ ≤ Real.sqrt cr * Real.sqrt X * A + 2 * |β⁻¹| * (Real.sqrt cr * Real.sqrt X * Real.sqrt G) :=
        add_le_add T1 T2
    _ = _ := by ring

end HRS.MS.S111X1
