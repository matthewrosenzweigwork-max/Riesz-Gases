import HRS.MS.R2InterpAux6
import HRS.Whole.AppendixA

/-!
# S10.2 (worker S102), part 7 (packet F2): the fluctuation interaction is minus the pair energy of the commutator kernel

For `D.M = -1` (the gradient dynamics), a collision-free configuration `X` and a density `ρ`:
`flucInteractionRd D ψ X ρ = - pairEnergy (commutatorKernel d D.s ∇ψ) X (ρ dx)`, hence `√N flucInteractionRd = -N^{-1/2} (N pairEnergy)`,
the sign and scaling of the term `-N^{-1/2} E A` of `r2_path_interpolation` (`r2QuadField = N (pairEnergy - E pairEnergy)`).
The integrability hypotheses are those that make the Bochner integrals genuine (cf. `GibbsWellDefined.conv_integrable`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d N : ℕ}

theorem s102_fderiv_even {f : Euc d → ℝ} (hf : ∀ x, f (-x) = f x) (z : Euc d) :
    fderiv ℝ f z = - fderiv ℝ f (-z) := by
  have hfun : (fun x => f (-x)) = f := funext hf
  by_cases h : DifferentiableAt ℝ f (-z)
  · have h2 : HasFDerivAt (fun x => f (-x)) ((fderiv ℝ f (-z)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) z :=
      HasFDerivAt.comp z (h.hasFDerivAt : HasFDerivAt f (fderiv ℝ f (-z)) (-z)) (hasFDerivAt_id z).neg
    rw [hfun] at h2
    rw [h2.fderiv]
    ext v
    simp
  · have h3 : ¬ DifferentiableAt ℝ f z := by
      intro hz
      apply h
      have h4 : DifferentiableAt ℝ (fun x => f (-x)) (-z) :=
        DifferentiableAt.comp (-z) (by simpa using hz) differentiableAt_id.neg
      rw [hfun] at h4
      exact h4
    rw [fderiv_zero_of_not_differentiableAt h3, fderiv_zero_of_not_differentiableAt h]
    simp

theorem s102_rieszKernelGrad_neg (s : ℝ) (z : Euc d) :
    rieszKernelGrad d s (-z) = - rieszKernelGrad d s z := by
  have he : ∀ x : Euc d, rieszKernel d s (-x) = rieszKernel d s x := by
    intro x; simp [rieszKernel]
  have h1 := s102_fderiv_even he z
  unfold rieszKernelGrad gradient
  rw [h1]
  simp

/-- The commutator kernel is symmetric. -/
theorem s102_commutatorKernel_symm (s : ℝ) (v : Euc d → Euc d) (x y : Euc d) :
    commutatorKernel d s v x y = commutatorKernel d s v y x := by
  unfold commutatorKernel
  have : x - y = -(y - x) := by abel
  rw [this, s102_rieszKernelGrad_neg, inner_neg_right, ← inner_neg_left, neg_sub]

theorem s102_commutatorKernel_diag (s : ℝ) (v : Euc d → Euc d) (x : Euc d) :
    commutatorKernel d s v x x = 0 := by
  simp [commutatorKernel]

theorem s102_matVec_neg_one (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

/-- The interaction pairing for `M = -1`. -/
theorem s102_interactionPairing_eq (D : WholeDyn d) (hM : D.M = -1) (ψ : Euc d → ℝ) (ν ν' : Measure (Euc d)) :
    interactionPairingW D ψ ν ν' =
      -(1 / 2) * ∫ x, ∫ y, commutatorKernel d D.s (fun z => gradient ψ z) x y ∂ν' ∂ν := by
  unfold interactionPairingW
  have hk : ∀ x y : Euc d, (if x = y then (0 : ℝ) else
      inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))) =
      -commutatorKernel d D.s (fun z => gradient ψ z) x y := by
    intro x y
    by_cases h : x = y
    · subst h; simp [commutatorKernel]
    · rw [if_neg h, hM, s102_matVec_neg_one, inner_neg_right]
      rfl
  simp_rw [hk, integral_neg]
  ring

theorem s102_flucInteractionRd_eq (D : WholeDyn d) (hM : D.M = -1) (hN : 0 < N) (ψ : Euc d → ℝ)
    (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) (ρ : Euc d → ℝ)
    (hint : ∀ a : Euc d, Integrable (fun y => commutatorKernel d D.s (fun z => gradient ψ z) a y)
      (HRS.Whole.withDensityReal ρ)) :
    flucInteractionRd D ψ X ρ =
      -pairEnergy (commutatorKernel d D.s (fun z => gradient ψ z)) X (HRS.Whole.withDensityReal ρ) := by
  set h := commutatorKernel d D.s (fun z => gradient ψ z) with hh
  have hsymm : ∀ x y, h x y = h y x := fun x y => s102_commutatorKernel_symm _ _ x y
  have hinj : ∀ i j, i ≠ j → X i ≠ X j := by
    intro i j hij hXij
    exact hX ⟨i, j, hij, hXij⟩
  have hE : ∀ f : Euc d → ℝ, ∫ x, f x ∂(HRS.Whole.empirical X) = (N : ℝ)⁻¹ * ∑ i, f (X i) :=
    fun f => HRS.Whole.pair_empirical hN X f
  have e_ee : ∫ x, ∫ y, h x y ∂(HRS.Whole.empirical X) ∂(HRS.Whole.empirical X) =
      (N : ℝ)⁻¹ * ∑ i, ((N : ℝ)⁻¹ * ∑ j, h (X i) (X j)) := by
    rw [hE]
    simp_rw [hE]
  have e_er : ∫ x, ∫ y, h x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.empirical X) =
      (N : ℝ)⁻¹ * ∑ i, ∫ y, h (X i) y ∂(HRS.Whole.withDensityReal ρ) := hE _
  have e_re : ∫ x, ∫ y, h x y ∂(HRS.Whole.empirical X) ∂(HRS.Whole.withDensityReal ρ) =
      (N : ℝ)⁻¹ * ∑ i, ∫ y, h (X i) y ∂(HRS.Whole.withDensityReal ρ) := by
    simp_rw [hE]
    rw [integral_const_mul, integral_finset_sum]
    · simp_rw [hsymm _ (X _)]
    · intro j _
      simp_rw [hsymm _ (X j)]
      exact hint (X j)
  have hd0 : ∀ x, h x x = 0 := fun x => s102_commutatorKernel_diag _ _ x
  have hdiag : ∀ i, ∑ j, h (X i) (X j) = ∑ j ∈ Finset.univ.erase i, h (X i) (X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hd0, zero_add]
  unfold flucInteractionRd pairEnergy
  simp only [s102_interactionPairing_eq D hM]
  simp only [← hh]
  simp only [e_ee, e_er, e_re]
  simp_rw [hdiag]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Finset.mul_sum]
  field_simp
  ring

end HRS.MS.R2Interp

end
