import HRS.MS.S82P2Local
import HRS.MS.WsStatAux5
import HRS.MS.WadAux14

/-!
# S8.2 A02 (S82V), part 4: oddness of the force, symmetry of the pair gradients, drift formulas
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82v_fderiv_comp_neg (g : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ (fun y => g (-y)) x = -fderiv ℝ g (-x) := by
  by_cases hg : DifferentiableAt ℝ g (-x)
  · have h1 : HasFDerivAt (fun y : Euc d => -y) (-ContinuousLinearMap.id ℝ (Euc d)) x :=
      (hasFDerivAt_id x).neg
    have h2 := (hg.hasFDerivAt).comp x h1
    have : fderiv ℝ (fun y => g (-y)) x = (fderiv ℝ g (-x)).comp (-ContinuousLinearMap.id ℝ (Euc d)) :=
      h2.fderiv
    rw [this]
    ext v; simp
  · have hg' : ¬ DifferentiableAt ℝ (fun y => g (-y)) x := by
      intro h
      apply hg
      have h3 : DifferentiableAt ℝ (fun y : Euc d => -y) (-x) := differentiableAt_id.neg
      have h5 : DifferentiableAt ℝ (fun y => g (-y)) (-(-x)) := by rwa [neg_neg]
      have h4 := DifferentiableAt.comp (-x) h5 h3
      convert h4 using 1
      funext y; simp
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
    simp

/-- The Riesz force is odd. -/
lemma s82v_force_neg (s : ℝ) (z : Euc d) :
    rieszKernelGrad d s (-z) = -rieszKernelGrad d s z := by
  have h : ∀ x : Euc d, rieszKernel d s (-x) = rieszKernel d s x := fun x => by
    unfold rieszKernel; rw [norm_neg]
  have e : rieszKernel d s = fun x => rieszKernel d s (-x) := funext fun x => (h x).symm
  have key : ∀ w : Euc d, rieszKernelGrad d s w = -rieszKernelGrad d s (-w) := by
    intro w
    unfold rieszKernelGrad gradient
    conv_lhs => rw [e]
    rw [s82v_fderiv_comp_neg]
    simp
  have := key (-z)
  rw [neg_neg] at this
  exact this

lemma s82v_pairGradY_eq {F : Euc d → Euc d → ℝ} (hsym : ∀ x y, F x y = F y x) (x y : Euc d) :
    pairGradY F x y = pairGradX F y x := by
  unfold pairGradY pairGradX
  have : F x = fun x' => F x' x := funext fun y' => hsym x y'
  rw [this]

lemma s82v_gradV (a beta : ℝ) (x : Euc d) :
    gradient (quadraticGradientDyn d (criticalS d) a beta).V x = a • x := by
  show gradient (confinement a) x = a • x
  exact HRS.MS.Wad.s83_gradient_confinement a x

/-- The mean-field drift of the critical coefficients. -/
lemma s82v_drift (a beta : ℝ) (rho : Euc d → ℝ) (x : Euc d) :
    (critCoeff d a beta rho).drift 0 x = -Phase2S82.forceMean rho x - a • x := by
  show Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) rho x) - gradient (confinement a) x = _
  rw [HRS.MS.S21.s21_matVec_neg_one, HRS.MS.Wad.s83_gradient_confinement]
  rfl

lemma s82v_nu (a beta : ℝ) (rho : Euc d → ℝ) : (critCoeff d a beta rho).ν = beta⁻¹ := rfl

/-- The particle drift. -/
lemma s82v_particleDrift {N : ℕ} (a beta : ℝ) (X : EucConfig d N) (i : Fin N) :
    particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i =
      (-(1 / (N : ℝ))) • ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d (criticalS d) (X i - X j) -
        a • X i := by
  unfold particleDriftW
  rw [s82v_gradV a beta]
  have : ∀ j, Torus.matVec (quadraticGradientDyn d (criticalS d) a beta).M
      (rieszKernelGrad d (quadraticGradientDyn d (criticalS d) a beta).s (X i - X j)) =
      -rieszKernelGrad d (criticalS d) (X i - X j) := fun j =>
    HRS.MS.S21.s21_matVec_neg_one _
  simp_rw [this]
  rw [Finset.sum_neg_distrib, smul_neg, neg_smul]

end HRS.MS.S82V

end
