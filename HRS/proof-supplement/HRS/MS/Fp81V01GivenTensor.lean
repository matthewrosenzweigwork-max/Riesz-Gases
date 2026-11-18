import HRS.MS.S111TermAux8
import HRS.MS.GenPathAux47

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.S111T

variable {d : ℕ} {s a β γ T u : ℝ} {ρ : Euc d → ℝ}

/-- The tensor represented by a physical cubic source is the given path cubic tensor. -/
theorem fp81v01_given_tensor_eq
    (hT : 0 < T) (hu : 0 ≤ u) {K K' : projTensor (R2X d T) 3}
    (hK : IsR2PathCubic d s a β γ ρ T u K)
    (S : PhysicalCubicSources d s a β γ ρ T u K') :
    K = K' := by
  classical
  have hcoord : ∀ (tau : Fin 3 → Set.Icc (0 : ℝ) T)
      (alpha : Fin 3 → MultiIndex d)
      (M : (R2X d T) [×3]→L[ℝ] ℝ),
      (∀ w : Fin 3 → R2X d T,
        M w = ∏ i, OscDual.coord (OscPath.at' (w i) (tau i)) (alpha i)) →
      (K : TensorDual (R2X d T) 3) M = (K' : TensorDual (R2X d T) 3) M := by
    intro tau alpha M hM
    let phi : Fin 3 → Euc d → ℝ := fun i => oscTestFun (wholeSpaceIndex d) (alpha i)
    have hphi : ∀ i, IsOscTest (wholeSpaceIndex d) (phi i) := by
      intro i
      exact HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d) (alpha i)
    let N : (R2X d T) [×3]→L[ℝ] ℝ :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap
        (fun i => HRS.MS.R2Interp.s102_ell (T := T) (m := wholeSpaceIndex d) (tau i) (alpha i))
    have hNcoord : ∀ w : Fin 3 → R2X d T,
        N w = ∏ i, OscDual.coord (OscPath.at' (w i) (tau i)) (alpha i) := by
      intro w
      simp [N, HRS.MS.R2Interp.s102_ell_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
    have hNeval : ∀ w : Fin 3 → R2X d T,
        N w = ∏ i, OscDual.eval (OscPath.at' (w i) (tau i)) (phi i) := by
      intro w
      simp [N, phi, HRS.MS.R2Interp.s102_ell_apply,
        OscDual.eval_oscTestFun,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
    have hMN : M = N := by
      apply ContinuousMultilinearMap.ext
      intro w
      rw [hM, hNcoord]
    obtain ⟨chi, hchi⟩ := hK.2.1 tau phi hphi
    have hformula := hK.2.2 tau phi hphi chi hchi N hNeval
    have hterm : u + T ∈ Set.Icc (0 : ℝ) (u + T) := by
      constructor
      · linarith
      · exact le_rfl
    have hinitial := S.initial_eval tau phi hphi N hNeval
    have hdrift := S.drift_eval tau phi hphi chi hchi N hNeval (u + T) hterm
    have hcov := S.covariance_eval tau phi hphi chi hchi N hNeval (u + T) hterm
    have hrep : K' = S.toCubicSources.initial + S.toCubicSources.drift (u + T) +
        S.toCubicSources.covariance (u + T) := S.toCubicSources.represents
    have hK'N : (K' : TensorDual (R2X d T) 3) N = cubicFormula
        (quadraticGradientDyn d s a β) (fun _ => ρ) β γ (HRS.Whole.withDensityReal ρ)
        (fun i => u + (tau i : ℝ)) phi chi := by
      rw [hrep]
      change (((S.toCubicSources.initial : TensorDual (R2X d T) 3) +
        (S.toCubicSources.drift (u + T) : TensorDual (R2X d T) 3)) +
        (S.toCubicSources.covariance (u + T) : TensorDual (R2X d T) 3)) N = _
      rw [add_apply, add_apply]
      rw [hinitial, hdrift, hcov]
      simp [cubicFormula, HRS.Whole.quadraticGradientDyn, fun i => (tau i).2.2]
      <;> ring
    rw [hMN]
    calc (K : TensorDual (R2X d T) 3) N
        = cubicFormula (quadraticGradientDyn d s a β) (fun _ => ρ) β γ
            (HRS.Whole.withDensityReal ρ) (fun i => u + (tau i : ℝ)) phi chi := hformula.1
      _ = (K' : TensorDual (R2X d T) 3) N := hK'N.symm

  exact s111t_cubic_coordinates_determine d T hT K K' hcoord

#print axioms fp81v01_given_tensor_eq

end HRS.Fp81.V01
