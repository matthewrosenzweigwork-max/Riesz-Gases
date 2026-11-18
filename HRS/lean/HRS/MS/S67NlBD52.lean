import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.WhoAux8

/-!
# S6.7 nonlinear, packet S6.7nl.52: measurable derivative evaluations from measurable values

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4835-4841, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
Induction on the derivative order: each coordinate evaluation of the next derivative is the
a.e. limit of difference quotients of the previous jet at countably many shifted points; the
a.e. differentiability comes from the a.e. `C^K` hypothesis.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_derivative_time_measurable (d K : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (G : ℝ → Euc d → ℝ)
    (hG : ∀ x, AEStronglyMeasurable (fun t => G t x) (volume.restrict (Icc (0 : ℝ) τ)))
    (hGK : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) τ)), ContDiff ℝ (K : WithTop ℕ∞) (G t)) :
    ∀ i ≤ K, ∀ x : Euc d,
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ i (G t) x)
        (volume.restrict (Icc (0 : ℝ) τ)) := by
  intro i
  induction i with
  | zero =>
    intro _ x
    have : (fun t => iteratedFDeriv ℝ 0 (G t) x) =
        fun t => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (G t x) := by
      funext t; rw [iteratedFDeriv_zero_eq_comp]; rfl
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.continuous.comp_aestronglyMeasurable
      (hG x)
  | succ i ih =>
    intro hi x
    have hik : i ≤ K := by omega
    have hdiff : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) τ)),
        DifferentiableAt ℝ (iteratedFDeriv ℝ i (G t)) x := by
      filter_upwards [hGK] with t ht
      exact (ht.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : i < K))) x
    have hfd : AEStronglyMeasurable (fun t => fderiv ℝ (iteratedFDeriv ℝ i (G t)) x)
        (volume.restrict (Icc (0 : ℝ) τ)) := by
      set E := ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ
      have hcomp : ∀ l : Fin d, AEStronglyMeasurable (fun t =>
          fderiv ℝ (iteratedFDeriv ℝ i (G t)) x (EuclideanSpace.single l 1))
          (volume.restrict (Icc (0 : ℝ) τ)) := fun l => by
        refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (n : ℕ) (t : ℝ) =>
          ((n : ℝ) + 1) • (iteratedFDeriv ℝ i (G t)
              (x + (1 / ((n : ℝ) + 1)) • EuclideanSpace.single l (1 : ℝ)) -
            iteratedFDeriv ℝ i (G t) x)) (fun n => ((ih hik _).sub (ih hik x)).fun_const_smul _) ?_
        filter_upwards [hdiff] with t ht
        exact HRS.MS.Who.who_slope_tendsto ht l
      have hfun : (fun t => fderiv ℝ (iteratedFDeriv ℝ i (G t)) x) = fun t =>
          ∑ l : Fin d, ((ContinuousLinearMap.smulRightL ℝ (Euc d) E)
            (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ))
            (fderiv ℝ (iteratedFDeriv ℝ i (G t)) x (EuclideanSpace.single l 1)) := by
        funext t
        conv_lhs => rw [HRS.MS.Who.who_clm_decomp (fderiv ℝ (iteratedFDeriv ℝ i (G t)) x)]
        rfl
      rw [hfun]
      exact Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
        ((ContinuousLinearMap.smulRightL ℝ (Euc d) E)
          (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable (hcomp l)
    have : (fun t => iteratedFDeriv ℝ (i + 1) (G t) x) = fun t =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ i (G t)) x) := by
      funext t; rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [this]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d)
      ℝ).symm.continuous.comp_aestronglyMeasurable hfd

end HRS.MS.BreakdownS67
