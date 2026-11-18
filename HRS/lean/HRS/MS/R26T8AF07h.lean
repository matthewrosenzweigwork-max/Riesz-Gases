import HRS.MS.R26T8AF07g

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07h): smoothness of the local generator

For `g` smooth and the smooth thermal force `F = forceMean ρ` (coordinates smooth), `localP g` is smooth.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07h_contDiff_localP (a beta : ℝ) (rho : Euc d → ℝ)
    (hF : ∀ j : Fin d, ContDiff ℝ ∞ (fun x => forceMean rho x j))
    (g : Euc d → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => r26t8a_localP a beta rho g x) := by
  have hlap : ContDiff ℝ ∞ (fun x => Laplacian.laplacian g x) := by
    have e : (fun x => Laplacian.laplacian g x) = fun x => ∑ i : Fin d, r26t8a_l3_D i (r26t8a_l3_D i g) x :=
      funext fun x => r26t8a_f07c_lap g hg x
    rw [e]
    refine ContDiff.sum fun i _ => ?_
    exact r26t8a_l3_contDiff_D i _ (r26t8a_l3_contDiff_D i g hg)
  have hgf : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have hE : ContDiff ℝ ∞ (fun x => fderiv ℝ g x x) :=
    hgf.clm_apply contDiff_id
  have hgrad : ContDiff ℝ ∞ (fun x => gradient g x) := by
    have e : (fun x => gradient g x) = fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ g x) :=
      rfl
    rw [e]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp hgf
  have hin : ContDiff ℝ ∞ (fun x => inner ℝ (forceMean rho x) (gradient g x)) := by
    have e : (fun x => inner ℝ (forceMean rho x) (gradient g x)) =
        fun x => ∑ j : Fin d, forceMean rho x j * gradient g x j := by
      funext x
      rw [r26t8a_f07e_inner]
    rw [e]
    refine ContDiff.sum fun j _ => ?_
    refine ContDiff.mul (hF j) ?_
    exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).contDiff.comp hgrad
  unfold r26t8a_localP
  exact ((contDiff_const.mul hlap).sub (contDiff_const.mul hE)).sub hin

end HRS.MS.R26T8A

end
