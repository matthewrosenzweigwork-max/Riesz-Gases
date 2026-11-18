import HRS.MS.SA16Y4Id1
import HRS.MS.SA16SHw5
import HRS.MS.SA16Y3L3

/-!
# S.A.16 (SA16Y4) Id2: the limit integrand is the forward weak term

`sa16y4_flim_eq`: for `F σ = wrep (G0)` a.e. (here: equal as functions) the limit integrand
`ν ℓ_{Δψ}(G0) - ∫ wrep G0 · div(bψ) - ∫ wrep G0 · nonlocalTestRd C (t-σ) ψ` of `sa16y4_f_tendsto` equals
`forwardWeakTerm C t F ψ σ` (`C.ν = ν`, drift `b = C.drift (t-σ)` with differentiable components).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Id2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y4_flim_eq {m : ℕ} (C : WholeCoeff d) (t σ : ℝ) (F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (G0 : WmpSpace d m p) (hF : F σ = fun x => wrep d m p G0 x) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : IsCcInfty ψ) (hdiff : ∀ k, Differentiable ℝ (fun y => C.drift (t - σ) y k)) :
    C.ν * sa16r_ell d m p (sa16sw_cc_lap hψ) G0 -
        (∫ x, wrep d m p G0 x * sa16so_divFun (fun i y => C.drift (t - σ) y i) ψ x) -
        ∫ x, wrep d m p G0 x * nonlocalTestRd C (t - σ) ψ x =
      forwardWeakTerm C t F ψ σ := by
  unfold forwardWeakTerm
  rw [hF, sa16r_ell_apply]
  have h1 : ∀ x, sa16so_divFun (fun i y => C.drift (t - σ) y i) ψ x =
      movDiv (fun y => ψ y • C.drift (t - σ) y) x := fun x =>
    (sa16y4_movDiv_eq hdiff (hψ.1.differentiable (by simp)) x).symm
  simp_rw [h1]
  congr 2
  rw [sa16sw_lap_eq hψ.1]

end Id2

end HRS.Whole.AppendixA.Phase2SA16R
