import HRS.MS.S111X2Aux22

/-!
# S11.1 X2, packet E05/H01 at the level of pairs: decay of the window-covariance difference

`s111x2_quench_ge`: the quench identity for `0 ≤ r ≤ t` (including `r = 0`).
`s111x2_pair_diff`: for classical solutions `f` (datum `φ`, horizon `u+t₁`) and `g` (datum `ψ`, horizon `u+t₂`),
`|Cov_γ(u+t₁,u+t₂)(φ,ψ) - Cov_β(t₁,t₂)(φ,ψ)| ≤ 2 η⁻¹ e^{-2(λ/β)u} ‖P φ‖ ‖P ψ‖` for the exact covariances
`linearGaussianCov` of the quench started at `R_γ` at time `u` versus the stationary one: the sharp rate for one pair of
observations (no time supremum and no sum over observations yet: these are the remaining H01/H02 steps).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- The quench identity for `0 ≤ r ≤ t`. -/
theorem s111x2_quench_ge (hd : 2 ≤ d) {s a β γ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    {φ ψ : Euc d → ℝ} {f h' : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r φ f)
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t ψ h') :
    linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ) r t φ ψ =
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β φ
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t ψ) +
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 r φ)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t ψ) -
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 r φ)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t ψ) := by
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
    have hU : propagatorW C 0 0 φ = φ := by
      rw [s111x2_prop_eq hd hs0 hs ha hβ hρ le_rfl hf ⟨le_rfl, le_rfl⟩]
      exact hf.terminal
    unfold linearGaussianCov noiseCovW
    rw [min_eq_left (le_trans le_rfl hrt), hU]
    have : ∫ s' in Icc (0 : ℝ) 0, ∫ x, inner ℝ (gradient (propagatorW C s' 0 φ) x)
        (gradient (propagatorW C s' t ψ) x) * C.ρ s' x = 0 := by
      rw [Icc_self]
      exact setIntegral_measure_zero _ (by simp)
    rw [this]
    ring
  · exact s111x2_quench hd hs0 hs ha hβ hρ hpos hrt hf hh

/-- Bound of the susceptibility form by centered norms. -/
theorem s111x2_susc_le {μ : MeasureTheory.Measure (Euc d)} {g : Euc d → ℝ} {θ η : ℝ}
    (RF : ResponseForm g μ θ η) {u v : Euc d → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    |HRS.Whole.susceptibilityCov g μ θ u v| ≤
      Real.sqrt (s111x2_centeredSquare μ u) * Real.sqrt (s111x2_centeredSquare μ v) :=
  RF.schwarz u v hu hv

end HRS.MS.S111X2
