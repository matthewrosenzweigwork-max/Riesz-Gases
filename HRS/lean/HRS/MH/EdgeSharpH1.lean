import HRS.MH.EdgeSharpDefs
import HRS.MH.EdgeSharpC3b
import HRS.MH.EdgeSharpD4
import HRS.MH.EdgeSharpEF
import HRS.MH.EdgeSharpE2K2
import HRS.Sections.Q40bAux2
import HRS.MD.EQGaussLyapDet
import HRS.MD.EQEvoUnif

/-!
# EdgeSharp packet H1 (statement-verbatim copy of `HRS/MH/EdgeSharpSpec.lean`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

variable {d : ℕ}

theorem cross_cov_density (S : PreparedData d) (m T : ℝ) (hV : S.V = fun _ => 0) (hρ0 : S.ρ0 = fun _ => 1)
    (k : Lattice d) (hk : k ≠ 0) (b : ℝ)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s S.β S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (0 + T) ν P' Z₀ Z) :
    ∀ r ∈ Set.Icc (0 : ℝ) (0 + T), ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      ∫ x, ψ x * crossDensity d S.s S.β k b r x =
        ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z 0 ω) (phi0 k b) ∂P' := by
  intro r hr ψ hψ
  have hr' : r ∈ Set.Icc (0 : ℝ) (0 + T) := hr
  have hd1 : 1 ≤ d := by have := S.hd; omega
  have hρ1 : ∀ r' ∈ Set.Icc 0 r, S.ρ r' = (fun _ => (1 : Torus d → ℝ)) r' :=
    fun r' h => meanField_density_eq_one S hV hρ0 r' h.1
  have hdyn : S.dyn = PDE.mfData d S.s S.hs0 S.hsd (fun _ => 0) S.β S.hβ := by
    unfold PreparedData.dyn; rw [hV]
  have hU : propagator S.dyn S.ρ 0 r ψ =
      propagator (PDE.mfData d S.s S.hs0 S.hsd (fun _ => 0) S.β S.hβ) (fun _ => 1) 0 r ψ := by
    rw [hdyn]; exact HRS.Q40b.q40b_propagator_congr hρ1 0 ψ
  have hone : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
    unfold Torus.IsSmooth Torus.IsCk; exact contDiff_const
  have hUs : Torus.IsSmooth (propagator S.dyn S.ρ 0 r ψ) := by
    rw [hU]
    exact HRS.MD.EQGaussLyapDet.eqgld_prop_smooth hd1 S.hs0 S.hsd (fun _ => 0)
      (by unfold Torus.IsSmooth Torus.IsCk; exact contDiff_const)
      S.hβ (fun _ => 1) HRS.MD.EQEvoUnif.eqevo_isProb_one hone (fun _ => one_pos) ψ hψ 0 r le_rfl hr.1
  have hUc : Continuous (propagator S.dyn S.ρ 0 r ψ) :=
    PDE.ClassicalAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hUs 1)
  have h1 := crossCov_eq_nu_integral S.dyn S.ρ ν hν.1 P' Z₀ Z hZ.meas hZ.law_init hZ.sol hr' hψ
    (phi0_isSmooth k b) hUs
  have hμ : S.μ0 = volume := by
    unfold PreparedData.μ0; rw [hρ0]; unfold withDensityReal; simp
  rw [h1, hν.2 _ _ hUs (phi0_isSmooth k b), hμ, preparedCov_phi0 S.hd S.hs0 S.hsd S.hβ k hk b hUc, hU]
  have e1 := integral_propagator_mul_cosTest hd1 S.hs0 S.hsd S.hβ hr.1 hψ k
  have e2 := integral_propagator_mul_cosTest hd1 S.hs0 S.hsd S.hβ hr.1 hψ ((2 : ℤ) • k)
  simp only [e1, e2]
  have hψc : Continuous ψ :=
    PDE.ClassicalAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hψ 1)
  have hcos : ∀ j : Lattice d, Continuous (PDE.cosTest j) := fun j => by
    unfold PDE.cosTest
    exact continuous_const.mul
      (PDE.ClassicalAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth (HRS.d1_isSmooth_cosMode j) 1))
  have hi1 : Integrable (fun x => ψ x * PDE.cosTest k x) volume := (hψc.mul (hcos k)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => ψ x * PDE.cosTest ((2 : ℤ) • k) x) volume :=
    (hψc.mul (hcos _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold crossDensity
  have hrw : ∀ x, ψ x * ((1 + S.β * rieszCoeff d S.s k)⁻¹ * Real.exp (PDE.modelEigenvalue d S.s S.β⁻¹ (-1) k * r) * PDE.cosTest k x +
      b * (1 + S.β * rieszCoeff d S.s ((2 : ℤ) • k))⁻¹ *
        Real.exp (PDE.modelEigenvalue d S.s S.β⁻¹ (-1) ((2 : ℤ) • k) * r) * PDE.cosTest ((2 : ℤ) • k) x) =
      ((1 + S.β * rieszCoeff d S.s k)⁻¹ * Real.exp (PDE.modelEigenvalue d S.s S.β⁻¹ (-1) k * r)) * (ψ x * PDE.cosTest k x) +
      (b * (1 + S.β * rieszCoeff d S.s ((2 : ℤ) • k))⁻¹ *
        Real.exp (PDE.modelEigenvalue d S.s S.β⁻¹ (-1) ((2 : ℤ) • k) * r)) * (ψ x * PDE.cosTest ((2 : ℤ) • k) x) := fun x => by ring
  simp_rw [hrw]
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  ring

end HRS.MH.EdgeSharp
