import HRS.MH.EdgeSharpDefs
import HRS.MH.EdgeSharpEF
import HRS.Main.HeadlineEdgeworth
import HRS.Main.Q42Aux1
import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.Classical
import HRS.PDE.MeanField
import HRS.Uniform.Q48bAux1
import HRS.MD.EQEvoUnif

/-!
# EdgeSharp packets E2, K2 (statement-verbatim copies of `HRS/MH/EdgeSharpSpec.lean`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

variable {d : ℕ}

/-! ### E2 -/

theorem meanField_density_eq_one (S : PreparedData d) (hV : S.V = fun _ => 0) (hρ0 : S.ρ0 = fun _ => 1) :
    ∀ r : ℝ, 0 ≤ r → S.ρ r = fun _ => 1 := by
  intro r hr
  have hd := S.hd
  set K : ℕ := 6 * d + 30 with hKdef
  have hK : (d : ℝ) / 2 + 6 < (K : ℝ) := by
    have : (d : ℝ) ≤ 6 * d + 30 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have hc : (K : ℝ) = 6 * d + 30 := by simp [hKdef]
    rw [hc]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ρc, hsol, hpath⟩ := S.hρ K hK
  rw [hV, hρ0] at hsol
  have hsm1 : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := by
    unfold Torus.IsSmooth Torus.IsCk
    exact contDiff_const
  have hV0 : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := by
    unfold Torus.IsSmooth Torus.IsCk
    exact contDiff_const
  have hth : IsThermalDensity (periodicRiesz d S.s) (fun _ => (0 : ℝ)) S.β (fun _ => (1 : ℝ)) :=
    isThermalDensity_one_zero hd S.hs0 S.hsd S.β
  have hconst : PDE.IsMFSolutionHK d S.s (fun _ => (0 : ℝ)) S.β⁻¹ (K : ℝ) (fun _ => (1 : ℝ))
      (fun _ => PDE.coeffOf (fun _ : Torus d => (1 : ℝ))) :=
    Uniform.Q48b.q48b_isMFSolutionHK (by omega) S.s S.hs0 S.hsd S.β S.hβ _ hV0 _ hth hsm1
      (fun _ => one_pos) K
  have H : PDE.FiniteRegHyp d S.s S.β S.β K (fun _ => (0 : ℝ)) (fun _ : Torus d => (1 : ℝ)) :=
    MD.EQEvoUnif.eqevo_finiteRegHyp_one hd S.s S.β S.β S.hs0 S.hsd S.hβ le_rfl _ hV0 K (by omega)
  obtain ⟨ρc', -, -, -, -, huniq⟩ := PDE.finite_reg_exists_unique (by omega) S.s S.β S.β K _ _ H S.β
    ⟨le_rfl, le_rfl⟩
  have h1 := huniq _ hsol r hr
  have h2 := huniq _ hconst r hr
  rw [← hpath]
  show PDE.toFun (ρc r) = _
  rw [h1, ← h2]
  exact (Uniform.Q48b.q48b_toFun_coeffOf hsm1).2.2

/-! ### K2 -/

private lemma isCk_const_fn (n : ℕ) (c : ℝ) : Torus.IsCk n (fun _ : Torus d => c) := by
  unfold Torus.IsCk
  exact contDiff_const

theorem cubic_first_term_ne_zero (S : PreparedData d) (hV : S.V = fun _ => 0) (hρ0 : S.ρ0 = fun _ => 1)
    (k : Lattice d) (hk : k ≠ 0) (b : ℝ) (hb : b ≠ 0) :
    ∫ x, responseInverse (periodicRiesz d S.dyn.s) S.μ0 S.β (propagator S.dyn S.ρ 0 0 (phi0 k b)) x *
        responseInverse (periodicRiesz d S.dyn.s) S.μ0 S.β (propagator S.dyn S.ρ 0 0 (phi0 k b)) x *
        responseInverse (periodicRiesz d S.dyn.s) S.μ0 S.β (propagator S.dyn S.ρ 0 0 (phi0 k b)) x ∂S.μ0 ≠ 0 := by
  have hV1 : Torus.IsCk 1 S.dyn.V := by
    have : S.dyn.V = S.V := rfl
    rw [this, hV]; exact isCk_const_fn 1 0
  have hμ1 : Torus.IsCk 1 (S.ρ 0) := by
    rw [S.hρ_init, hρ0]; exact isCk_const_fn 1 1
  have hφ2 : Torus.IsCk 2 (phi0 k b) := PDE.MFSemigroup.isCk_nat_of_isSmooth (phi0_isSmooth k b) 2
  have hprop : propagator S.dyn S.ρ 0 0 (phi0 k b) = phi0 k b :=
    PDE.MFSemigroup.propagator_zero S.dyn (PDE.ClassicalAux.convKernelFacts (by have := S.hd; omega) S.dyn)
      hV1 S.ρ hμ1 hφ2
  have hμ : S.μ0 = (volume : Measure (Torus d)) := by
    unfold PreparedData.μ0 withDensityReal
    rw [hρ0]; simp
  rw [hprop, hμ]
  have hs : S.dyn.s = S.s := rfl
  rw [hs]
  have h := (homogeneous_cubic_coefficients S.hd S.hs0 S.hsd S.β S.hβ k hk b).2
  have e : (fun x => responseInverse (periodicRiesz d S.s) (volume : Measure (Torus d)) S.β (phi0 k b) x *
        responseInverse (periodicRiesz d S.s) (volume : Measure (Torus d)) S.β (phi0 k b) x *
        responseInverse (periodicRiesz d S.s) (volume : Measure (Torus d)) S.β (phi0 k b) x) =
      fun x => responseInverse (periodicRiesz d S.s) (volume : Measure (Torus d)) S.β (phi0 k b) x ^ 3 := by
    funext x; ring
  rw [e]
  intro hz
  exact h.2 hb (h.1.symm.trans hz)

end HRS.MH.EdgeSharp
