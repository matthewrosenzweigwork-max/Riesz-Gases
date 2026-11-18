import HRS.Main.FullBoundsAssembly
import HRS.Main.EqMargU4
import HRS.Energy.KIDAux2
import HRS.Equilibrium.Q84bAuxA

/-!
# FULLBOUNDS (auxiliary potential of a Gibbs preparation)

TeX L6926-6940 (`P:eq:Gibbs-initial-*`): for the preparation `ℚ_{N,β₀}(μ°)` (`β₀ > 0`) the auxiliary potential
`V₀ = -β₀⁻¹ log ρ° - g * ρ°` is smooth, `ρ°` is the thermal density of `(V₀, β₀)`, and
`ℚ_{N,β₀}(μ°)` is the canonical Gibbs law of `(V₀, β₀)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Convolution of an integrable kernel with a smooth function is smooth. -/
theorem fb_convFun_smooth {g ρ : Torus d → ℝ} (hg : Integrable g) (hρ : Torus.IsSmooth ρ) :
    Torus.IsSmooth (convFun g ρ) := by
  have h : Torus.lift (convFun g ρ) = HRS.KID.convL (Torus.lift ρ) g := by
    funext w
    simp only [Torus.lift, Function.comp]
    rw [HRS.Q84b.q84b_convFun_eq']
    unfold HRS.KID.convL
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Function.comp]
    rw [HRS.KernelGrad.mk_sub, Torus.mk_rep]
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (convFun g ρ))
  rw [h]
  exact HRS.KID.contDiff_convL hρ hg

/-- The auxiliary potential `V₀ = -β₀⁻¹ log ρ° - g * ρ°` of a Gibbs preparation (`β₀ > 0`): it is smooth,
`ρ°` is a thermal density for `(V₀, β₀)`, and the canonical Gibbs law of `(V₀, β₀)` is `ℚ_{N,β₀}(μ°)`. -/
theorem fb_aux_potential (S : PreparedData d) {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    ∃ V₀ : Torus d → ℝ, Torus.IsSmooth V₀ ∧
      IsThermalDensity (periodicRiesz d S.s) V₀ β₀ S.ρ0 ∧
      ∀ N : ℕ, canonicalGibbs (periodicRiesz d S.s) V₀ N β₀ =
        modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 := by
  have hint : Integrable (periodicRiesz d S.s) :=
    (integral_periodicRiesz S.hd S.hs0 S.hsd).1
  set V₀ : Torus d → ℝ := fun x => -β₀⁻¹ * Real.log (S.ρ0 x) - convFun (periodicRiesz d S.s) S.ρ0 x
    with hV₀
  have hsm : Torus.IsSmooth V₀ := by
    have h1 : Torus.IsSmooth (convFun (periodicRiesz d S.s) S.ρ0) :=
      fb_convFun_smooth hint S.hρ0.smooth
    show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V₀)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => Real.log (Torus.lift S.ρ0 w)) :=
      ContDiff.log S.hρ0.smooth (fun w => (S.hρ0.pos _).ne')
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (convFun (periodicRiesz d S.s) S.ρ0)) := h1
    exact (contDiff_const.mul h2).sub h3
  have hexp : ∀ x, Real.exp (-β₀ * (V₀ x + convFun (periodicRiesz d S.s) S.ρ0 x)) = S.ρ0 x := by
    intro x
    have : -β₀ * (V₀ x + convFun (periodicRiesz d S.s) S.ρ0 x) = Real.log (S.ρ0 x) := by
      simp only [hV₀]
      field_simp
      ring
    rw [this, Real.exp_log (S.hρ0.pos x)]
  have hth : IsThermalDensity (periodicRiesz d S.s) V₀ β₀ S.ρ0 := by
    refine ⟨S.hρ0.density, fun x => ?_⟩
    simp_rw [hexp]
    rw [S.hρ0.density.integral_one, div_one]
  refine ⟨V₀, hsm, hth, fun N => ?_⟩
  obtain ⟨Λ, hΛ0, hΛ⟩ := HRS.PoleCavityAux.exists_density_bound S.hρ0
  refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d S.s) V₀ β₀ S.ρ0 hth
    (fun x => periodicRiesz_neg x) ?_
  intro x
  exact (HRS.CoercAux.J_bounds (by have := S.hd; omega) S.hs0 S.hsd one_pos S.hρ0.density hΛ0.le hΛ x).1

end Main

end HRS

end
