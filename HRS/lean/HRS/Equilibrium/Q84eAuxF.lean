/-
# HRS.Equilibrium.Q84eAuxF — packet Q84e: the Poisson equation in terms of `B`, `𝒥ψ`

Using `μ(B ψ(·,y)) = 0` (`q84e_Bop_mean`) the projected generators satisfy
`(𝒜_x + 𝒜_y)ψ(x,y) = B(ψ(·,y))(x) + B(ψ(·,x))(y) + 𝒥ψ(x,y)`, so the Poisson equation of
`IsPairCorrector` reads `B(ψ(·,y))(x) + B(ψ(·,x))(y) + 𝒥ψ(x,y) = -H_f(x,y)` off the diagonal.
-/
import HRS.Equilibrium.Q84eAuxE
import HRS.Equilibrium.Q84bAuxI

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ}

theorem q84e_poisson_red (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hβ : 0 < β) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ)
    (x y : Torus d) (hxy : x ≠ y) :
    Bop d s V β ρ (fun z => ψ z y) x + Bop d s V β ρ (fun z => ψ z x) y + Jpair d s ρ ψ x y =
      -Hsource d s ρ f x y := by
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift
    (Q84a.q84a_contDiff_one hρs.smooth).continuous
  have hρm : Measurable ρ := hρc.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρs.pos x).le
  set μ := withDensityReal ρ with hμ
  have hJi : ∀ b : Torus d, Integrable (fun z => Jop d s ρ (fun w => ψ w b) z) μ := fun b =>
    (q84e_integrable_mu_iff hρm hρ0).2
      (Q84b.q84b_Jop_mean hd hcrit hβ hV hρ hρs hψ.size b).1
  have key : ∀ b : Torus d, ∫ z, (Bop d s V β ρ (fun w => ψ w b) z +
      Jop d s ρ (fun w => ψ w b) z) ∂μ = ∫ z, Jop d s ρ (fun w => ψ w b) z ∂μ := by
    intro b
    have hB := q84e_Bop_mean hd hcrit hβ hV hρ hρs hψ b
    rw [integral_add hB.1 (hJi b), hB.2, zero_add]
  have hsymx : (fun z => ψ x z) = fun z => ψ z x := funext fun z => hψ.symm x z
  have e1 : genFst d s V β ρ ψ x y = (Bop d s V β ρ (fun w => ψ w y) x +
      Jop d s ρ (fun w => ψ w y) x) - ∫ z, Jop d s ρ (fun w => ψ w y) z ∂μ := by
    rw [← key y]
    unfold genFst projGen projMean pair
    rfl
  have e2 : genSnd d s V β ρ ψ x y = (Bop d s V β ρ (fun w => ψ w x) y +
      Jop d s ρ (fun w => ψ w x) y) - ∫ z, Jop d s ρ (fun w => ψ w x) z ∂μ := by
    rw [← key x]
    unfold genSnd projGen projMean pair
    rw [hsymx]
  have e3 : Jpair d s ρ ψ x y = (Jop d s ρ (fun w => ψ w y) x - ∫ z, Jop d s ρ (fun w => ψ w y) z ∂μ) +
      (Jop d s ρ (fun w => ψ w x) y - ∫ z, Jop d s ρ (fun w => ψ w x) z ∂μ) := by
    unfold Jpair projMean pair
    rw [hsymx]
  have hP := hψ.poisson x y hxy
  rw [e1, e2] at hP
  rw [e3]
  linarith

end HRS.Q84e

end
