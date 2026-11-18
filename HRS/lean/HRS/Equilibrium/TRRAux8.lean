/-
# TRR helper 8: the bias `B(θ) = C₀ Ψ(θ)`, `Ψ = ∫ ρ ∂_θρ`; smoothness.
-/
import HRS.Equilibrium.TRRAux7

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ} {s β : ℝ}

section BiasSmooth

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (k : Lattice d)

/-- `Ψ(θ) = ∫ ρ_θ ∂_θ ρ_θ dx`. -/
def Psi (θ : ℝ) : ℝ :=
  intC (Rc hd hs0 hsd hβ k θ * Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ))

lemma Psi_eq (θ : ℝ) :
    Psi hd hs0 hsd hβ k θ = intC (Rc hd hs0 hsd hβ k θ * deriv (Rc hd hs0 hsd hβ k) θ) := by
  rw [(hasDerivAt_Rc hd hs0 hsd hβ k θ).deriv]; rfl

lemma contDiff_deriv_Rc : ContDiff ℝ InfOrd (deriv (Rc hd hs0 hsd hβ k)) :=
  (contDiff_infty_iff_deriv.1 (contDiff_Rc hd hs0 hsd hβ k)).2

lemma contDiff_Psi : ContDiff ℝ InfOrd (Psi hd hs0 hsd hβ k) := by
  have : Psi hd hs0 hsd hβ k = fun θ => intC (Rc hd hs0 hsd hβ k θ * deriv (Rc hd hs0 hsd hβ k) θ) :=
    funext (Psi_eq hd hs0 hsd hβ k)
  rw [this]
  exact intC.contDiff.comp ((contDiff_Rc hd hs0 hsd hβ k).mul (contDiff_deriv_Rc hd hs0 hsd hβ k))

/-- the constant of the supercritical bias -/
def biasC (d : ℕ) (s β : ℝ) : ℝ :=
  sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1)) * β ^ ((d : ℝ) / s)

include hd hs0 hsd hβ in
theorem trr_bias_eq (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    supercriticalBias d s β (ρ θ) (Torus.cosMode k) = biasC d s β * Psi hd hs0 hsd hβ k θ := by
  have hρe : ρ θ = ⇑(Rc hd hs0 hsd hβ k θ) := trr_rho_eq_Rc hd hs0 hsd hβ k θ (hρ θ)
  unfold supercriticalBias biasC
  rw [hρe, trr_bias_integral hd hs0 hsd hβ k θ]
  congr 1
  unfold Psi
  rw [intC_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousMap.mul_apply]
  rw [Rd_apply]

end BiasSmooth

end HRS.TRR
