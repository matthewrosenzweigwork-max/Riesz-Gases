import HRS.Equilibrium.Parametrix.PXFIDAuxD

/-!
# Packet PX-FID, file E: integration by parts for a slice with a point singularity
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

/-- The identity for a fixed cut-off, in the form against `μ`. -/
theorem cutoff_identity (hd : 1 ≤ d) {β : ℝ} (hβ : β ≠ 0) {V ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ)
    (hforce : ∀ x, ρ x • (Torus.grad V x + forceField d s ρ x) = -β⁻¹ • Torus.grad ρ x)
    {ε : ℝ} (hε : 0 < ε) (ã : Euc d) {u ϕ : Torus d → ℝ}
    (hsm : ContDiffOn ℝ 2 (Torus.lift u) {p : Euc d | Torus.mk p ≠ Torus.mk ã})
    (hϕ : Torus.IsSmooth ϕ)
    (hi1 : Integrable (fun x => theta ε ã x * ϕ x * Bop d s V β ρ u x) (withDensityReal ρ))
    (hi2 : Integrable (fun x => theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x))
      (withDensityReal ρ))
    (hi3 : Integrable (fun x => ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x))
      (withDensityReal ρ)) :
    β * ∫ x, theta ε ã x * ϕ x * Bop d s V β ρ u x ∂(withDensityReal ρ) +
      ∫ x, theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x) ∂(withDensityReal ρ) +
      ∫ x, ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x) ∂(withDensityReal ρ) = 0 := by
  have hρm : Measurable ρ := (Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift ρ) from hρ.smooth).continuous).measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  have hI := integral_div_cutoff_eq_zero hε ã hϕ hρ.smooth hsm
  have hae : ∀ᵐ x : Torus d ∂(volume : Measure (Torus d)),
      ∑ j : Fin d, Torus.partialDeriv j (Wfield ε ã ϕ ρ u j) x =
        ρ x * (β * (theta ε ã x * ϕ x * Bop d s V β ρ u x) +
          theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x) +
          ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x)) := by
    have h0 : ∀ᵐ x ∂(volume : Measure (Torus d)), x ≠ Torus.mk ã := by
      rw [ae_iff]
      have := volume_singleton_torus hd (Torus.mk ã)
      simpa using this
    filter_upwards [h0] with x hx
    rw [div_cutoff_pointwise hβ hforce ã (theta_isSmooth ε ã) hϕ hρ.smooth hsm x hx]
    ring
  rw [integral_congr_ae hae] at hI
  have hI' : ∫ x, (β * (theta ε ã x * ϕ x * Bop d s V β ρ u x) +
      theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x) +
      ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x)) ∂(withDensityReal ρ) = 0 := by
    rw [integral_withDensityReal_eq ρ hρm hρ0]
    exact hI
  have hi1' : Integrable (fun x => β * (theta ε ã x * ϕ x * Bop d s V β ρ u x)) (withDensityReal ρ) :=
    hi1.const_mul β
  have hi12 : Integrable (fun x => β * (theta ε ã x * ϕ x * Bop d s V β ρ u x) +
      theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x)) (withDensityReal ρ) :=
    hi1'.add hi2
  rw [integral_add hi12 hi3, integral_add hi1' hi2, integral_const_mul] at hI'
  linarith

end HRS.Parx.PXFID

end
