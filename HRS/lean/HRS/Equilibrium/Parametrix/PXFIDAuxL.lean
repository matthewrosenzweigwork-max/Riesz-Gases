import HRS.Equilibrium.Parametrix.PXFIDAuxK
import HRS.Kernel.GradBasic

/-!
# Packet PX-FID, file L: no diagonal flux, and the pointwise equation without the projection means
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

/-- The standing hypotheses (a copy of `ParxHyp`, to keep this file independent of it). -/
structure FidHyp (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) : Prop where
  two_le : 2 ≤ d
  crit : s = (d : ℝ) / 2
  beta_pos : 0 < β
  V_smooth : Torus.IsSmooth V
  thermal : IsThermalDensity (periodicRiesz d s) V β ρ
  rho_smooth : SmoothPosDensity ρ

theorem FidHyp.s_nonneg {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (H : FidHyp d s V β ρ) :
    0 ≤ s := by
  rw [H.crit]; positivity

theorem FidHyp.s_lt {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (H : FidHyp d s V β ρ) :
    s < d := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  rw [H.crit]; linarith

theorem FidHyp.one_le_s {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ} (H : FidHyp d s V β ρ) :
    1 ≤ s := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
  rw [H.crit]; linarith

theorem integral_add_of_integral_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (h0 : ∫ x, f x ∂μ = 0) :
    ∫ x, (f x + g x) ∂μ = ∫ x, g x ∂μ := by
  by_cases hg : Integrable g μ
  · rw [integral_add hf hg, h0, zero_add]
  · have : ¬ Integrable (fun x => f x + g x) μ := by
      intro h
      apply hg
      have h2 : Integrable (fun x => f x + g x - f x) μ := h.sub hf
      simpa using h2
    rw [integral_undef this, integral_undef hg]

theorem grad_const_one (z : Torus d) : Torus.grad (fun _ : Torus d => (1 : ℝ)) z = 0 := by
  unfold Torus.grad gradient
  have : Torus.lift (fun _ : Torus d => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
  rw [this, fderiv_fun_const]
  simp

end HRS.Parx.PXFID

end
