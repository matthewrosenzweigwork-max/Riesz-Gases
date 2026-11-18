import HRS.MS.FinNoiseAux12

/-!
# S8.6 `finite_noise`, packet P6e (S86): linearity of the reconstruction `𝒯`

`s86_recon_sub`: `reconstructPath m T (M₁ - M₂) = reconstructPath m T M₁ - reconstructPath m T M₂` pointwise.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

theorem s86_A0_sub (x y : KSpace d m T) : (x - y).A₀ = x.A₀ - y.A₀ := rfl

theorem s86_B_sub (x y : KSpace d m T) : (x - y).B = x.B - y.B := rfl

theorem s86_A'_sub (x y : KSpace d m T) : (x - y).A' = x.A' - y.A' := rfl

theorem s86_evalA_sub (x y : KSpace d m T) (t : ℝ) : (x - y).evalA t = x.evalA t - y.evalA t := by
  unfold KSpace.evalA
  have hsub : Icc (0 : ℝ) (min t T) ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl (min_le_right _ _)
  have hint : ∀ z : KSpace d m T, Integrable (fun τ => (z.A' : ℝ → OscDual d m) τ)
      (volume.restrict (Icc (0 : ℝ) (min t T))) := fun z =>
    ((Lp.memLp z.A').integrable (by norm_num)).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hae : (fun τ => ((x - y).A' : ℝ → OscDual d m) τ) =ᵐ[volume.restrict (Icc (0 : ℝ) (min t T))]
      fun τ => (x.A' : ℝ → OscDual d m) τ - (y.A' : ℝ → OscDual d m) τ := by
    have := Lp.coeFn_sub x.A' y.A'
    rw [s86_A'_sub]
    exact (ae_mono (Measure.restrict_mono hsub le_rfl)) this
  rw [integral_congr_ae hae, integral_sub (hint x) (hint y), s86_A0_sub]
  abel

theorem s86_recon_sub {Ω : Type*} (M₁ M₂ : ℝ → Ω → KSpace d m T) (w : Ω) (t : ℝ) :
    reconstructPath m T (fun τ z => M₁ τ z - M₂ τ z) w t =
      reconstructPath m T M₁ w t - reconstructPath m T M₂ w t := by
  unfold reconstructPath
  rw [s86_evalA_sub, s86_B_sub, s86_B_sub]
  abel

end HRS.MS.FinNoise
