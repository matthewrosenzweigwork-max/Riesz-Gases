import HRS.MC.E214I
import HRS.MC.E214A3
import HRS.MC.E213U13o

/-!
# Packet E214I, part 2: the Theorem 2.13 machinery instantiated at the stationary datum (P3)

All statements are the E213/E214A theorems at `Ss := stationaryPrepared S ρβ hρβ`, `β₀ := S.β`,
`hEs := stationaryPrepared_hE S hE ρβ hρβ`.
-/

noncomputable section

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213Plan HRS.MC.E213O HRS.MC.E213T

namespace HRS.MC.E214I

variable {d : ℕ} (S : PreparedData d) {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)
  (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)

/-- Gaussian data for the stationary datum. -/
theorem stationary_exists_gaussData :
    Nonempty (GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ)) :=
  HRS.MC.E213U4.exists_gaussData_proof (stationaryPrepared_hE S hE ρβ hρβ)

/-- Window Edgeworth expansion for the stationary datum, with the Gaussian data exposed. -/
theorem stationary_window_gd (T : ℝ) (hT : 0 < T) :
    ∃ (gd : GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ))
      (ε : ℕ → ℝ), IsWindowEdgeworth (stationaryPrepared S ρβ hρβ) S.β m T (gd.Kproj T) ε :=
  HRS.MC.E214A.edgeworth_window_gd (stationaryPrepared S ρβ hρβ) S.β m T
    (stationaryPrepared_hE S hE ρβ hρβ) hT

variable {S ρβ hρβ}

/-- Uniform bound on the stationary window tensors. -/
theorem stationary_Kproj_bounded
    (gd : GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ))
    (T : ℝ) (hT : 0 < T) : ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a → ‖gd.Kproj T a‖ ≤ C :=
  HRS.MC.E213U11.Kproj_bounded_proof gd T hT

/-- Uniform moment package for the stationary window. -/
theorem stationary_gd_moments
    (gd : GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ))
    (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a →
      (∀ᵐ ω ∂gd.P₀, gd.Jwin T a ω ∈ projTensor (PathSpace d m T) 2) ∧
      MeasureTheory.AEStronglyMeasurable (gd.Zwin T a) gd.P₀ ∧
      MeasureTheory.AEStronglyMeasurable (gd.Dwin T a) gd.P₀ ∧
      MeasureTheory.AEStronglyMeasurable (gd.Jwin T a) gd.P₀ ∧
      MeasureTheory.Integrable (fun ω => ‖gd.Dwin T a ω‖ * ‖gd.Zwin T a ω‖ * ‖gd.Zwin T a ω‖) gd.P₀ ∧
      MeasureTheory.Integrable (fun ω => ‖gd.Jwin T a ω‖ * ‖gd.Zwin T a ω‖) gd.P₀ ∧
      (∫ ω, ‖gd.Dwin T a ω‖ * ‖gd.Zwin T a ω‖ * ‖gd.Zwin T a ω‖ ∂gd.P₀) ≤ C ∧
      (∫ ω, ‖gd.Jwin T a ω‖ * ‖gd.Zwin T a ω‖ ∂gd.P₀) ≤ C :=
  HRS.MC.E213U11.gd_moments_proof gd T hT

/-- Uniform `q`-th moments of the stationary window field `Zwin`. -/
theorem stationary_Z_moment
    (gd : GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ))
    (T : ℝ) (hT : 0 < T) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      MeasureTheory.AEStronglyMeasurable (gd.Zwin T a) gd.P₀ ∧
      MeasureTheory.Integrable (fun ω => ‖gd.Zwin T a ω‖ ^ q) gd.P₀ ∧
      ∫ ω, ‖gd.Zwin T a ω‖ ^ q ∂gd.P₀ ≤ C :=
  HRS.MC.E213U11.u11_Z_moment gd T hT q hq

/-- The stationary window tensor lies in the projective tensor space. -/
theorem stationary_Kwin_mem
    (gd : GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ))
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    gd.Kwin T a ∈ projTensor (PathSpace d m T) 3 :=
  HRS.MC.E213U11.Kwin_mem_proof gd T hT a ha

/-- Chaos structure of the stationary window (Gaussianity of `Zwin`, chaos orders of `Dwin`, `JwinP`). -/
theorem stationary_chaos_data
    (gd : GaussData (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ))
    (T : ℝ) (hT : 0 < T) :
    ∃ ξ : ℕ → gd.Ω₀ → ℝ, IsStdGaussianSeq gd.P₀ ξ ∧ ∀ a : ℝ, 0 ≤ a →
      IsCenteredGaussian (HRS.law gd.P₀ (gd.Zwin T a)) ∧ InFirstChaos gd.P₀ ξ 2 (gd.Zwin T a) ∧
      (∀ q : ℝ, 3 ≤ q → InSecondChaos gd.P₀ ξ q (gd.Dwin T a)) ∧
      (∀ q : ℝ, 2 ≤ q → InFirstChaos gd.P₀ ξ q (gd.JwinP T a)) :=
  HRS.MC.E213U13.chaos_data_proof gd T hT

end HRS.MC.E214I

end
