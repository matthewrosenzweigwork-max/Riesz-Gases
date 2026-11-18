import HRS.Sections.Sec3
import HRS.Sections.Q41Aux20

/-!
# Packet Q41, helper 21: the stationary Gaussian field exists (`q41_field_exists`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFPair

variable {d : ℕ}

/-- **Existence of the stationary Gaussian field** `Z_β` on `E_m`, for every `m > d/2 + 1`. -/
theorem q41_field_exists (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < 2 * m) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → Ω → NegSobolev d m), IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z := by
  obtain ⟨hpos, hsm⟩ := q41_thermal_regular hd hs0 hsd hβ hV hρβ
  have hρC := q41_cont_of_smooth hsm
  obtain ⟨c₀, Λ₀, H⟩ := frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hsm hpos (2 * mStar d + 4)
  have hr := q41_modeKernel H hd hs0 hsd hβ hV hρβ hρC hpos
  obtain ⟨Ω, mΩ, P, hP, Z, hZm, hZc, hfdd⟩ := q41_smooth_process (r := q41_r H) (by omega) hm hr
    (q41_cov2 H) (fun e φ ψ hφ hψ t t' ht ht' => q41_cov2_limit H (by omega) e hφ hψ ht ht')
  exact ⟨Ω, mΩ, P, hP, Z, ⟨hZm, hZc, fun p τ φ hτ hφ => hfdd p τ φ hτ hφ⟩⟩

end HRS.Q41
