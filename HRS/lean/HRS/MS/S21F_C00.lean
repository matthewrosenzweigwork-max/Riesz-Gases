import HRS.MS.ThCorrRespAux3
import HRS.MS.S111X2Aux5
import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.C00: thermal response energy and its two-sided `L²` bound

`s111x2_thermal_response_forms` (S11.1 X2, merged) at the physical temperature `θ = Γ = β` gives the coercivity/upper bounds
`η ‖P f‖² ≤ C_{β,μ_β}(f,f) ≤ ‖P f‖²` of the thermal susceptibility with `η = (1 + β‖K‖)⁻¹`-type constant chosen before `f`;
the energy is `β` times the susceptibility form (not divided by `β`), so `c = β η`, `C = β`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

def r26t3_energy {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (f : Euc p.d → ℝ) : ℝ :=
  p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (HRS.Whole.withDensityReal R.ρβ) p.β f f

theorem r26t3_energy_bounds {p : Parameters} {δ : ℝ} (R : Trajectory p δ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ f : Euc p.d → ℝ,
      MemLp f 2 (HRS.Whole.withDensityReal R.ρβ) →
      c * ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ) ≤ r26t3_energy R f ∧
      r26t3_energy R f ≤ C * ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ) := by
  obtain ⟨η, hη0, -, hη⟩ := HRS.MS.S111X2.s111x2_thermal_response_forms p.hd p.s p.a p.β p.β
    p.hs0 p.hs p.ha p.hβ p.hβ.le
  refine ⟨p.β * η, p.β, mul_pos p.hβ hη0, p.hβ, fun f hf => ?_⟩
  have hform := hη R.ρβ R.thermal p.β ⟨p.hβ.le, le_rfl⟩
  obtain ⟨h1, h2⟩ := hform.coercive f hf
  unfold r26t3_energy
  refine ⟨?_, ?_⟩
  · calc p.β * η * ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
            ∂(HRS.Whole.withDensityReal R.ρβ)
        = p.β * (η * HRS.MS.S111X2.s111x2_centeredSquare (HRS.Whole.withDensityReal R.ρβ) f) := by
          unfold HRS.MS.S111X2.s111x2_centeredSquare; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 p.hβ.le
  · calc p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (HRS.Whole.withDensityReal R.ρβ) p.β f f
        ≤ p.β * HRS.MS.S111X2.s111x2_centeredSquare (HRS.Whole.withDensityReal R.ρβ) f :=
          mul_le_mul_of_nonneg_left h2 p.hβ.le
      _ = _ := by unfold HRS.MS.S111X2.s111x2_centeredSquare; ring

end HRS.MS.R26T3
