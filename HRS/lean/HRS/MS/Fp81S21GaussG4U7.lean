import HRS.MS.Fp81S21GaussG4U2
import HRS.MS.Fp81S21GaussG4U3
import HRS.MS.Fp81S21GaussG4U44
import HRS.MS.Fp81S21Absorption
import HRS.MS.S21F_C00
import HRS.MS.ProClosureS111ChartedOrbits

/-! Centered initial estimate support for the S2.1(iii) G4 packet. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- The two G4 cost declarations agree definitionally. -/
theorem fp81s21_g4_cost_eq_u7 (d : ℕ) (f : Euc d → ℝ) :
    fp81s21_g4J d f = fp81s21_g4_J d f := by
  rfl

/-- The scalar generator estimate extends from oscillator tests to the finite
Hermite combinations used by terminal Duhamel. -/
theorem fp81s21_g4_generator_combo_cost (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ q : ℝ, 0 ≤ q → ∀ f : Euc p.d → ℝ,
        IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
        MemLp (generatorW (r26t3_coeff R) q f) 2
          (HRS.Whole.withDensityReal R.ρβ) ∧
        (∫ x, (generatorW (r26t3_coeff R) q f x)^2
          ∂HRS.Whole.withDensityReal R.ρβ) ≤ A * fp81s21_g4_J p.d f := by
  obtain ⟨δ0, hδ0, hδ0half, hphys⟩ := fp81s21_g4_generator p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨A, hA, hbound⟩ := hphys δ hδ hδle R
  refine ⟨A, hA, ?_⟩
  intro q hq f hf
  have hf' : IsOscTest (wholeSpaceIndex p.d : ℝ) f :=
    HRS.MS.ProClosureS111.dualCombo_isOscTest hf
  obtain ⟨hgen, _hgrad, hsum⟩ := hbound q hq f hf'
  have hsum' :
      (∫ x, (generatorW (r26t3_coeff R) q f x)^2
        ∂HRS.Whole.withDensityReal R.ρβ) +
      (∫ x, ‖gradient f x‖^2 ∂HRS.Whole.withDensityReal R.ρβ)
        ≤ A * fp81s21_g4_J p.d f := by
    simpa only [fp81s21_g4_cost_eq_u7] using hsum
  refine ⟨hgen, ?_⟩
  have hgrad : 0 ≤
      ∫ x, ‖gradient f x‖^2 ∂HRS.Whole.withDensityReal R.ρβ :=
    integral_nonneg fun x => sq_nonneg _
  exact (le_add_of_nonneg_right hgrad).trans hsum'

#print axioms fp81s21_g4_cost_eq_u7
#print axioms fp81s21_g4_generator_combo_cost
end HRS.Fp81.S21
