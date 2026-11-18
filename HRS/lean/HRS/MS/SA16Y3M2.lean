import HRS.MS.SA16Y3M1

/-!
# S.A.16 (SA16Y3) M2: from the jet energy bound to the `WmpSpace` norm bound (uniform constants)

`sa16y3_norm_of_energy`: there is `CN > 0` (depending only on `d, m, p`) with
`jetEnergy G ≤ jetEnergy H * exp a → ‖G‖ ≤ CN * ‖H‖ * exp (a / p)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section M2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_norm_of_energy (m : ℕ) :
    ∃ CN : ℝ, 0 < CN ∧ ∀ (G H : WmpSpace d m p) (a : ℝ),
      jetEnergy d m p G ≤ jetEnergy d m p H * Real.exp a → ‖G‖ ≤ CN * ‖H‖ * Real.exp (a / p) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨hN, ⟨C, hC0, hC⟩, hpow, -⟩ := closed_jet_energy_calculus d m p
  refine ⟨C, hC0, fun G H a hle => ?_⟩
  have hjG := hN.nonneg G
  have hjH := hN.nonneg H
  have hea : 0 < Real.exp (a / p) := Real.exp_pos _
  have hpw : jetNorm d m p G ^ p ≤ (jetNorm d m p H * Real.exp (a / p)) ^ p := by
    rw [hpow G, Real.mul_rpow hjH hea.le, hpow H, ← Real.exp_mul]
    have : a / p * p = a := by field_simp
    rw [this]; exact hle
  have h1 : jetNorm d m p G ≤ jetNorm d m p H * Real.exp (a / p) :=
    (Real.rpow_le_rpow_iff hjG (mul_nonneg hjH hea.le) hp0).1 hpw
  calc ‖G‖ ≤ jetNorm d m p G := (hC G).1
    _ ≤ jetNorm d m p H * Real.exp (a / p) := h1
    _ ≤ (C * ‖H‖) * Real.exp (a / p) := mul_le_mul_of_nonneg_right (hC H).2 hea.le
    _ = _ := by ring

end M2

end HRS.Whole.AppendixA.Phase2SA16R
