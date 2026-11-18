import HRS.MS.SA16Y5Sm1
import HRS.MS.SA16Y5Ds1
import HRS.MS.SA16Y4Nl2
import HRS.MS.SA16Y4Fin3

/-!
# S.A.16 (SA16Y5) Dn1: uniform data of the mollified densities (`Good`, decay, `Cb`, nonnegativity)

`sa16y5_density_data`: for `1 ≤ d` and every `(m+3,Λ)`-regular density `μ` with `W = d^{m+3} 4^{d+3} max(Λ,0)`:
`μ` and every mollification `ρ_N ⋆ μ` are `Good` and satisfy `|·| ≤ W (1+|x|)^{-(d+3)}`; `ρ_N ⋆ μ` is in `SB`, satisfies `Dec (m+3) W` and `Cb (m+3) W`,
and is nonnegative when `μ` is.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Dn1
variable {d : ℕ}

lemma sa16y5_Dec_Cb {N : ℕ} {W : ℝ} {μ : Euc d → ℝ} (hW : 0 ≤ W) (h : sa16y5_Dec N W μ) : sa16z_Cb N W μ := by
  intro k hk y
  refine (h k hk y).trans ?_
  have : (1 + ‖y‖) ^ (-((d + 3 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
      (by have : (0 : ℝ) ≤ ((d + 3 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  nlinarith

theorem sa16y5_density_data (hd : 1 ≤ d) (m : ℕ) (Λ : ℝ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ μ : EuclideanSpace ℝ (Fin d) → ℝ, IsRegularDensityW (m + 3) Λ μ →
      (sa16y4_Good μ ∧ ∀ x, |μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) ∧
      ∀ N : ℕ, sa16q_SB (sa16q_mol N μ) ∧ sa16y5_Dec (m + 3) W (sa16q_mol N μ) ∧ sa16y4_Good (sa16q_mol N μ) ∧
        (∀ x, |sa16q_mol N μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) ∧
        ((∀ x, 0 ≤ μ x) → ∀ x, 0 ≤ sa16q_mol N μ x) := by
  set W : ℝ := (d : ℝ) ^ (m + 3) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) with hW
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  refine ⟨W, hW0, fun μ hμ => ⟨⟨?_, ?_⟩, fun N => ⟨?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · obtain ⟨hC, hbd, -⟩ := sa16q_reg_data hμ
    exact ⟨hC.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)), max Λ 0, max Λ 0,
      fun x => by simpa [Real.norm_eq_abs] using hbd 0 (by omega) x,
      fun x => by simpa [norm_iteratedFDeriv_one] using hbd 1 (by omega) x⟩
  · intro x
    obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
    have h1 := hw 0 (by omega) (fun l => l.elim0) x
    have hx1 : 0 < (1 + ‖x‖) := by positivity
    have e : partialDeriv (fun l : Fin 0 => l.elim0 : Fin 0 → Fin d) μ x = μ x := by
      simp [partialDeriv, iteratedFDeriv_zero_apply]
    rw [e] at h1
    have hpos : 0 < (1 + ‖x‖) ^ (d + 3) := by positivity
    have e1 : (1 + ‖x‖) ^ (-((d : ℝ) + 3)) = ((1 + ‖x‖) ^ (d + 3))⁻¹ := by
      rw [Real.rpow_neg hx1.le, show (d : ℝ) + 3 = ((d + 3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have h2 : |μ x| ≤ 2 ^ (d + 3) * max Λ 0 * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
      rw [e1, ← div_eq_mul_inv, le_div_iff₀ hpos]
      exact h1
    refine h2.trans ?_
    have hW1 : 2 ^ (d + 3) * max Λ 0 ≤ W := by
      rw [hW]
      have hQ : (1 : ℝ) ≤ (d : ℝ) ^ (m + 3) * 2 ^ (d + 3) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd0) (one_le_pow₀ (by norm_num))
      have ha : 0 ≤ 2 ^ (d + 3) * max Λ 0 := by positivity
      calc 2 ^ (d + 3) * max Λ 0 = 1 * (2 ^ (d + 3) * max Λ 0) := (one_mul _).symm
        _ ≤ ((d : ℝ) ^ (m + 3) * 2 ^ (d + 3)) * (2 ^ (d + 3) * max Λ 0) := mul_le_mul_of_nonneg_right hQ ha
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right hW1 (Real.rpow_nonneg hx1.le _)
  · exact (sa16y4_mol_data3 hd hμ N).1
  · exact (sa16y4_mol_data3 hd hμ N).2
  · obtain ⟨hSB, -⟩ := sa16y4_mol_data3 hd hμ N
    obtain ⟨h1, B0, B1, hB0, hB1⟩ := sa16q_SB_C1 hSB
    exact ⟨h1, B0, B1, hB0, hB1⟩
  · intro x
    obtain ⟨-, hwt⟩ := sa16y4_mol_data3 hd hμ N
    have := hwt 0 (by omega) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    rw [show -((d : ℝ) + 3) = -((d + 3 : ℕ) : ℝ) by push_cast; ring]
    exact this
  · intro hpos x
    rw [sa16q_mol_eq]
    exact integral_nonneg fun y => mul_nonneg (hpos y) (sa16y_rho_nonneg N _)

end Dn1

end HRS.Whole.AppendixA.Phase2SA16R
