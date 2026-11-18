import HRS.MS.SA16Y4Nc8
import HRS.MS.SA16Y4Nl3
import HRS.MS.SA16Y4Mu1

/-!
# S.A.16 (SA16Y4) Fin3: `Good`, decay and `SA16SubOp` data of the mollified and of the true density

`sa16y4_density_data`: there is `W ≥ 0` (depending on `d, m, Λ` only) such that for every `(m+3,Λ)`-regular `μ` the true density and all its
mollifications `ρ_N ⋆ μ` are `Good`, satisfy `|·| ≤ W (1+‖x‖)^{-(d+3)}`, and `sa16so_G d m p s M ·` is their `SA16SubOp`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Fin3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y4_density_data (hd : 1 ≤ d) (m : ℕ) (s MB Λ : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
    (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) →
      ∀ μ : EuclideanSpace ℝ (Fin d) → ℝ, IsRegularDensityW (m + 3) Λ μ →
        (sa16y4_Good μ ∧ (∀ x, |μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) ∧
          SA16SubOp d m p s M μ (sa16so_G d m p s M μ)) ∧
        ∀ N : ℕ, sa16y4_Good (sa16q_mol N μ) ∧ (∀ x, |sa16q_mol N μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) ∧
          SA16SubOp d m p s M (sa16q_mol N μ) (sa16so_G d m p s M (sa16q_mol N μ)) := by
  obtain ⟨C, hC0, hex⟩ := sa16so_G_exists d m hd s p MB Λ hs0 hs2 hfar
  obtain ⟨CG, CG1, hCG, hCG1, hnl⟩ := sa16y4_nl_pair d m hd s p MB Λ hs0 hs2 hfar
  set W : ℝ := (d : ℝ) ^ (m + 3) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) with hW
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  refine ⟨W, hW0, fun M hM μ hμ => ⟨⟨?_, ?_, ?_⟩, fun N => ⟨?_, ?_, ?_⟩⟩⟩
  · -- Good μ
    obtain ⟨hC, hbd, -⟩ := sa16q_reg_data hμ
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
  · obtain ⟨T, hT, hTs⟩ := hex M hM μ hμ
    rw [sa16so_G_eq hTs]; exact hTs
  · obtain ⟨hSB, -⟩ := sa16y4_mol_data3 hd hμ N
    obtain ⟨h1, B0, B1, hB0, hB1⟩ := sa16q_SB_C1 hSB
    exact ⟨h1, B0, B1, hB0, hB1⟩
  · intro x
    obtain ⟨-, hwt⟩ := sa16y4_mol_data3 hd hμ N
    have := hwt 0 (by omega) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    rw [show -((d : ℝ) + 3) = -((d + 3 : ℕ) : ℝ) by push_cast; ring]
    exact this
  · obtain ⟨T1, T0, h0, h1, hc, hs0', hs1'⟩ := hnl M hM μ hμ N
    rw [sa16so_G_eq hs0']; exact hs0'

end Fin3

end HRS.Whole.AppendixA.Phase2SA16R
