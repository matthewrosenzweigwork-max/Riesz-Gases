import HRS.MC.S7PIDTVec

/-!
# Packet PI-D, sub-packet B (part 1): `Π_F v → v` as the finite set `F` of modes increases to all modes
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDB

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ}

theorem S7PIDB_trunc_lip (m : ℝ) (F : Finset (NonzeroLattice d)) :
    LipschitzWith 1 (fun a : NegSobolev d m => truncF m F a) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact HRS.MC.Sec7.S7PIDT.S7PIDT_trunc_sub_le m F a b

theorem S7PIDB_trunc_tendsto (m : ℝ) (v : NegSobolev d m) :
    Tendsto (fun F : Finset (NonzeroLattice d) => truncF m F v) atTop (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ F : Finset (NonzeroLattice d), ‖truncF m F v - v‖ ^ 2 =
      ∑' k : {x // x ∉ F}, NegSobolev.coord v k ^ 2 := by
    intro F
    obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (truncF m F v - v)
    rw [h2]
    have hk : ∀ k, NegSobolev.coord (truncF m F v - v) k ^ 2 =
        ({x | x ∉ F} : Set (NonzeroLattice d)).indicator (fun k => NegSobolev.coord v k ^ 2) k := by
      intro k
      rw [HRS.MC.Sec7.S7PIDT.S7PIDT_coord_sub, HRS.MC.Sec7.S7PIDT.S7PIDT_coord_trunc]
      by_cases hkF : k ∈ F <;> simp [hkF, Set.indicator]
    simp_rw [hk]
    exact (tsum_subtype ({x | x ∉ F} : Set (NonzeroLattice d)) (fun k => NegSobolev.coord v k ^ 2)).symm
  have h0 : Tendsto (fun F : Finset (NonzeroLattice d) => ‖truncF m F v - v‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hsq]
    exact tendsto_tsum_compl_atTop_zero (fun k : NonzeroLattice d => NegSobolev.coord v k ^ 2)
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h0
  simp only [Real.sqrt_zero] at h1
  refine h1.congr fun F => ?_
  simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]

end HRS.MC.Sec7.S7PIDB

end
