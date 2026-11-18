import HRS.Main.A9Aux9

/-!
# Packet A9, part 10: the `ℓ¹`-bound of the `E_γ`-norm in expectation; coordinates of `x - ι y`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P

variable {d : ℕ}

theorem a9_coord_continuous (m : ℝ) (j : NonzeroLattice d) :
    Continuous fun F : NegSobolev d m => NegSobolev.coord F j := by
  have e : (fun F : NegSobolev d m => NegSobolev.coord F j) =
      fun F => innerSL ℝ (a9unit m j) F := by
    funext F; rw [innerSL_apply_apply, a9unit_inner]
  rw [e]; exact (innerSL ℝ (a9unit m j)).continuous

/-- `E‖Q‖ ≤ ∑_j b_j` when `E|Q_j| ≤ b_j` (`ℓ² ≤ ℓ¹` and Tonelli). -/
theorem a9_lintegral_norm_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℝ}
    (Q : Ω → NegSobolev d m) (hQ : AEMeasurable Q P) (b : NonzeroLattice d → ℝ)
    (hb0 : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hc : ∀ j, ∫⁻ ω, ENNReal.ofReal |NegSobolev.coord (Q ω) j| ∂P ≤ ENNReal.ofReal (b j)) :
    ∫⁻ ω, ENNReal.ofReal ‖Q ω‖ ∂P ≤ ENNReal.ofReal (∑' j, b j) := by
  calc ∫⁻ ω, ENNReal.ofReal ‖Q ω‖ ∂P
      ≤ ∫⁻ ω, ∑' j, ENNReal.ofReal |NegSobolev.coord (Q ω) j| ∂P :=
        lintegral_mono fun ω => a9_ofReal_norm_le_tsum (Q ω)
    _ = ∑' j, ∫⁻ ω, ENNReal.ofReal |NegSobolev.coord (Q ω) j| ∂P := by
        refine lintegral_tsum fun j => ?_
        exact ((((a9_coord_continuous m j).measurable.comp_aemeasurable hQ)).abs).ennreal_ofReal
    _ ≤ ∑' j, ENNReal.ofReal (b j) := ENNReal.tsum_le_tsum hc
    _ = ENNReal.ofReal (∑' j, b j) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbs).symm

section EmbedCoord

variable {m : ℝ} {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k)

include hk in
theorem a9_coord_sub_embed_mem (x : NegSobolev d m) (y : ℝ^q) (a₀ : Fin q) :
    NegSobolev.coord (x - embedCLM (fun a => a9unit m (k a)) y) (k a₀) =
      NegSobolev.coord x (k a₀) - y a₀ := by
  rw [a9_coord_sub, a9_coord_embed]
  congr 1
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a _ ha
    have : k a₀ ≠ k a := fun h => ha (hk h).symm
    simp [this]
  · simp

theorem a9_coord_sub_embed_nmem (x : NegSobolev d m) (y : ℝ^q) (j : NonzeroLattice d)
    (hj : j ∉ Set.range k) :
    NegSobolev.coord (x - embedCLM (fun a => a9unit m (k a)) y) j = NegSobolev.coord x j := by
  rw [a9_coord_sub, a9_coord_embed]
  have : ∑ a, (if j = k a then y a else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : j ≠ k a := fun h => hj ⟨a, h.symm⟩
    simp [this]
  rw [this]; ring

end EmbedCoord

end HRS.Main.A9
