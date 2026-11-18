import HRS.MS.CritForceTerms
import HRS.MS.R26T8AB04a

/-!
# S8.2 T8A B09a: finite-term Minkowski for the actual raw supremum

If `S t w = ∑ i, Y i t w` for all `t ∈ [0,T]` (a.e. `w`), the `Y i` have measurable suprema with `L²(P)` bounds `b i`, then the
`L²(P)` norm of the actual supremum `⨆ t, ofReal |S t w|` is at most `∑ b i`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b09_blocks {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (T : ℝ) {n : ℕ}
    (S : ℝ → Ω → ℝ) (Y : Fin n → ℝ → Ω → ℝ) (b : Fin n → ℝ) (hb0 : ∀ i, 0 ≤ b i)
    (hid : ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, S t w = ∑ i, Y i t w)
    (hm : ∀ i, AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y i t w‖ₑ) P)
    (hb : ∀ i, (r26t8a_scalarSupSq P T (Y i)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (b i)) :
    (∫⁻ w, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |S t w|) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (∑ i, b i) := by
  obtain ⟨R, -, hR, hRb⟩ := HRS.MS.S82BD.s82_blocks_of_terms P
    (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |S t w|)
    (fun i w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y i t w‖ₑ) b hb0 hm hb (by
      filter_upwards [hid] with w hw
      refine iSup_le fun t => ?_
      rw [hw t t.2, ← Real.enorm_eq_ofReal_abs]
      refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact le_iSup (fun t : Set.Icc (0 : ℝ) T => ‖Y i t w‖ₑ) t)
  refine (ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)).trans hRb
  filter_upwards [hR] with w hw
  exact pow_le_pow_left' hw 2

end HRS.MS.R26T8A

end
