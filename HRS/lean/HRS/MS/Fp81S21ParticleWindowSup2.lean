import HRS.MS.Fp81S21ParticleWindowSup

/-! Countable square-sum estimates over oscillator modes. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21

/-- The countable-mode version of the `L³` square-sum estimate. The countable
index is assumed infinite so it can be reindexed by `ℕ`; this covers the
oscillator mode type `MultiIndex d` when `d > 0`. -/
theorem fp81s21_countable_tsum_square_l3_minkowski
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] [Infinite ι]
    (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, AEStronglyMeasurable (X i) P) :
    (∫⁻ ω, (∑' i, ‖X i ω‖ₑ ^ (2 : ℝ)) ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ) ≤
      ∑' i, (eLpNorm' (X i) 6 P) ^ (2 : ℝ) := by
  classical
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := ι)
  have hnat := fp81s21_tsum_square_l3_minkowski P
    (fun n => X (e n)) (fun n => hX (e n))
  calc
    (∫⁻ ω, (∑' i, ‖X i ω‖ₑ ^ (2 : ℝ)) ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ) =
        (∫⁻ ω, (∑' n, ‖X (e n) ω‖ₑ ^ (2 : ℝ)) ^ (3 : ℝ) ∂P) ^ (1 / 3 : ℝ) := by
      congr 2
      funext ω
      rw [(e.tsum_eq (fun i => ‖X i ω‖ₑ ^ (2 : ℝ))).symm]
    _ ≤ ∑' n, (eLpNorm' (X (e n)) 6 P) ^ (2 : ℝ) := hnat
    _ = ∑' i, (eLpNorm' (X i) 6 P) ^ (2 : ℝ) := by
      exact e.tsum_eq (fun i => (eLpNorm' (X i) 6 P) ^ (2 : ℝ))

#print axioms HRS.Fp81.S21.fp81s21_countable_tsum_square_l3_minkowski
end HRS.Fp81.S21
end
