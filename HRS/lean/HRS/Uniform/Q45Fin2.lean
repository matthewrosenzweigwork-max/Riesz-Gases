import HRS.Uniform.Q45Fin1

/-!
# Q45: abstract finite-dimensional comparison for block-Riemann sums of Hilbert martingales
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The left-endpoint block sums `∑_k ⟨α_{j,k}, M_{r_{k+1}} - M_{r_k}⟩`, `j < m`. -/
def zeta {m : ℕ} (α : Fin m → ℕ → H) (T : ℝ) (Nb : ℕ) (M : ℝ → Ω → H) (ω : Ω) : ℝ^m :=
  WithLp.toLp 2 fun j => ∑ k ∈ Finset.range Nb,
    inner ℝ (α j k) (M (rr Nb T (k + 1)) ω - M (rr Nb T k) ω)

/-- Extraction of the derivative bounds from membership in the `C_b²` unit ball. -/
lemma cbUnit_bounds {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Φ : B → ℝ}
    (hΦ : Φ ∈ CbUnitBall B 2) :
    ContDiff ℝ 2 Φ ∧ (∀ x, |Φ x| ≤ 1) ∧ (∀ x, ‖fderiv ℝ Φ x‖ ≤ 1) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 Φ x‖ ≤ 1) := by
  obtain ⟨hc, hb, hn⟩ := hΦ
  have b0 := hb 0 (by norm_num)
  have b1 := hb 1 (by norm_num)
  have b2 := hb 2 le_rfl
  have s0 : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have s1 : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 Φ z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have s2 : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 2 Φ z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have hsum : (⨆ z, ‖iteratedFDeriv ℝ 0 Φ z‖) + (⨆ z, ‖iteratedFDeriv ℝ 1 Φ z‖) +
      (⨆ z, ‖iteratedFDeriv ℝ 2 Φ z‖) ≤ 1 := by
    refine le_trans (le_of_eq ?_) hn
    unfold cbNorm
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  refine ⟨hc, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have := le_ciSup b0 x
    rw [norm_iteratedFDeriv_zero] at this
    rw [← Real.norm_eq_abs]
    linarith
  · have := le_ciSup b1 x
    rw [norm_iteratedFDeriv_one] at this
    linarith
  · have := le_ciSup b2 x
    linarith

end HRS.Uniform.Q45
