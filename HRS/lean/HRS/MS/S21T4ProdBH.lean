import HRS.MS.S21T4ProdBG

/-!
# R26-T3.S13: finite-section linearity of Wick quadratic forms

This is an exact identity for the centered quadratic Gaussian sections.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

theorem s21t4_wick_section_family_linear
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (z : ℕ → Ω → ℝ) {m : ℕ}
    (A : Fin m → ℕ → ℕ → ℝ) (α : Fin m → ℝ)
    (n : ℕ) (ω : Ω) :
    s94Sec P z (fun i j => ∑ k, α k * A k i j) n ω =
      ∑ k : Fin m, α k * s94Sec P z (A k) n ω := by
  unfold s94Sec
  calc
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          ∑ k : Fin m, α k * (A k i j *
            (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k : Fin m, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          α k * (A k i j *
            (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P)) := by
      calc
        _ = ∑ i ∈ Finset.range n, ∑ k : Fin m, ∑ j ∈ Finset.range n,
            α k * (A k i j *
              (z i ω * z j ω - ∫ ζ, z i ζ * z j ζ ∂P)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

end HRS.MS.R26T3
