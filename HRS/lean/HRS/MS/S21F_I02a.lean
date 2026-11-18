import HRS.MS.S21F_I00
import HRS.MC.E213O1

/-!
# S21F, packet R26-T3.I02 (part a): slices of an `ℓ²` sequence along an enumeration

For an enumeration `e : ℕ ≃ ℕ × MultiIndex d` the slice `z ↦ (α ↦ z_{e⁻¹(n,α)}) ∈ B_m` is additive and homogeneous, and
`∑_n ‖slice n z‖² = ‖z‖²`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d : ℕ} {m : ℝ}

theorem s21f_slice_mem (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (z : SeqL2) :
    Memℓp (fun α : MultiIndex d => SeqL2.coord z (e.symm (n, α))) 2 := by
  rw [memℓp_two_iff]
  have h : Summable fun i => SeqL2.coord z i ^ 2 := lp_two_summable (show lp (fun _ : ℕ => ℝ) 2 from z)
  have h2 : Summable fun q : ℕ × MultiIndex d => SeqL2.coord z (e.symm q) ^ 2 :=
    (e.symm.summable_iff (f := fun i => SeqL2.coord z i ^ 2)).2 h
  exact h2.comp_injective (i := fun α : MultiIndex d => (n, α)) (fun a b hab => by simpa using hab)

/-- The `n`-th slice. -/
def s21f_slice (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (z : SeqL2) : OscDual d m :=
  (⟨fun α => SeqL2.coord z (e.symm (n, α)), s21f_slice_mem e n z⟩ : lp (fun _ : MultiIndex d => ℝ) 2)

theorem s21f_slice_coord (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (z : SeqL2) (α : MultiIndex d) :
    OscDual.coord (s21f_slice (m := m) e n z) α = SeqL2.coord z (e.symm (n, α)) := rfl

theorem s21f_slice_add (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (z w : SeqL2) :
    s21f_slice (m := m) e n (z + w) = s21f_slice e n z + s21f_slice e n w := by
  refine lp.ext (funext fun α => ?_)
  show SeqL2.coord (z + w) _ = SeqL2.coord z _ + SeqL2.coord w _
  rfl

theorem s21f_slice_smul (e : ℕ ≃ ℕ × MultiIndex d) (n : ℕ) (c : ℝ) (z : SeqL2) :
    s21f_slice (m := m) e n (c • z) = c • s21f_slice e n z := by
  refine lp.ext (funext fun α => ?_)
  show SeqL2.coord (c • z) _ = c * SeqL2.coord z _
  rfl

theorem s21f_slice_sq (e : ℕ ≃ ℕ × MultiIndex d) (z : SeqL2) :
    Summable (fun n => ‖s21f_slice (m := m) e n z‖ ^ 2) ∧
      ∑' n, ‖s21f_slice (m := m) e n z‖ ^ 2 = ‖z‖ ^ 2 := by
  have h : Summable fun i => SeqL2.coord z i ^ 2 := lp_two_summable (show lp (fun _ : ℕ => ℝ) 2 from z)
  have hF : Summable fun q : ℕ × MultiIndex d => SeqL2.coord z (e.symm q) ^ 2 :=
    (e.symm.summable_iff (f := fun i => SeqL2.coord z i ^ 2)).2 h
  have hn : ∀ n, ‖s21f_slice (m := m) e n z‖ ^ 2 = ∑' α, SeqL2.coord z (e.symm (n, α)) ^ 2 := fun n =>
    lp_two_norm_sq (s21f_slice (m := m) e n z)
  have hrow : ∀ n, Summable fun α : MultiIndex d => SeqL2.coord z (e.symm (n, α)) ^ 2 := fun n =>
    hF.comp_injective (i := fun α : MultiIndex d => (n, α)) (fun a b hab => by simpa using hab)
  simp_rw [hn]
  refine ⟨hF.prod, ?_⟩
  rw [← hF.tsum_prod' hrow, Equiv.tsum_eq e.symm (fun i => SeqL2.coord z i ^ 2)]
  exact (lp_two_norm_sq (show lp (fun _ : ℕ => ℝ) 2 from z)).symm

end HRS.MS.R26T3
