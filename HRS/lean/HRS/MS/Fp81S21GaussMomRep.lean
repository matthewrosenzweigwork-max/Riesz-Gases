import HRS.MS.Fp81S21WeightedMoments6
import HRS.MS.ProClosureS111CoeffMoments
import HRS.Sections.Q41Aux8

/-! Every-time measurable coefficient fields from scalar trace bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Jointly measurable scalar coordinates with summable second-moment bounds
produce a jointly measurable coefficient field, with one common coordinate
agreement event and the trace bound at every specified time. -/
theorem fp81s21_coeff_field_every_time
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℝ × Ω → ℝ) (hF : ∀ j, Measurable (F j))
    (b : ℕ → ℝ) (hb : Summable b)
    (hsec : ∀ u, 0 ≤ u → ∀ j,
      MemLp (fun ω => F j (u, ω)) 2 P ∧
        (∫ ω, F j (u, ω) ^ 2 ∂P) ≤ b j) :
    ∃ q : ℝ → Ω → r26t6_Coeff,
      Measurable (Function.uncurry q) ∧
      ∀ u, 0 ≤ u →
        MemLp (q u) 2 P ∧ (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ ∑' j, b j ∧
        ∀ᵐ ω ∂P, ∀ j, q u ω j = F j (u, ω) := by
  let S : Set (ℝ × Ω) := {p | Summable (fun j => F j p ^ 2)}
  have hS : MeasurableSet S :=
    HRS.Q41.q41_measurableSet_summable (fun j p => F j p ^ 2)
      (fun j => (hF j).pow_const 2) (fun j p => sq_nonneg _)
  let Q : ℝ × Ω → r26t6_Coeff := fun p => natCoeffOf (fun j => F j p)
  have hcoord (p : ℝ × Ω) (j : ℕ) :
      Q p j = if p ∈ S then F j p else 0 := by
    by_cases hp : p ∈ S
    · simp only [if_pos hp]
      exact natCoeffOf_apply hp j
    · have hn : ¬ Memℓp (fun j => F j p) 2 := by
        rw [natCoeff_mem_iff]
        exact hp
      simp [Q, natCoeffOf, hn, hp]
  have hQ : Measurable Q := by
    apply fp81s21_coeff_measurable Q
    intro j
    have he : (fun p => Q p j) = fun p => if p ∈ S then F j p else 0 := by
      funext p
      exact hcoord p j
    rw [he]
    exact Measurable.ite hS (hF j) measurable_const
  refine ⟨fun u ω => Q (u, ω), hQ, ?_⟩
  intro u hu
  have hsum : Summable (fun j => ∫ ω, F j (u, ω) ^ 2 ∂P) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => sq_nonneg _)
      (fun j => (hsec u hu j).2) hb
  have hae : ∀ᵐ ω ∂P, ∀ j, Q (u, ω) j = F j (u, ω) := by
    filter_upwards [(scalar_square_tonelli P (fun j ω => F j (u, ω))
      (fun j => (hsec u hu j).1) hsum).2] with ω hω j
    exact natCoeffOf_apply hω j
  have hcoords : ∀ j, MemLp (fun ω => Q (u, ω) j) 2 P := by
    intro j
    exact (memLp_congr_ae (hae.mono fun ω hω => hω j)).2 (hsec u hu j).1
  have hbnd : ∀ j, (∫ ω, Q (u, ω) j ^ 2 ∂P) ≤ b j := by
    intro j
    calc
      _ = ∫ ω, F j (u, ω) ^ 2 ∂P :=
        integral_congr_ae (hae.mono fun ω hω => by rw [hω j])
      _ ≤ b j := (hsec u hu j).2
  exact ⟨(coeff_second_moment_bound P (fun ω => Q (u, ω)) hcoords b hb hbnd).1,
    (coeff_second_moment_bound P (fun ω => Q (u, ω)) hcoords b hb hbnd).2, hae⟩

#print axioms fp81s21_coeff_field_every_time
end HRS.Fp81.S21
end
