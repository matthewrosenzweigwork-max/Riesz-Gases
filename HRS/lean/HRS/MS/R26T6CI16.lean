import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# R26-T6C.I16 — geometric countably valued approximation

A pointwise convergent finite-range simple-function sequence admits a
measurable, point-dependent index selection at each geometric accuracy.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS

theorem r26t6c_geometric_approximation {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] (F : A → E) (hF : StronglyMeasurable F) :
    ∃ Q : ℕ → A → E,
      (∀ n, StronglyMeasurable (Q n) ∧ (Set.range (Q n)).Countable) ∧
      ∀ n a, ‖Q n a - F a‖ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  classical
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let ε : ℕ → ℝ := fun n => (2 : ℝ) ^ (-(n : ℤ))
  let p : ℕ → ℕ → A → Prop := fun n k a =>
    ‖(hF.approx k : A → E) a - F a‖ ≤ ε n
  have hε : ∀ n, 0 < ε n := fun n => by
    dsimp [ε]
    exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have hex : ∀ n a, ∃ k, p n k a := by
    intro n a
    obtain ⟨N, hN⟩ :=
      (Metric.tendsto_atTop.1 (hF.tendsto_approx a)) (ε n) (hε n)
    refine ⟨N, ?_⟩
    change ‖(hF.approx N : A → E) a - F a‖ ≤ ε n
    have hh := hN N le_rfl
    simpa only [dist_eq_norm] using hh.le
  have hpmeas : ∀ n k, MeasurableSet {a : A | p n k a} := by
    intro n k
    change MeasurableSet {a : A |
      ‖(hF.approx k : A → E) a - F a‖ ≤ ε n}
    have hsub : StronglyMeasurable (fun a : A =>
        (hF.approx k : A → E) a - F a) :=
      (hF.approx k).stronglyMeasurable.sub hF
    exact measurableSet_le hsub.measurable.norm measurable_const
  let Q : ℕ → A → E := fun n a =>
    (hF.approx (Nat.find (hex n a)) : A → E) a
  have hQmeas : ∀ n, Measurable (Q n) := by
    intro n
    have hi : Measurable (fun a : A =>
      (hF.approx (Nat.find (hex n a)) : A → E) a) := by
      exact Measurable.find
        (fun k => (hF.approx k).measurable)
        (hpmeas n) (hex n)
    exact hi
  have hQrange : ∀ n, (Set.range (Q n)).Countable := by
    intro n
    have hs : (Set.range (Q n)) ⊆
        ⋃ k : ℕ, Set.range (hF.approx k : A → E) := by
      rintro y ⟨a,rfl⟩
      refine Set.mem_iUnion.2 ⟨Nat.find (hex n a), ?_⟩
      exact ⟨a, rfl⟩
    exact (Set.countable_iUnion
      (fun k => (hF.approx k).finite_range.countable)).mono hs
  refine ⟨Q, (fun n => ⟨(stronglyMeasurable_iff_measurable_separable).2
    ⟨hQmeas n, (hQrange n).isSeparable⟩, hQrange n⟩), ?_⟩
  intro n a
  exact Nat.find_spec (hex n a)

end HRS.MS.R26T6C
