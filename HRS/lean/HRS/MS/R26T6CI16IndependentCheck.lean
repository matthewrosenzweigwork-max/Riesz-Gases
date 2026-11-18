import HRS.MS.R26T6CI16

-- Independently extracted the exact original proposed theorem with no added assumptions.
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS

theorem r26t6c_geometric_approximation_independent_pinned_consumer {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] (F : A → E) (hF : StronglyMeasurable F) :
    ∃ Q : ℕ → A → E,
      (∀ n, StronglyMeasurable (Q n) ∧ (Set.range (Q n)).Countable) ∧
      ∀ n a, ‖Q n a - F a‖ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  exact r26t6c_geometric_approximation F hF


-- A quantitative consequence needed to pass from geometric approximants to summable errors.
theorem r26t6c_i16_successive_norm_bound {A E : Type*}
    [NormedAddCommGroup E] (Q : ℕ → A → E) (F : A → E)
    (hQ : ∀ n a, ‖Q n a - F a‖ ≤ (2 : ℝ) ^ (-(n : ℤ)))
    (n : ℕ) (a : A) :
    ‖Q (n + 1) a - Q n a‖ ≤
      (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-(n : ℤ)) := by
  calc
    ‖Q (n + 1) a - Q n a‖ =
        ‖(Q (n + 1) a - F a) - (Q n a - F a)‖ := by
          congr 1
          abel
    _ ≤ ‖Q (n + 1) a - F a‖ + ‖Q n a - F a‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-(n : ℤ)) :=
      add_le_add (hQ (n + 1) a) (hQ n a)

#print axioms HRS.MS.R26T6C.r26t6c_geometric_approximation
#print axioms HRS.MS.R26T6C.r26t6c_geometric_approximation_independent_pinned_consumer
#print axioms HRS.MS.R26T6C.r26t6c_i16_successive_norm_bound
end HRS.MS.R26T6C
