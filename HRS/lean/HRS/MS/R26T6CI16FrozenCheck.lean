import HRS.MS.R26T6CI16
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS
theorem r26t6c_geometric_approximation_frozen_consumer {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] (F : A → E) (hF : StronglyMeasurable F) :
    ∃ Q : ℕ → A → E,
      (∀ n, StronglyMeasurable (Q n) ∧ (Set.range (Q n)).Countable) ∧
      ∀ n a, ‖Q n a - F a‖ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  exact r26t6c_geometric_approximation F hF

#print axioms r26t6c_geometric_approximation
#print axioms r26t6c_geometric_approximation_frozen_consumer
end HRS.MS.R26T6C
