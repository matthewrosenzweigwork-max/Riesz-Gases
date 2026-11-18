import HRS.MS.R2InterpAux43
import HRS.MS.R2InterpAux13

/-!
# S10.2 (worker S102), part 75: the predicted path at the horizon is the path itself (input `hE1` of the particle packet)
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

theorem s102_predicted_T (w : OscPath d m T) (z : ℝ → (Euc d → ℝ) → ℝ) : r2Predicted C w z T = w := by
  classical
  set f : ℝ → OscDual d m := fun t => if t ≤ T then r2PathAt w t else r2Vprop C m t T (z T) with hfdef
  have hc : ContinuousOn f (Icc 0 T) := by
    have : ContinuousOn (fun t => r2PathAt w t) (Icc 0 T) := by
      rw [continuousOn_iff_continuous_restrict]
      have : (Icc 0 T).domRestrict (fun t => r2PathAt w t) = fun t : Icc (0 : ℝ) T => OscPath.at' w t := by
        funext t; exact s102_r2PathAt_of_mem w t.2
      rw [this]
      exact w.continuous
    refine this.congr fun t ht => ?_
    simp [hfdef, ht.2]
  refine ContinuousMap.ext (fun t => ?_)
  have h1 := s102_windowPathOf_at (m := m) (T := T) hc t.2
  have h2 : f t = OscPath.at' w t := by
    simp only [hfdef, if_pos t.2.2]
    exact s102_r2PathAt_of_mem w t.2
  have h3 : r2PathAt (r2Predicted C w z T) t = OscPath.at' (r2Predicted C w z T) t :=
    s102_r2PathAt_of_mem _ t.2
  have : OscPath.at' (r2Predicted C w z T) t = OscPath.at' w t := by
    rw [← h3]
    exact h1.trans h2
  exact this

/-- The observations of the predicted path at the horizon are those of the path (`hE1`). -/
theorem s102_hE1 {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) :
    s102_Y C m T P X ζ T = zetaPathW m T 0 P X ζ :=
  s102_predicted_T _ _

end HRS.MS.R2Interp

end
