import HRS.MS.Fp81S21PredMap10
import HRS.MS.R2InterpAux13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Identify a chart-coefficient prediction with the physical propagator
prediction whenever the chart and physical functionals agree on compact tests. -/
theorem fp81s21_predicted_chart_at
    {d r : ℕ} {Pw m T : ℝ} {C : WholeCoeff d} {c : MultiIndex d → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hlin : S102Lin C m T) (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (w : OscPath d m T)
    (Q : ℝ → (Euc d → ℝ) → ℝ) {u t : ℝ}
    (hu : u ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (hQ : S102Z r Pw (Q u))
    (hagree : ∀ f, IsR2Test f → fp81s21_chartAction E z f = Q u f)
    (hmatch : r2Vprop C m u u (Q u) = r2PathAt w u) :
    r2PathAt (r2Predicted C w Q u) t =
      if t ≤ u then r2PathAt w t
      else r2Vprop C m t u (fp81s21_chartAction E z) := by
  have hp := s102_predicted_at hP hD hlin w Q hu hQ hmatch ht
  rw [hp]
  split_ifs with htu
  · rfl
  · have htu' : u ≤ t := (not_le.mp htu).le
    have htt : t ∈ Icc u T := ⟨htu', ht.2⟩
    have hphysical := fp81s21_chartVprop_physical hP hD hlin E z (Q u)
      hQ hagree hu htt
    exact hphysical.symm

#print axioms HRS.Fp81.S21.fp81s21_predicted_chart_at

end HRS.Fp81.S21
