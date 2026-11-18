import HRS.MS.S21F_D00
import HRS.MS.Fp81S21EmbedField11

/-! Generic coefficient-space facts used by the weighted generator adjoint. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open scoped RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The coefficient Hilbert space used by both weighted charts. -/
abbrev fp81s21_F := r26t6_Coeff

/-- Input regularity indices in the B3 generator statement. -/
abbrev fp81s21_q (p : Parameters) : ℕ := 2 * p.d + 6

/-- Input polynomial weight in the B3 generator statement. -/
abbrev fp81s21_P (p : Parameters) : ℝ := (p.d : ℝ) + 2

/-- The full finite-norm test class on which the primal action is specified. -/
abbrev fp81s21_Input (p : Parameters) (f : Euc p.d → ℝ) : Prop :=
  IsR2WeightedTest (fp81s21_q p + 2) (fp81s21_P p) f

/-- The bounded primal family and its exact action on all input tests. -/
def fp81s21_primal
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (A : ℝ) (T : ℝ → fp81s21_F →L[ℝ] fp81s21_F) : Prop :=
  ∀ u, ‖T u‖ ≤ A ∧ ∀ f, fp81s21_Input p f →
    T u (E.encode f) =
      Es.encode (generatorW (r26t3_coeff R) (max u 0) f)

/-- A Hilbert adjoint's coordinate is its action on the corresponding chart
basis test. -/
theorem fp81s21_adjoint_test_coordinate
    {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw)
    (T : fp81s21_F →L[ℝ] fp81s21_F)
    (z : fp81s21_F) (j : ℕ) :
    (T.adjoint z) j = inner ℝ z (T (E.encode (E.test j))) := by
  have htest : E.encode (E.test j) =
      (lp.single 2 j (1 : ℝ) : fp81s21_F) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  have hadj :
      inner ℝ (T.adjoint z) (lp.single 2 j (1 : ℝ)) =
        inner ℝ z (T (lp.single 2 j (1 : ℝ))) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    (T.adjoint z) j =
        inner ℝ (T.adjoint z) (lp.single 2 j (1 : ℝ)) := by
          simp [lp.inner_single_right]
    _ = inner ℝ z (T (lp.single 2 j (1 : ℝ))) := hadj
    _ = inner ℝ z (T (E.encode (E.test j))) := by rw [← htest]

#print axioms HRS.Fp81.S21.fp81s21_adjoint_test_coordinate

end HRS.Fp81.S21
