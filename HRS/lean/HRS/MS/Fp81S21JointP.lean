import HRS.MS.Fp81S21QuadPoly
import HRS.MS.Fp81S21RankKernel
import HRS.MS.Fp81S21SmoothSqErr
import HRS.MS.Fp81S21TimeRep2
import HRS.MS.ProClosureS111PhysicalWick
import HRS.MS.S21E_Wick

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

abbrev fp81s21_jointP_U (H : ℝ) :=
  Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))

abbrev fp81s21_jointP_X (p : Parameters) (H : ℝ) :=
  OscPath p.d (wholeSpaceIndex p.d : ℝ) H

abbrev fp81s21_jointP_CH (H : ℝ) := fp81s21_SmoothCH H

/-- The chart coordinate functional on an oscillator state, using the chart's
actual test at coordinate `j`. -/
noncomputable def fp81s21_jointP_evalCLM (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (j : ℕ) : OscDual p.d (wholeSpaceIndex p.d : ℝ) →L[ℝ] ℝ :=
  HRS.Whole.s21eEvalCLM (wholeSpaceIndex p.d : ℝ)
    (r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) (E.test_smooth j)).2

/-- Continuous scalar time history of one charted linear evaluation. -/
noncomputable def fp81s21_jointP_evalCurveCLM (p : Parameters) (H : ℝ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (j : ℕ) : fp81s21_jointP_X p H →L[ℝ] C(Icc (0 : ℝ) H, ℝ) :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) H)
    (fp81s21_jointP_evalCLM p E j)

/-- Convert a scalar continuous time history to one coefficient-basis coordinate. -/
noncomputable def fp81s21_jointP_scalarCoeffCurveCLM (H : ℝ) (j : ℕ) :
    C(Icc (0 : ℝ) H, ℝ) →L[ℝ] C(Icc (0 : ℝ) H, r26t6_Coeff) :=
  ContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) H)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (fp81s21_coeffBasis j))

/-- The projected linear evaluation curve, written in the selected coefficient
chart and in its first `m` basis coordinates. -/
noncomputable def fp81s21_jointP_linearCurveCLM (p : Parameters) (H : ℝ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) (m : ℕ) :
    fp81s21_jointP_X p H →L[ℝ] fp81s21_jointP_CH H :=
  ∑ j : Fin m,
    (fp81s21_jointP_scalarCoeffCurveCLM H j).comp
      (fp81s21_jointP_evalCurveCLM p H E j)

/-- Continuous time dependence of a finite-rank polynomial evaluated on a path. -/
theorem fp81s21_jointP_quadTime_continuous {d : ℕ} (H : ℝ)
    (D : fp81s21_RankKernel d) (x : OscPath d (wholeSpaceIndex d : ℝ) H) :
    Continuous (fun t : Icc (0 : ℝ) H =>
      fp81s21_quadPoly D.c D.u x t) := by
  let ev : Fin D.n → Icc (0 : ℝ) H → ℝ := fun i t =>
    HRS.Whole.s21eEvalCLM (wholeSpaceIndex d : ℝ)
      (fp81s21_isOscTest_of_r2 D.valid i).2 (OscPath.at' x t)
  have hev : ∀ i, Continuous (ev i) := by
    intro i
    have h := (HRS.Whole.s21eEvalCLM (wholeSpaceIndex d : ℝ)
      (fp81s21_isOscTest_of_r2 D.valid i).2).continuous.comp x.continuous
    change Continuous (fun t : Icc (0 : ℝ) H =>
      HRS.Whole.s21eEvalCLM (wholeSpaceIndex d : ℝ)
        (fp81s21_isOscTest_of_r2 D.valid i).2 (OscPath.at' x t))
    exact h
  have hs : Continuous (fun t : Icc (0 : ℝ) H =>
      (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j * ev i t * ev j t) := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro i hi
    apply continuous_finset_sum
    intro j hj
    exact (continuous_const.mul (hev i)).mul (hev j)
  convert hs using 1
  funext t
  simp [fp81s21_quadPoly, ev, OscPath.at', HRS.Whole.s21eEvalCLM_apply]

/-- The raw projected quadratic time curve. Each kernel contributes its raw
quadratic polynomial as one coefficient; no law-dependent centering occurs. -/
noncomputable def fp81s21_jointP_quadCurve {p : Parameters} (H : ℝ) (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p.d)
    (x : fp81s21_jointP_X p H) : fp81s21_jointP_CH H :=
  ∑ j : Fin m,
    ⟨fun t => fp81s21_quadPoly (D j).c (D j).u x t • fp81s21_coeffBasis j,
      (fp81s21_jointP_quadTime_continuous H (D j) x).smul continuous_const⟩

/-- The finite-dimensional joint map consumed by the joint averaging and
separately-centered lifting interfaces. Its second component is raw. -/
noncomputable def fp81s21_jointP_map {p : Parameters} (H : ℝ) (hH : 0 < H)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d) :
    fp81s21_jointP_X p H → fp81s21_jointP_U H × fp81s21_jointP_U H :=
  fun x =>
    (fp81s21_timeProject H m
      (fp81s21_smoothPathToL2 H hH (fp81s21_jointP_linearCurveCLM p H E m x)),
     fp81s21_timeProject H m
      (fp81s21_smoothPathToL2 H hH (fp81s21_jointP_quadCurve H m D x)))

#print axioms fp81s21_jointP_quadTime_continuous

end HRS.Fp81.S21
