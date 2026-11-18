import HRS.MS.Fp81S21WeightedMoments6

/-! Measurable chart Riesz representatives for empirical configurations. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111
open HRS.MS.R2Interp

/-- An admissible weighted-test functional has a measurable chart Riesz
representative when its values on the chart tests are measurable. -/
theorem fp81s21_measurable_riesz
    {d r : ℕ} {Pw : ℝ} {S : Type*} [MeasurableSpace S]
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (T : S → (Euc d → ℝ) → ℝ)
    (hZ : ∀ a, S102Z r Pw (T a))
    (hc : ∀ j, Measurable (fun a => T a (E.test j))) :
    ∃ q : S → r26t6_Coeff, Measurable q ∧
      ∀ a, fp81s21_TestRep E (T a) (q a) := by
  have hrep (a : S) : ∃ z : r26t6_Coeff, fp81s21_TestRep E (T a) z := by
    have hwt (f : Euc d → ℝ) (hf : IsR2Test f) : IsR2WeightedTest r Pw f :=
      (weightedTestSubmodule_iff).1 (weighted_test_of_compact_smooth hP hf)
    obtain ⟨C, hC⟩ := (hZ a).bdd
    let C' := max C 0
    have hC' : 0 ≤ C' := le_max_right C 0
    obtain ⟨z, haction, hcoord, hnorm⟩ :=
      fp81s21_chart_riesz_from_tests_coordinate hP E (T a)
        (fun f g hf hg => (hZ a).add f g (hwt f hf) (hwt g hg))
        (fun c f hf => (hZ a).smul c f (hwt f hf)) C' hC'
        (fun f hf => by
          calc
            |T a f| ≤ C * (weightedSobolevE r Pw f).toReal := hC f (hwt f hf)
            _ ≤ C' * (weightedSobolevE r Pw f).toReal :=
              mul_le_mul_of_nonneg_right (le_max_left C 0)
                (ENNReal.toReal_nonneg))
    exact ⟨z, haction, hcoord, hnorm⟩
  let q : S → r26t6_Coeff := fun a => Classical.choose (hrep a)
  refine ⟨q, fp81s21_coeff_measurable q (fun j => ?_), fun a => ?_⟩
  · have hcoord : ∀ a, q a j = T a (E.test j) := fun a =>
      (Classical.choose_spec (hrep a)).2.1 j
    have heq : (fun a => q a j) = fun a => T a (E.test j) := by
      funext a
      exact hcoord a
    rw [heq]
    exact hc j
  · exact Classical.choose_spec (hrep a)

/-- Every empirical fluctuation configuration has a measurable coefficient
representative, with its all-test action and exact dual norm identities. -/
theorem fp81s21_emp_config_rep
    {d r N : ℕ} {Pw : ℝ}
    (hd : 1 ≤ d) (hPw : 0 ≤ Pw) (hr : (d : ℝ) / 2 < r)
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (hN : 0 < N) (μ : ℝ → Measure (Euc d))
    (hi : ∀ u, Integrable (fun x => jbracket x ^ Pw) (μ u))
    (hm : ∀ j, Measurable (fun u => HRS.Whole.pair (μ u) (E.test j))) :
    ∃ z : ℝ → EucConfig d N → r26t6_Coeff,
      Measurable (Function.uncurry z) ∧
      ∀ u X, fp81s21_TestRep E (r2EmpDistr (μ u) X) (z u X) := by
  let T : ℝ × EucConfig d N → (Euc d → ℝ) → ℝ :=
    fun p => r2EmpDistr (μ p.1) p.2
  have hZ : ∀ p, S102Z r Pw (T p) := by
    intro p
    exact s102_Z_fluct hd hPw r hr hN p.2 (μ p.1) (hi p.1) (Real.sqrt N)
  have hc : ∀ j, Measurable (fun p : ℝ × EucConfig d N => T p (E.test j)) := by
    intro j
    have hsum : Measurable (fun p : ℝ × EucConfig d N =>
        ∑ i, E.test j (p.2 i)) :=
      Finset.measurable_sum _ fun i _ =>
        (E.test_smooth j).1.continuous.measurable.comp
          ((measurable_pi_apply i).comp measurable_snd)
    have hμmeas : Measurable (fun p : ℝ × EucConfig d N =>
        HRS.Whole.pair (μ p.1) (E.test j)) := (hm j).comp measurable_fst
    have hformula :
        (fun p : ℝ × EucConfig d N => T p (E.test j)) =
          (fun p => Real.sqrt N *
            ((N : ℝ)⁻¹ * ∑ i, E.test j (p.2 i) - HRS.Whole.pair (μ p.1) (E.test j))) := by
      funext p
      dsimp [T, HRS.Whole.r2EmpDistr]
      rw [HRS.Whole.pair_empirical hN]
    rw [hformula]
    exact measurable_const.mul ((measurable_const.mul hsum).sub hμmeas)
  obtain ⟨q, hq, hqrep⟩ :=
    fp81s21_measurable_riesz hP E T hZ hc
  refine ⟨fun u X => q (u, X), ?_, fun u X => ?_⟩
  · exact hq
  · exact hqrep (u, X)

#print axioms HRS.Fp81.S21.fp81s21_measurable_riesz
#print axioms HRS.Fp81.S21.fp81s21_emp_config_rep

end HRS.Fp81.S21
