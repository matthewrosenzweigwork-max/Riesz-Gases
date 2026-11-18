import HRS.MS.Fp81S21WeightedMoments7
import HRS.MS.ProClosureS111ChartTrace
import HRS.MS.R2InterpAux27

/-! The measurable coefficient feature of the gradient evaluations for the
physical weighted chart, with its weighted Bessel bound. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.R2Interp

/-- The coefficient vector of the `k`th derivative evaluation of the chart
basis is jointly measurable, has the required coordinates, and satisfies
the weighted gradient trace bound. -/
theorem fp81s21_gradient_feature
    {d : ℕ} (hd : 1 ≤ d)
    (E : r26t6_WeightedChart d (2 * d + 8) ((d : ℝ) + 2)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ D : Euc d → Fin d → r26t6_Coeff,
        Measurable (Function.uncurry D) ∧
        (∀ x k j, D x k j = gradient (E.test j) x k) ∧
        ∀ x, ∑ k, ‖D x k‖ ^ 2 ≤
          C * jbracket x ^ (2 * ((d : ℝ) + 2)) := by
  have hr : (2 : ℝ) + (d : ℝ) / 2 < ((2 * d + 8 : ℕ) : ℝ) := by
    push_cast
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hreg : (d : ℝ) / 2 + 1 < ((2 * d + 8 : ℕ) : ℝ) := by
    linarith
  have hP : (d : ℝ) < 2 * ((d : ℝ) + 2) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hPw : 0 ≤ (d : ℝ) + 2 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  obtain ⟨C₀, hC₀, hpartial⟩ :=
    physical_chart_partial_trace d (2 * d + 8) ((d : ℝ) + 2) hr hP
  have hgradTrace (x : Euc d) (k : Fin d) :
      Summable (fun j : ℕ => gradient (E.test j) x k ^ 2) ∧
      (∑' j : ℕ, gradient (E.test j) x k ^ 2) ≤
        C₀ ^ 2 * jbracket x ^ (2 * ((d : ℝ) + 2)) := by
    obtain ⟨hs, hb⟩ := hpartial E 1 (by norm_num) (fun _ : Fin 1 => k) x
    have hcoord (j : ℕ) :
        partialDeriv (fun _ : Fin 1 => k) (E.test j) x =
          gradient (E.test j) x k := by
      rw [s102_gradient_apply]
      simp [partialDeriv, iteratedFDeriv_one_apply]
    have hseq :
        (fun j : ℕ => partialDeriv (fun _ : Fin 1 => k) (E.test j) x ^ 2) =
          fun j => gradient (E.test j) x k ^ 2 := by
      funext j
      rw [hcoord j]
    rw [hseq] at hs hb
    exact ⟨hs, hb⟩
  let T : Euc d × Fin d → (Euc d → ℝ) → ℝ :=
    fun q f => gradient f q.1 q.2
  have hZ : ∀ q : Euc d × Fin d, S102Z (2 * d + 8) ((d : ℝ) + 2) (T q) := by
    intro q
    change S102Z (2 * d + 8) ((d : ℝ) + 2)
      (fun f => gradient f q.1 q.2)
    exact s102_Z_gradient hd hPw (2 * d + 8) hreg q.1 q.2
  have hc : ∀ j, Measurable (fun q : Euc d × Fin d => T q (E.test j)) := by
    intro j
    apply measurable_from_prod_countable_left
    intro k
    have hg : Continuous (gradient (E.test j)) :=
      HRS.MH.DualityRd.db1_gradient_continuous
        ((E.test_smooth j).1.of_le (by norm_num))
    exact ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) k).comp hg).measurable
  obtain ⟨q, hqmeas, hqrep⟩ := fp81s21_measurable_riesz hP E T hZ hc
  let D : Euc d → Fin d → r26t6_Coeff := fun x k => q (x, k)
  let C : ℝ := (d : ℝ) * C₀ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Nat.cast_nonneg d) (sq_nonneg C₀)
  refine ⟨C, hC, D, ?_, ?_, ?_⟩
  · have hu : Function.uncurry D = q := rfl
    rw [hu]
    exact hqmeas
  · intro x k j
    exact (hqrep (x, k)).2.1 j
  · intro x
    have hnorm (k : Fin d) :
        ‖D x k‖ ^ 2 ≤ C₀ ^ 2 * jbracket x ^ (2 * ((d : ℝ) + 2)) := by
      have hn := lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (E := fun _ : ℕ => ℝ)
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (D x k)
      have hcoordEq :
          (fun j : ℕ => ‖D x k j‖ ^ 2) =
            fun j => gradient (E.test j) x k ^ 2 := by
        funext j
        simpa [D, T, Real.norm_eq_abs, sq_abs] using
          congrArg (fun y : ℝ => y ^ 2) ((hqrep (x, k)).2.1 j)
      rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num] at hn
      have hn' : ‖D x k‖ ^ 2 = ∑' j : ℕ, ‖D x k j‖ ^ 2 := by
        simpa using hn
      rw [hn', hcoordEq]
      exact (hgradTrace x k).2
    calc
      (∑ k : Fin d, ‖D x k‖ ^ 2) ≤
          ∑ k : Fin d, C₀ ^ 2 * jbracket x ^ (2 * ((d : ℝ) + 2)) :=
        Finset.sum_le_sum fun k _ => hnorm k
      _ = (d : ℝ) * (C₀ ^ 2 * jbracket x ^ (2 * ((d : ℝ) + 2))) := by
        simp
      _ = C * jbracket x ^ (2 * ((d : ℝ) + 2)) := by
        dsimp [C]
        ring

#print axioms HRS.Fp81.S21.fp81s21_gradient_feature

end HRS.Fp81.S21
