import HRS.MS.Fp81S21WickApprox16
import HRS.MS.R2WinOrbNLAux5
import HRS.MS.GapRefAux2

/-! The first chart-test gradients belong to one bounded velocity ball. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

/-- The first `m` weak-chart tests have smooth gradients in one common
`C_b²` velocity ball. The radius is chosen before the kernel approximation. -/
theorem fp81s21_chart_gradient_velocities
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw) (m : ℕ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ θ : Fin m → HRS.MS.R2S11.s11V d Λ,
      ∀ j : Fin m, (θ j).1 = gradient (E.test j) := by
  have hex : ∀ j : Fin m, ∃ B : ℝ, 0 ≤ B ∧
      ∀ l ≤ 3, ∀ x, ‖iteratedFDeriv ℝ l (E.test j) x‖ ≤ B := by
    intro j
    exact (E.test_smooth j).2.exists_bound_iteratedFDeriv (E.test_smooth j).1 3
  choose B hB hjet using hex
  let Λ : ℝ := ∑ j : Fin m, 3 * B j
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num) (hB j)
  have hvel : ∀ j : Fin m, IsR2VelocityBall d Λ (gradient (E.test j)) := by
    intro j
    refine ⟨HRS.MS.Gap.gap1_contDiff_gradient (E.test_smooth j).1 2, ?_⟩
    have hcb : cbNormVecE 2 (gradient (E.test j)) ≤ ENNReal.ofReal (3 * B j) := by
      convert HRS.MS.R2WinOrbNL.s103n_cb_of_jets
        (n := 2) ((E.test_smooth j).1.of_le (by simp)) (hjet j) using 1 <;> norm_num
    apply hcb.trans
    apply ENNReal.ofReal_le_ofReal
    change 3 * B j ≤ Λ
    exact Finset.single_le_sum (fun i _ => mul_nonneg (by norm_num) (hB i))
      (Finset.mem_univ j)
  exact ⟨Λ, hΛ, fun j => ⟨gradient (E.test j), hvel j⟩, fun _ => rfl⟩

#print axioms fp81s21_chart_gradient_velocities
end HRS.Fp81.S21
end
