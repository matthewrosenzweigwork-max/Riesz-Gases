import HRS.MS.Fp81S21GaussG4U44
import HRS.MS.Fp81S21WindowSup22

/-! Joint measurability of the finite-combination terminal-derivative kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem fp81s21_g4_combo_gradient_joint_meas
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 ≤ H)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {f : Euc p.d → ℝ} (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f) :
    ∃ V : (ℝ × ℝ) → Euc p.d → Euc p.d,
      Measurable (Function.uncurry V) ∧
      ∀ r q, 0 ≤ r → r ≤ q → q ≤ H → ∀ x,
        V (r, q) x = gradient (r26t3_U R r q
          (generatorW (r26t3_coeff R) q f)) x := by
  classical
  obtain ⟨S, c, rfl⟩ := hf
  have horb (α : MultiIndex p.d) : S104nOrbit (r26t3_coeff R)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) H :=
    s104b_orbit_of_termRegGen hterm R.admissible R.resulting α H hH
  choose V hV hVe using fun α =>
    fp81s21_window_terminal_derivative_gradient_joint_meas (r26t3_coeff R)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) (horb α)
  refine ⟨fun a x => ∑ α ∈ S, c α • V α a x, ?_, ?_⟩
  · exact Finset.measurable_sum S fun α _ => (hV α).const_smul (c α)
  · intro r q hr hrq hqH x
    have hq : 0 ≤ q := hr.trans hrq
    have hreg : ∀ α ∈ S, DifferentiableAt ℝ (r26t3_U R r q
        (generatorW (r26t3_coeff R) q
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x := by
      intro α hα
      have hex := (horb α).ex1 q ⟨hq, hqH⟩
      have hcb := s104n_memCb_prop hex ⟨hr, hrq⟩
      exact (hcb.1.differentiable (by norm_num)) x
    rw [(fp81s21_g4_generator_combo p R hterm hr hrq S c).2.2,
      fp81s21_g4_gradient_sum S c _ x hreg]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hVe α r q hr hrq hqH x]
    rfl

#print axioms fp81s21_g4_combo_gradient_joint_meas
end HRS.Fp81.S21
end
