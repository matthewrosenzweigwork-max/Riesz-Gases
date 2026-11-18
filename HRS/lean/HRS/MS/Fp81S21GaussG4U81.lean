import HRS.MS.Fp81S21GaussG4U13
import HRS.MS.Fp81S21GaussG4U3

/-! Reference-measure input bound for oscillator tests. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Who

theorem fp81s21_g4_input_l2 (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) g →
      MemLp g 2 (HRS.Whole.withDensityReal R.ρβ) ∧
      (∫ x, (g x)^2 ∂HRS.Whole.withDensityReal R.ρβ) ≤
        B * fp81s21_g4_J p.d g := by
  let P : ℝ := 2 * (p.d : ℝ) + 4
  have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hPd : (p.d : ℝ) / 2 < P := by dsimp [P]; linarith
  obtain ⟨C, hC, hc⟩ := fp81s21_g4_weight_to_reference p R hP
  refine ⟨C * (p.d : ℝ)^2, by positivity, ?_⟩
  intro g hg
  have hcb := fp81s21_g4_osc_cb2 p.d hg
  have hJ : 0 ≤ fp81s21_g4_J p.d g := by
    unfold fp81s21_g4_J
    exact sq_nonneg _
  have hcost : wSq P (fun x => ‖g x‖) ≤
      ENNReal.ofReal ((p.d : ℝ)^2 * fp81s21_g4_J p.d g) := by
    calc
      _ ≤ Nsq 1 P g := by
        simpa [Nsq, iteratedFDeriv_zero_apply] using
          (who_wSq_le_Nsq (r := 1) (i := 0) (by omega) P g)
      _ ≤ _ := by
        simpa [fp81s21_g4_J, P] using
          fp81s21_g4_Nsq_cost (le_trans (by decide) p.hd) hPd hcb
  obtain ⟨hm, hi⟩ := hc g hcb.1.continuous _ (by positivity) hcost
  refine ⟨hm, ?_⟩
  calc
    _ ≤ C * ((p.d : ℝ)^2 * fp81s21_g4_J p.d g) := hi
    _ = _ := by ring

#print axioms fp81s21_g4_input_l2
end HRS.Fp81.S21
end
