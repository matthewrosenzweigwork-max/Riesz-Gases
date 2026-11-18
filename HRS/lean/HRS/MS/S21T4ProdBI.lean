import HRS.MS.S21T4ProdBH
import HRS.MC.IID8

/-!
# R26-T3.S13: linearity of L² convergence of random functions

The convergence is the actual Bochner L² convergence encoded by TendstoL2;
the proof uses the L² seminorm triangle inequality and scalar multiplication.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21t4_tendstoL2_add
    {Fn Hn : ℕ → Ω → ℝ} {F H : Ω → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (Fn n) P)
    (hHm : ∀ n, AEStronglyMeasurable (Hn n) P)
    (hF : TendstoL2 P Fn F) (hH : TendstoL2 P Hn H) :
    TendstoL2 P (fun n ω => Fn n ω + Hn n ω)
      (fun ω => F ω + H ω) := by
  have h1 := hF.tendsto_eLpNorm hFm
  have h2 := hH.tendsto_eLpNorm hHm
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine HRS.MC.IID.tendstoL2_of_tendsto_eLpNorm
    (Qn := fun n ω => Fn n ω + Hn n ω)
    (Q := fun ω => F ω + H ω)
    (by
      have e : (F + H) = (fun ω => F ω + H ω) := by funext ω; rfl
      rw [← e]
      exact hF.1.add hH.1)
    (fun n => by
      have e : (Fn n + Hn n) = (fun ω => Fn n ω + Hn n ω) := by
        funext ω
        rfl
      rw [← e]
      exact (hFm n).add (hHm n)) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h3 (fun _ => bot_le) fun n => ?_
  have e : (fun ω => Fn n ω + Hn n ω) -
      (fun ω => F ω + H ω) = (Fn n - F) + (Hn n - H) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  exact eLpNorm_add_le (by norm_num)

theorem s21t4_tendstoL2_const_mul
    {Fn : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (Fn n) P)
    (hF : TendstoL2 P Fn F) (c : ℝ) :
    TendstoL2 P (fun n ω => c * Fn n ω)
      (fun ω => c * F ω) := by
  have h1 := hF.tendsto_eLpNorm hFm
  have h3 : Tendsto
      (fun n => ‖c‖ₑ * eLpNorm (Fn n - F) 2 P)
      atTop (𝓝 (‖c‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul h1 (Or.inr enorm_ne_top)
  rw [mul_zero] at h3
  refine HRS.MC.IID.tendstoL2_of_tendsto_eLpNorm
    (Qn := fun n ω => c * Fn n ω)
    (Q := fun ω => c * F ω)
    (hF.1.const_mul c) (fun n => (hFm n).const_mul c) ?_
  refine h3.congr fun n => ?_
  have e : (fun ω => c * Fn n ω) - (fun ω => c * F ω) =
      c • (Fn n - F) := by
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, eLpNorm_const_smul]

end HRS.MS.R26T3
