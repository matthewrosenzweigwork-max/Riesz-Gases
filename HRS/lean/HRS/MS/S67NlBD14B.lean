import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.Whole.MovtrAux2
import HRS.MS.MovForceAux6
import HRS.MS.S67NlBD03

/-!
# S6.7 nonlinear breakdown, packet 14B: L1 tail and compact local-potential integrability

`s67bd_tail_local_integrable`: the tail `h(y) ∇g(x-y) 1_{|x-y|>1/4}` is dominated by `C|h|`; the local
potential integrand by `sup_{B(x,2)}|D_i h| · |g_loc(x-·)|`; the far integrand by `K |h|`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_local (d : ℕ) (s : ℝ) (h : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  ∫ y, movb2_gloc d s (x - y) * s67bd_D i h y

def s67bd_far (d : ℕ) (s : ℝ) (h : Euc d → ℝ) (i : Fin d) (x : Euc d) : ℝ :=
  ∫ y, movb2_kfar d s i (x - y) * h y

def s67bd_tail (d : ℕ) (s : ℝ) (h : Euc d → ℝ) (x y : Euc d) : Euc d :=
  if ‖x - y‖ ≤ 1 / 4 then 0 else h y • rieszKernelGrad d s (x - y)

theorem s67bd_tail_local_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Euc d → ℝ) (hh : ContDiff ℝ 1 h) (hI : Integrable h volume) :
    ∀ x, Integrable (s67bd_tail d s h x) volume ∧ ∀ i : Fin d,
      Integrable (fun y => movb2_gloc d s (x - y) * s67bd_D i h y) volume ∧
      Integrable (fun y => movb2_kfar d s i (x - y) * h y) volume := by
  intro x
  have hd1 : 1 ≤ d := by omega
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · -- the tail
    set Ct : ℝ := movtr_sigma s * (1 / 4 : ℝ) ^ (-s - 1) with hCt
    have hCt0 : 0 ≤ Ct := mul_nonneg hσ (Real.rpow_nonneg (by norm_num) _)
    have hmeas : AEStronglyMeasurable (s67bd_tail d s h x) volume := by
      have hm : Measurable (s67bd_tail d s h x) := by
        unfold s67bd_tail
        refine Measurable.ite (measurableSet_le (measurable_const.sub measurable_id).norm
          measurable_const) measurable_const ?_
        exact hh.continuous.measurable.smul
          ((movtr_rieszKernelGrad_measurable s).comp (measurable_const.sub measurable_id))
      exact hm.aestronglyMeasurable
    refine (hI.norm.const_mul Ct).mono' hmeas (Eventually.of_forall fun y => ?_)
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · have : s67bd_tail d s h x y = 0 := by simp only [s67bd_tail, hy, ↓reduceIte]
      rw [this, norm_zero]
      exact mul_nonneg hCt0 (norm_nonneg _)
    · have hy' := not_le.1 hy
      have hz : x - y ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hy'; linarith
      have : s67bd_tail d s h x y = h y • rieszKernelGrad d s (x - y) := by
        simp only [s67bd_tail, hy, ↓reduceIte]
      rw [this, norm_smul, movtr_rieszKernelGrad_norm s hs0 hz]
      have hpow : ‖x - y‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hy'.le (by linarith)
      calc ‖h y‖ * (movtr_sigma s * ‖x - y‖ ^ (-s - 1))
          ≤ ‖h y‖ * (movtr_sigma s * (1 / 4 : ℝ) ^ (-s - 1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hσ) (norm_nonneg _)
        _ = Ct * ‖h y‖ := by rw [hCt]; ring
  · -- the local potential integrand
    obtain ⟨hgl, -⟩ := mv1_gloc_integrable (d := d) hd1 hs0 hsd
    obtain ⟨L, hL⟩ := (isCompact_closedBall x (2 : ℝ)).exists_bound_of_continuousOn
      (hh.continuous_fderiv one_ne_zero).continuousOn
    have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL x (Metric.mem_closedBall_self (by norm_num)))
    have hDc : Continuous (s67bd_D i h) :=
      ((hh.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have hglx : Integrable (fun y => movb2_gloc d s (x - y)) volume :=
      (integrable_comp_sub_left (movb2_gloc d s) x).2 hgl
    refine (hglx.norm.const_mul L).mono'
      (hglx.aestronglyMeasurable.mul hDc.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    by_cases hy : ‖x - y‖ ≤ 2
    · have hmem : y ∈ Metric.closedBall x 2 := by
        rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hy
      have hDy : ‖s67bd_D i h y‖ ≤ L := by
        have h1 := (fderiv ℝ h y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
        have h2 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
        rw [h2, mul_one] at h1
        exact h1.trans (hL y hmem)
      calc ‖movb2_gloc d s (x - y)‖ * ‖s67bd_D i h y‖
          ≤ ‖movb2_gloc d s (x - y)‖ * L := mul_le_mul_of_nonneg_left hDy (norm_nonneg _)
        _ = L * ‖movb2_gloc d s (x - y)‖ := mul_comm _ _
    · have : movb2_gloc d s (x - y) = 0 := movb2_gloc_eq_zero (not_le.1 hy).le
      rw [this]
      simp
  · -- the far potential integrand
    obtain ⟨K, hK0, hK⟩ := movb2_kfar_bound (d := d) (s := s) hs0
    have hkc : Continuous (movb2_kfar d s i) :=
      ((mv1_gfar_smooth (d := d) s).continuous_fderiv (by simp)).clm_apply continuous_const
    have hkm : AEStronglyMeasurable (fun y => movb2_kfar d s i (x - y)) volume :=
      (hkc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    refine (hI.norm.const_mul K).mono' (hkm.mul hh.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    have h1 : |movb2_kfar d s i (x - y)| ≤ K := by
      calc |movb2_kfar d s i (x - y)| = |movb2_kfar d s i (x - y)| * 1 := (mul_one _).symm
        _ ≤ |movb2_kfar d s i (x - y)| * (1 + ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (x - y)]) (abs_nonneg _)
        _ ≤ K := hK i (x - y)
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end HRS.MS.BreakdownS67
