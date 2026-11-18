import HRS.MS.SA12Z3NearN7C
import HRS.MS.UniqN2bC
import HRS.MS.UniqN3aH

/-!
# S.A.12 N7 (SA12Z3), part D: real `L²` plumbing

* `sa12z3_pair`: `|∫ om² u X| ≤ (∫ W u²)^{1/2} (∫ (1_B X)²)^{1/2}` for `om² ≤ W`, `supp om ⊆ B`;
* `sa12z3_hess_real`, `sa12z3_first_real`: the local operator bounds (N1 and `n0_kcd_local`) in real form;
* `sa12z3_close`: the arithmetic closing one term of the energy estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_eLp_eq {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, one_div, Real.norm_eq_abs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq_abs]

theorem sa12z3_memLp_ind {X : Euc d → ℝ} (hX : Continuous X) (c : Euc d) (R : ℝ) :
    MemLp ((closedBall c R).indicator X) 2 volume := by
  have hm : AEStronglyMeasurable ((closedBall c R).indicator X) volume :=
    (hX.aestronglyMeasurable).indicator measurableSet_closedBall
  rw [memLp_two_iff_integrable_sq hm]
  have h1 : Integrable (fun x => X x ^ 2) (volume.restrict (closedBall c R)) :=
    (hX.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall c R)
  have h2 : Integrable ((closedBall c R).indicator (fun x => X x ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 h1
  refine h2.congr (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall c R <;> simp [Set.indicator, hx]

theorem sa12z3_l2_of_eLp {g v : Euc d → ℝ} (hg : MemLp g 2 volume) (hv : MemLp v 2 volume) {K : ℝ}
    (hK : 0 ≤ K) (h : eLpNorm g 2 volume ≤ ENNReal.ofReal K * eLpNorm v 2 volume) :
    Real.sqrt (∫ x, g x ^ 2) ≤ K * Real.sqrt (∫ x, v x ^ 2) := by
  rw [sa12z3_eLp_eq hg, sa12z3_eLp_eq hv, ← ENNReal.ofReal_mul hK] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- The pairing bound. -/
theorem sa12z3_pair {c : Euc d} {R : ℝ} {om W u X : Euc d → ℝ} (homc : Continuous om)
    (homcs : HasCompactSupport om) (homs : Function.support om ⊆ closedBall c R)
    (hom1 : ∀ x, |om x| ≤ 1) (hWc : Continuous W) (hWcs : HasCompactSupport W)
    (hWom : ∀ x, om x ^ 2 ≤ W x) (huc : Continuous u) (hX : Continuous X) :
    |∫ x, om x ^ 2 * (u x * X x)| ≤
      Real.sqrt (∫ x, W x * u x ^ 2) * Real.sqrt (∫ x, ((closedBall c R).indicator X x) ^ 2) := by
  set f : Euc d → ℝ := fun x => om x ^ 2 * u x with hf
  set g : Euc d → ℝ := (closedBall c R).indicator X with hg
  have hfc : Continuous f := (homc.pow 2).mul huc
  have hfcs : HasCompactSupport f := by
    have : HasCompactSupport (fun x => om x ^ 2) := homcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact this.mul_right
  have hfL : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfcs
  have hgL : MemLp g 2 volume := sa12z3_memLp_ind hX c R
  have hpt : ∀ x, om x ^ 2 * (u x * X x) = f x * g x := by
    intro x
    by_cases hx : x ∈ closedBall c R
    · simp [hf, hg, Set.indicator, hx]; ring
    · have : om x = 0 := by
        by_contra h
        exact hx (homs (Function.mem_support.2 h))
      simp [hf, hg, Set.indicator, hx, this]
  simp_rw [hpt]
  refine (HRS.MS.UniqN3a.cs_real hfL hgL).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  have hWu : Integrable (fun x => W x * u x ^ 2) volume :=
    ((hWc.mul (huc.pow 2)).integrable_of_hasCompactSupport hWcs.mul_right)
  refine integral_mono hfL.integrable_sq hWu fun x => ?_
  have h1 : om x ^ 2 ≤ 1 := by
    have := hom1 x
    nlinarith [abs_nonneg (om x), sq_abs (om x)]
  have h2 : (om x ^ 2) ^ 2 ≤ W x := by
    have := hWom x
    have h0 : 0 ≤ om x ^ 2 := sq_nonneg _
    nlinarith
  show (om x ^ 2 * u x) ^ 2 ≤ W x * u x ^ 2
  calc (om x ^ 2 * u x) ^ 2 = (om x ^ 2) ^ 2 * u x ^ 2 := by ring
    _ ≤ W x * u x ^ 2 := by gcongr

/-- N1 in real form. -/
theorem sa12z3_hess_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) :
    ∃ C C₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₀ ∧ ∀ (i j : Fin d) (R : ℝ), 1 ≤ R → ∀ (c : Euc d) (v : Euc d → ℝ),
      MemCb 2 v → Function.support v ⊆ closedBall c R →
      Real.sqrt (∫ x, ((closedBall c R).indicator (hessRiesz d s i j v) x) ^ 2) ≤
        C * R ^ C₀ * Real.sqrt (∫ x, v x ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, h⟩ := hess_local_finite d hd s hs0 hs2
  refine ⟨C, C₀, hC.le, hC₀, fun i j R hR c v hv hsupp => ?_⟩
  have hsd : s < d := by linarith
  obtain ⟨hv2, hvc⟩ := sa12z3_memCb_cc hv hsupp
  have hcont : Continuous (hessRiesz d s i j v) := by
    have hf : hessRiesz d s i j v = fun y => D1 i (HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v) y :=
      funext fun x => sa12z3_hess_eq hs0 hsd i j hv2 hvc x
    rw [hf]
    exact HRS.MS.UniqN1c.n1c_D1_kcd_cont hs0 hsd hv2 hvc j i
  refine sa12z3_l2_of_eLp (sa12z3_memLp_ind hcont c R) (hv2.continuous.memLp_of_hasCompactSupport hvc)
    (by positivity) ?_
  exact h i j R hR c v hv hsupp c R le_rfl

/-- The first-order local bound in real form (`s ≤ d - 1`). -/
theorem sa12z3_first_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s ≤ (d : ℝ) - 1) :
    ∃ C C₀ : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (R : ℝ), 1 ≤ R → ∀ (c : Euc d) (v : Euc d → ℝ),
      ContDiff ℝ 1 v → HasCompactSupport v → Function.support v ⊆ closedBall c R →
      Real.sqrt (∫ x, ((closedBall c R).indicator (firstRiesz d s i v) x) ^ 2) ≤
        C * R ^ C₀ * Real.sqrt (∫ x, v x ^ 2) := by
  obtain ⟨C₀, C, h⟩ := HRS.MS.UniqN0.n0_kcd_local hd hs0 hsd
  refine ⟨|C|, C₀, abs_nonneg _, fun i R hR c v hv hvc hsupp => ?_⟩
  have hK : firstRiesz d s i v = HRS.Whole.AppendixALemmas.kernelConvDeriv d s i v :=
    funext fun x => sa12z3_firstRiesz_eq' hs0 hsd i hv hvc x
  have hcont : Continuous (firstRiesz d s i v) := by
    rw [hK]
    exact K_cont hs0 hsd ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (D1_supp hvc i)
  have hvL : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  have h1 := h i R hR c v hv hvc hsupp c R le_rfl
  rw [HRS.MS.UniqN2b.n2b_kgOrder_zero hs1, HRS.MS.UniqM1.sobolevNormE_zero_eq hvL, ← hK] at h1
  have hR0 : 0 < R ^ C₀ := Real.rpow_pos_of_pos (by linarith) _
  refine sa12z3_l2_of_eLp (sa12z3_memLp_ind hcont c R) hvL (by positivity) ?_
  refine h1.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) bot_le)
  exact mul_le_mul_of_nonneg_right (le_abs_self C) hR0.le

/-- Closing one term. -/
theorem sa12z3_close {A1 A2 e K κ : ℝ} (he : 0 ≤ e) (hκ : 0 ≤ κ) (hA2nn : 0 ≤ A2)
    (h1 : A1 ≤ Real.sqrt e) (hA1 : 0 ≤ A1) (h2 : A2 ≤ K * Real.sqrt (κ * e)) :
    A1 * A2 ≤ K * Real.sqrt κ * e := by
  have hA2 : A2 ≤ K * (Real.sqrt κ * Real.sqrt e) := by
    rwa [Real.sqrt_mul hκ] at h2
  calc A1 * A2 ≤ Real.sqrt e * (K * (Real.sqrt κ * Real.sqrt e)) :=
        mul_le_mul h1 hA2 hA2nn (Real.sqrt_nonneg _)
    _ = K * Real.sqrt κ * (Real.sqrt e * Real.sqrt e) := by ring
    _ = K * Real.sqrt κ * e := by rw [Real.mul_self_sqrt he]

end HRS.MH.AdjointRd.Phase2SA12Near
