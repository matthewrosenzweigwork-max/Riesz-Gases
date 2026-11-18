import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovForceAux6
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD14A
import HRS.MS.S67NlBD14B

/-!
# S6.7 nonlinear, packet S6.7nl.14C: compact punctured-ball integration by parts with the annular correction

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4221-4245, 4751-4763, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definition: `s67bd_cutoffCorrection`.
Route: multiply `h` by a smooth bump `chi` equal to `1` on the ball `B(x,3)` with support in
`B(x,4)`; the product `u = chi h` is `C^1` with compact support, hence has a Gaussian envelope,
and the merged `movb2_force_split` applies to it. The near integral of `u` equals that of `h`;
the local integral agrees on `B(x,2)`; and `kfar` vanishes on `|z| < 1` while it equals
`partial_i g` on `|z| > 2`, so `kfar(x-y) u(y) - (tail_u)_i` is exactly
`cutoffCorrection(x-y) h(y)` (both vanish where `u` and `h` differ).
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

def s67bd_cutoffCorrection (d : ℕ) (s : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  if ‖z‖ ≤ 1 / 4 then 0 else movb2_kfar d s i z - rieszKernelGrad d s z i

lemma s67bd14c_GA {x : Euc d} {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hcs : HasCompactSupport u)
    {R : ℝ} (hR : tsupport u ⊆ Metric.closedBall x R) : ∃ E, movb2_GA 1 1 E u := by
  obtain ⟨M0, hM0⟩ := (hcs.iteratedFDeriv 0).exists_bound_of_continuous
    (hu.continuous_iteratedFDeriv (by norm_num))
  obtain ⟨M1, hM1⟩ := (hcs.iteratedFDeriv 1).exists_bound_of_continuous
    (hu.continuous_iteratedFDeriv (by norm_num))
  set M : ℝ := max (max M0 M1) 0 with hM
  have hM00 : 0 ≤ M := le_max_right _ _
  set R' : ℝ := ‖x‖ + |R| with hR'
  refine ⟨M * Real.exp (R' ^ 2), fun i hi y => ?_⟩
  have hbound : ‖iteratedFDeriv ℝ i u y‖ ≤ M := by
    interval_cases i
    · exact (hM0 y).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hM1 y).trans ((le_max_right _ _).trans (le_max_left _ _))
  by_cases hy : iteratedFDeriv ℝ i u y = 0
  · rw [hy, norm_zero]; positivity
  · have hmem : y ∈ tsupport u :=
      support_iteratedFDeriv_subset (𝕜 := ℝ) i (Function.mem_support.2 hy)
    have hyb : ‖y‖ ≤ R' := by
      have := hR hmem
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      calc ‖y‖ = ‖(y - x) + x‖ := by simp
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ R' := by rw [hR']; linarith [le_abs_self R]
    have h1 : R' ^ 2 - ‖y‖ ^ 2 ≥ 0 := by nlinarith [norm_nonneg y, norm_nonneg x, abs_nonneg R]
    have h2 : 1 ≤ Real.exp (R' ^ 2 - ‖y‖ ^ 2) := Real.one_le_exp h1
    calc ‖iteratedFDeriv ℝ i u y‖ ≤ M := hbound
      _ ≤ M * Real.exp (R' ^ 2 - ‖y‖ ^ 2) := le_mul_of_one_le_right hM00 h2
      _ = M * Real.exp (R' ^ 2) * Real.exp (-1 * ‖y‖ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma s67bd14c_T_eq (κ w : Euc d → ℝ) (x : Euc d) :
    movb2_T κ w x = ∫ y, κ (x - y) * w y := by
  unfold movb2_T
  rw [← integral_sub_left_eq_self (fun z => κ z * w (x - z)) volume x]
  simp only [sub_sub_cancel]

lemma s67bd14c_kfar_near (s : ℝ) (i : Fin d) {z : Euc d} (hz : ‖z‖ < 1) :
    movb2_kfar d s i z = 0 := by
  unfold movb2_kfar
  have h : movb2_gfar d s =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    exact movb2_gfar_eq_zero (mem_ball_zero_iff.1 hw).le
  rw [h.fderiv_eq]; simp

lemma s67bd14c_kfar_far (s : ℝ) (i : Fin d) {z : Euc d} (hz : 2 < ‖z‖) :
    movb2_kfar d s i z = rieszKernelGrad d s z i := by
  unfold movb2_kfar rieszKernelGrad
  have h : movb2_gfar d s =ᶠ[𝓝 z] rieszKernel d s := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact movb2_gfar_eq_g (le_of_lt hw)
  rw [h.fderiv_eq, movtr_gradient_apply]

theorem s67bd_compact_force_ibp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Euc d → ℝ) (hh : ContDiff ℝ 1 h) (hI : Integrable h volume)
    (x : Euc d) (i : Fin d)
    (hnear : Integrable (s67bd_near d s h x) volume)
    (hloc : Integrable (fun y => movb2_gloc d s (x - y) * s67bd_D i h y) volume) :
    Integrable (fun y => s67bd_cutoffCorrection d s i (x - y) * h y) volume ∧
    (∫ y, s67bd_near d s h x y) i = s67bd_local d s h i x +
      ∫ y, s67bd_cutoffCorrection d s i (x - y) * h y := by
  have hd1 : 1 ≤ d := by omega
  let χ : ContDiffBump x := ⟨3, 4, by norm_num, by norm_num⟩
  have hχ1 : ∀ y, ‖x - y‖ ≤ 3 → χ y = 1 := fun y hy =>
    χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]; exact hy)
  set u : Euc d → ℝ := fun y => χ y * h y with hu
  have huC1 : ContDiff ℝ 1 u := (χ.contDiff (n := 1)).mul hh
  have hcs : HasCompactSupport u := χ.hasCompactSupport.mul_right
  have huI : Integrable u volume := huC1.continuous.integrable_of_hasCompactSupport hcs
  have hueq : ∀ y, ‖x - y‖ ≤ 3 → u y = h y := fun y hy => by
    simp only [hu, hχ1 y hy, one_mul]
  have hudiff : ∀ y, ‖x - y‖ < 3 → fderiv ℝ u y = fderiv ℝ h y := fun y hy => by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball x 3 by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hy)] with w hw
    exact hueq w (by rw [← dist_eq_norm, dist_comm]; exact (Metric.mem_ball.1 hw).le)
  have hts : tsupport u ⊆ Metric.closedBall x 4 := by
    have h1 : tsupport u ⊆ tsupport χ := tsupport_mul_subset_left
    rw [χ.tsupport_eq] at h1
    exact h1
  obtain ⟨E, hGA⟩ := s67bd14c_GA huC1 hcs hts
  have hsplit := movb2_force_split hd1 hs0 hsd one_pos huC1 hGA i x
  obtain ⟨htail, hpair⟩ := s67bd_tail_local_integrable hd hs0 hsd u huC1 huI x
  obtain ⟨_, hkint⟩ := hpair i
  have hnu : s67bd_near d s u x = s67bd_near d s h x := by
    funext y
    unfold s67bd_near
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · rw [if_pos hy, if_pos hy, hueq y (by linarith), hueq x (by simp)]
    · rw [if_neg hy, if_neg hy]
  have hmf : movForce d s u x = (∫ y, s67bd_near d s h x y) + ∫ y, s67bd_tail d s u x y := by
    unfold movForce convGradConvW
    rw [← hnu, ← integral_add (hnu ▸ hnear) htail]
    congr 1
    funext y
    unfold s67bd_near s67bd_tail
    split_ifs <;> simp
  have hcomp : ∀ F : Euc d → Euc d, Integrable F volume → (∫ y, F y) i = ∫ y, F y i := by
    intro F hF
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hF
    simpa using this.symm
  have hnearcomp := hcomp _ hnear
  have htailcomp := hcomp _ htail
  have hmfi : (movForce d s u x) i = (∫ y, s67bd_near d s h x y) i + (∫ y, s67bd_tail d s u x y) i := by
    rw [hmf]; rfl
  have hlocal : movb2_T (movb2_gloc d s) (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x =
      s67bd_local d s h i x := by
    rw [s67bd14c_T_eq]
    unfold s67bd_local s67bd_D
    congr 1
    funext y
    by_cases hy : ‖x - y‖ < 3
    · rw [hudiff y hy]
    · have : movb2_gloc d s (x - y) = 0 := movb2_gloc_eq_zero (by linarith [not_lt.1 hy])
      rw [this, zero_mul, zero_mul]
  have hkT := s67bd14c_T_eq (movb2_kfar d s i) u x
  have hcorr : ∀ y, s67bd_cutoffCorrection d s i (x - y) * h y =
      movb2_kfar d s i (x - y) * u y - (s67bd_tail d s u x y) i := by
    intro y
    unfold s67bd_cutoffCorrection s67bd_tail
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · rw [if_pos hy, if_pos hy, s67bd14c_kfar_near s i (by linarith)]; simp
    · rw [if_neg hy, if_neg hy]
      simp only [PiLp.smul_apply, smul_eq_mul]
      by_cases hy3 : ‖x - y‖ ≤ 3
      · rw [hueq y hy3]; ring
      · rw [s67bd14c_kfar_far s i (by linarith [not_le.1 hy3])]; ring
  have h1 : Integrable (fun y => (s67bd_tail d s u x y) i) volume :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integrable_comp htail
  have hint : Integrable (fun y => s67bd_cutoffCorrection d s i (x - y) * h y) volume := by
    refine (hkint.sub h1).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    exact (hcorr y).symm
  refine ⟨hint, ?_⟩
  have hint2 : ∫ y, s67bd_cutoffCorrection d s i (x - y) * h y =
      (∫ y, movb2_kfar d s i (x - y) * u y) - ∫ y, (s67bd_tail d s u x y) i := by
    rw [← integral_sub hkint h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hcorr y)
  rw [hlocal, hkT] at hsplit
  linarith

end HRS.MS.BreakdownS67
