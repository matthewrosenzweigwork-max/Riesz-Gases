import HRS.MS.R26T8AP22k
import HRS.MS.R26T8AN2

/-!
# S8.2 local Newton layer, packet T8A.P22 (part l): the smooth remainder and the corrected contract
`r26t8a_p22_S0 B z = 2 nu ∫ K(z-w) c_B(w) dw` is `C^∞`, linear in `B`, with jets bounded by `C ‖B‖` on the closed unit ball (`C` independent of `B`).
`r26t8a_leading_newton_commutator_unif` is the T8A.P22 contract with the constant `C` placed BEFORE `B` (the Pro signature puts `∃ C` after `B`, which makes the bound vacuous).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Convolution
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

def r26t8a_p22_S0 (nu : ℝ) (chi : Euc d → ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (z : Euc d) : ℝ :=
  2 * nu * ∫ w, newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w

theorem r26t8a_p22_Kint (hd : 2 ≤ d) (nu : ℝ) {g : Euc d → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
    (z : Euc d) : Integrable (fun w => newtonKernel d nu (z - w) * g w) := by
  have hloc := r26t8a_N2_locInt (fun r => r26t8a_K_integrableOn hd nu r)
  have hcont : Continuous (fun u : Euc d => g (z - u)) := hg.comp (continuous_const.sub continuous_id)
  have hcs' : HasCompactSupport (fun u : Euc d => g (z - u)) := hcs.comp_homeomorph (Homeomorph.subLeft z)
  have h1 : Integrable (fun u => newtonKernel d nu u * g (z - u)) :=
    hloc.integrable_smul_right_of_hasCompactSupport hcont hcs'
  have h2 := h1.comp_sub_left z
  refine h2.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [sub_sub_cancel]

theorem r26t8a_p22_S0_contDiff (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) : ContDiff ℝ ∞ (r26t8a_p22_S0 nu chi B) := by
  have hloc := r26t8a_N2_locInt (fun r => r26t8a_K_integrableOn hd nu r)
  have hconv' := (r26t8a_p22_cfun_cs nu B hchi).contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
    (μ := (volume : Measure (Euc d))) (n := (⊤ : ℕ∞)) hloc (by exact_mod_cast r26t8a_p22_cfun_contDiff nu B hchi)
  have hconv : ContDiff ℝ ∞ (newtonKernel d nu ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (r26t8a_p22_cfun nu B chi)) := by
    exact_mod_cast hconv'
  have heq : r26t8a_p22_S0 nu chi B = fun z => 2 * nu *
      (newtonKernel d nu ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (r26t8a_p22_cfun nu B chi)) z := by
    funext z
    unfold r26t8a_p22_S0
    congr 1
    rw [convolution_def]
    rw [← integral_sub_left_eq_self (fun w => newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w) volume z]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sub_sub_cancel, ContinuousLinearMap.mul_apply']
  rw [heq]
  exact contDiff_const.mul hconv

theorem r26t8a_p22_S0_add (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    (B1 B2 : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    r26t8a_p22_S0 nu chi (B1 + B2) = fun z => r26t8a_p22_S0 nu chi B1 z + r26t8a_p22_S0 nu chi B2 z := by
  funext z
  unfold r26t8a_p22_S0
  have i1 := r26t8a_p22_Kint hd nu (r26t8a_p22_cfun_contDiff nu B1 hchi).continuous (r26t8a_p22_cfun_cs nu B1 hchi) z
  have i2 := r26t8a_p22_Kint hd nu (r26t8a_p22_cfun_contDiff nu B2 hchi).continuous (r26t8a_p22_cfun_cs nu B2 hchi) z
  rw [← mul_add, ← integral_add i1 i2]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun w => by simp only [r26t8a_p22_cfun_add nu hchi]; ring)

theorem r26t8a_p22_S0_smul (nu c : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    r26t8a_p22_S0 nu chi (c • B) = fun z => c * r26t8a_p22_S0 nu chi B z := by
  funext z
  unfold r26t8a_p22_S0
  have : ∀ w, newtonKernel d nu (z - w) * r26t8a_p22_cfun nu (c • B) chi w =
      c * (newtonKernel d nu (z - w) * r26t8a_p22_cfun nu B chi w) := fun w => by
    rw [r26t8a_p22_cfun_smul nu c hchi]; ring
  simp_rw [this]
  rw [integral_const_mul]
  ring

set_option maxHeartbeats 3200000 in
theorem r26t8a_p22_S0_jets (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), ∀ z ∈ closedBall (0 : Euc d) 1,
      ‖iteratedFDeriv ℝ j (r26t8a_p22_S0 nu chi B) z‖ ≤ C * ‖B‖ := by
  refine r26t8a_p22_unif (isCompact_closedBall (0 : Euc d) 1)
    (fun (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) z => iteratedFDeriv ℝ j (r26t8a_p22_S0 nu chi B) z)
    (fun B1 B2 z _ => ?_) (fun c B z _ => ?_) (fun B => ?_)
  · have e := r26t8a_p22_S0_add hd nu hchi B1 B2
    show iteratedFDeriv ℝ j (r26t8a_p22_S0 nu chi (B1 + B2)) z = _
    rw [e]
    have h1 := (r26t8a_p22_S0_contDiff hd nu hchi B1).of_le (by simp : (j : WithTop ℕ∞) ≤ ∞)
    have h2 := (r26t8a_p22_S0_contDiff hd nu hchi B2).of_le (by simp : (j : WithTop ℕ∞) ≤ ∞)
    exact iteratedFDeriv_add_apply (h1.contDiffAt) (h2.contDiffAt)
  · have e := r26t8a_p22_S0_smul nu c hchi B
    show iteratedFDeriv ℝ j (r26t8a_p22_S0 nu chi (c • B)) z = c • iteratedFDeriv ℝ j (r26t8a_p22_S0 nu chi B) z
    rw [e]
    have h1 := (r26t8a_p22_S0_contDiff hd nu hchi B).of_le (by simp : (j : WithTop ℕ∞) ≤ ∞)
    exact iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := j) (a := c) (f := r26t8a_p22_S0 nu chi B) (x := z) h1.contDiffAt
  · exact ((r26t8a_p22_S0_contDiff hd nu hchi B).continuous_iteratedFDeriv (by simp)).continuousOn

end HRS.MS.R26T8A
