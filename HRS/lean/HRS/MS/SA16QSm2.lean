import HRS.MS.SA16QSm1
import HRS.MS.SA16QHls1
import HRS.MH.AdjointRdDefs

/-!
# S.A.16 (SA16Q), E6 part 8: the smooth coefficient case, decomposition of `eucNonlocal`

`sa16q_SB a`: `a` smooth with every iterated derivative bounded (such `a` multiplies Schwartz
functions into Schwartz functions).  For `a` in this class and `u ∈ 𝓢`, `d ≥ 2`, `0 ≤ s ≤ d - 2`:

`eucNonlocal s M a u x = ∑_{ij} M_{ji} ( ∂_i ∂_j (g * P) - ∂_i (g * Q_j) )(x)`,  `P = a u`, `Q_j = (∂_j a) u`

(the identity `a ∂_j u = ∂_j(a u) - (∂_j a) u`, integration by parts on the source).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section SB
variable {d : ℕ}

/-- smooth with all iterated derivatives bounded -/
def sa16q_SB (a : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ a ∧ ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n a x‖ ≤ B

lemma sa16q_SB_temperate {a : Euc d → ℝ} (h : sa16q_SB a) : a.HasTemperateGrowth :=
  ⟨h.1, fun n => by obtain ⟨B, hB⟩ := h.2 n; exact ⟨0, B, fun x => by simpa using hB x⟩⟩

lemma sa16q_SB_pd {a : Euc d → ℝ} (h : sa16q_SB a) (e : Euc d) :
    sa16q_SB (fun x => fderiv ℝ a x e) := by
  have hf : ContDiff ℝ ∞ (fderiv ℝ a) := h.1.fderiv_right (m := ∞) (by simp)
  refine ⟨hf.clm_apply contDiff_const, fun n => ?_⟩
  obtain ⟨B, hB⟩ := h.2 (n + 1)
  refine ⟨‖e‖ * B, fun x => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ a) (c := e) (x := x)
    (N := ∞) (n := n) hf.contDiffAt (by exact_mod_cast le_top)
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)

lemma sa16q_SB_sub {a b : Euc d → ℝ} (ha : sa16q_SB a) (hb : sa16q_SB b) :
    sa16q_SB (fun x => a x - b x) := by
  refine ⟨ha.1.sub hb.1, fun n => ?_⟩
  obtain ⟨B1, h1⟩ := ha.2 n
  obtain ⟨B2, h2⟩ := hb.2 n
  refine ⟨B1 + B2, fun x => ?_⟩
  show ‖iteratedFDeriv ℝ n (a - b) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((ha.1.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((hb.1.of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact (norm_sub_le _ _).trans (add_le_add (h1 x) (h2 x))

/-- the Schwartz function `a u` -/
def sa16q_mulS {a : Euc d → ℝ} (h : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℝ) :=
  SchwartzMap.smulLeftCLM ℝ a u

lemma sa16q_mulS_apply {a : Euc d → ℝ} (h : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    sa16q_mulS h u x = a x * u x := by
  simp [sa16q_mulS, SchwartzMap.smulLeftCLM_apply_apply (sa16q_SB_temperate h)]

open LineDeriv in
/-- the Schwartz function `∂_e u` -/
def sa16q_dS (e : Euc d) (u : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℝ) := ∂_{e} u

lemma sa16q_dS_apply (e : Euc d) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    sa16q_dS e u x = fderiv ℝ u x e := by
  unfold sa16q_dS
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

end SB

section Decomp
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

lemma sa16q_conv_int_sw (ψ : 𝓢(Euc d, ℝ)) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y) * ψ y) := by
  obtain ⟨C, hC, hd1, hc, hD, hD'⟩ := sa16q_schwartz_hyp ψ
  have h := sa16q_conv_integrable (sa16q_g_meas d s) (sa16q_g_WI hd hs hs2) hC ψ.continuous hD x
  have := h.comp_sub_left x
  simpa [sub_sub_cancel] using this

/-- the function `x ↦ ∂_e (g * ψ) (x)` is `g * ∂_e ψ` -/
lemma sa16q_fderiv_conv_fun (ψ : 𝓢(Euc d, ℝ)) (e : Euc d) :
    (fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) x e) =
      HRS.Whole.convFun (rieszKernel d s) ⇑(sa16q_dS e ψ) := by
  funext x
  rw [(sa16q_conv_fderiv_schwartz hd hs hs2 ψ x e).2]
  congr 1

theorem sa16q_F_decomp (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha : sa16q_SB a)
    (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M a u x =
      ∑ i : Fin d, ∑ j : Fin d, M j i *
        (fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_mulS ha u)) y
            (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) -
          fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
            (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u)) x
            (EuclideanSpace.single i (1 : ℝ))) := by
  unfold HRS.MH.AdjointRd.eucNonlocal
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
  set P := sa16q_mulS ha u with hP
  set Q := sa16q_mulS (sa16q_SB_pd ha e) u with hQ
  have hPfun : ⇑P = fun y => a y * u y := funext (sa16q_mulS_apply ha u)
  have hQfun : ∀ y, Q y = fderiv ℝ a y e * u y := fun y => sa16q_mulS_apply (sa16q_SB_pd ha e) u y
  have hdiffA : DifferentiableAt ℝ
      (fun x' => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) P) x' e) x := by
    rw [sa16q_fderiv_conv_fun hd hs hs2 P e]
    exact (sa16q_conv_fderiv_schwartz hd hs hs2 (sa16q_dS e P) x 0).1
  have hdiffB : DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) Q) x :=
    (sa16q_conv_fderiv_schwartz hd hs hs2 Q x 0).1
  have key : (fun x' => ∫ y, rieszKernel d s (x' - y) * (a y * fderiv ℝ (⇑u) y e)) =
      fun x' => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) P) x' e -
        HRS.Whole.convFun (rieszKernel d s) Q x' := by
    funext x'
    rw [show fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) P) x' e =
        HRS.Whole.convFun (rieszKernel d s) ⇑(sa16q_dS e P) x' from
      congrFun (sa16q_fderiv_conv_fun hd hs hs2 P e) x']
    simp only [HRS.Whole.convFun]
    have i1 : Integrable (fun y => rieszKernel d s (x' - y) * (sa16q_dS e P) y) :=
      sa16q_conv_int_sw hd hs hs2 _ x'
    have i2 : Integrable (fun y => rieszKernel d s (x' - y) * Q y) := sa16q_conv_int_sw hd hs hs2 _ x'
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [sa16q_dS_apply, hQfun, hPfun]
    have hd1 : HasFDerivAt (fun y => a y * u y) (a y • fderiv ℝ u y + u y • fderiv ℝ a y) y :=
      (ha.1.differentiable (by simp) y).hasFDerivAt.mul (u.differentiableAt.hasFDerivAt)
    rw [hd1.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [key]
  rw [fderiv_fun_sub hdiffA hdiffB]
  rfl

end Decomp

end HRS.Whole.AppendixA.Phase2SA16Q
