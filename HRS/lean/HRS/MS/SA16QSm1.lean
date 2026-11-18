import HRS.MS.SA16QKer5
import HRS.MS.SA16StrongWnorm
import HRS.MS.SA16StrongConvN
import HRS.MS.SA16StrongSL4

/-!
# S.A.16 (SA16Q), E6 part 6: the Riesz convolution of a Schwartz function

`G ψ = HRS.Whole.convFun (rieszKernel d s) ψ` for `ψ ∈ 𝓢(ℝ^d)`, `d ≥ 2`, `0 ≤ s ≤ d - 2`:

* `sa16q_conv_fderiv_schwartz`: differentiable, `∂_e (G ψ) = G (∂_e ψ)`;
* `sa16q_conv_contDiff`: `G ψ` is `C^∞`;
* `sa16q_conv_pd`: `∂^idx (G ψ) = G (∂^idx ψ)`;
* `sa16q_pd_comm`: `∂^idx ∂_e f = ∂_e ∂^idx f` for smooth `f`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Sm1
variable {d : ℕ}

lemma sa16q_Dec_mono {F : Type*} [NormedAddCommGroup F] {C C' : ℝ} {f : Euc d → F}
    (h : sa16q_Dec C f) (hC : C ≤ C') : sa16q_Dec C' f := by
  intro z
  refine (h z).trans ?_
  gcongr

lemma sa16q_dec_schwartz {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ : 𝓢(Euc d, F)) :
    ∃ C : ℝ, 0 ≤ C ∧ sa16q_Dec C ψ := by
  obtain ⟨C, hC0, hC⟩ := HRS.S16Cze.s16cze_weighted ψ (d + 2)
  refine ⟨C, hC0, fun z => ?_⟩
  have := hC 0 (-z)
  simpa using this

lemma sa16q_g_WI (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) :
    sa16q_WI (rieszKernel d s) := by
  have h := sa16q_m0_WI hd hs hs2
  unfold sa16q_WI at h ⊢
  refine h.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((sa16q_g_meas d s).norm.mul ((measurable_const.add measurable_norm).pow_const _)).aestronglyMeasurable
  · have hw : 0 ≤ (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hm : ‖rieszKernel d s y‖ ≤ ‖sa16q_m0 d s y‖ := by
      unfold sa16q_m0
      rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (by positivity))]
      linarith [norm_nonneg y]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    exact mul_le_mul_of_nonneg_right hm hw

lemma sa16q_conv_eq (d : ℕ) (s : ℝ) (φ : Euc d → ℝ) :
    HRS.Whole.convFun (rieszKernel d s) φ = fun x => ∫ y, rieszKernel d s y * φ (x - y) :=
  funext (HRS.S16Cze.s16cze_conv_swap _ _)

/-- the decay hypotheses for a Schwartz function and its derivative -/
lemma sa16q_schwartz_hyp (ψ : 𝓢(Euc d, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ Differentiable ℝ ψ ∧ Continuous (fderiv ℝ ψ) ∧ sa16q_Dec C ψ ∧
      sa16q_Dec C (fderiv ℝ ψ) := by
  obtain ⟨C1, h1, hD1⟩ := sa16q_dec_schwartz ψ
  obtain ⟨C2, h2, hD2⟩ := sa16q_dec_schwartz (SchwartzMap.fderivCLM ℝ (Euc d) ℝ ψ)
  have hfd : ∀ z, SchwartzMap.fderivCLM ℝ (Euc d) ℝ ψ z = fderiv ℝ ψ z :=
    fun z => SchwartzMap.fderivCLM_apply ℝ ψ z
  have hD2' : sa16q_Dec C2 (fderiv ℝ ψ) := fun z => by rw [← hfd]; exact hD2 z
  refine ⟨max C1 C2, le_max_of_le_left h1, fun z => ψ.differentiableAt, ?_,
    sa16q_Dec_mono hD1 (le_max_left _ _), sa16q_Dec_mono hD2' (le_max_right _ _)⟩
  have : fderiv ℝ ψ = ⇑(SchwartzMap.fderivCLM ℝ (Euc d) ℝ ψ) := funext fun z => (hfd z).symm
  rw [this]
  exact (SchwartzMap.fderivCLM ℝ (Euc d) ℝ ψ).continuous

section Gen
variable {m : Euc d → ℝ} (hm : Measurable m) (hWI : sa16q_WI m)
include hm hWI

/-- generic kernel: differentiation of `x ↦ ∫ m y ψ (x - y) dy` for Schwartz `ψ` -/
theorem sa16q_gen_fderiv (ψ : 𝓢(Euc d, ℝ)) (x e : Euc d) :
    DifferentiableAt ℝ (fun x => ∫ y, m y * ψ (x - y)) x ∧
    fderiv ℝ (fun x => ∫ y, m y * ψ (x - y)) x e = ∫ y, m y * fderiv ℝ ψ (x - y) e := by
  obtain ⟨C, hC, hd1, hc, hD, hD'⟩ := sa16q_schwartz_hyp ψ
  exact ⟨(sa16q_hasFDerivAt_conv hm hWI hC hd1 hc hD hD' x).differentiableAt,
    sa16q_fderiv_conv_apply hm hWI hC hd1 hc hD hD' x e⟩

open LineDeriv in
theorem sa16q_gen_contDiff : ∀ (n : ℕ) (ψ : 𝓢(Euc d, ℝ)),
    ContDiff ℝ n (fun x => ∫ y, m y * ψ (x - y)) := by
  intro n
  induction n with
  | zero =>
    intro ψ
    show ContDiff ℝ (0 : WithTop ℕ∞) _
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (sa16q_gen_fderiv hm hWI ψ x 0).1.continuousAt)
  | succ n ih =>
    intro ψ
    rw [Nat.cast_succ]
    refine (contDiff_succ_iff_fderiv_apply).2 ⟨fun x => (sa16q_gen_fderiv hm hWI ψ x 0).1,
      fun h => absurd h (by simp), fun y => ?_⟩
    have h : (fun x => fderiv ℝ (fun x => ∫ y', m y' * ψ (x - y')) x y) =
        fun x => ∫ y', m y' * (∂_{y} ψ) (x - y') := by
      funext x
      rw [(sa16q_gen_fderiv hm hWI ψ x y).2]
      congr 1
    rw [h]
    exact ih _

theorem sa16q_gen_contDiff_top (ψ : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ ∞ (fun x => ∫ y, m y * ψ (x - y)) :=
  contDiff_infty.2 fun n => sa16q_gen_contDiff hm hWI n ψ

open LineDeriv in
theorem sa16q_gen_pd : ∀ (j : ℕ) (idx : Fin j → Fin d) (ψ : 𝓢(Euc d, ℝ)),
    partialDeriv idx (fun x => ∫ y, m y * ψ (x - y)) =
      fun x => ∫ y, m y * partialDeriv idx (⇑ψ) (x - y) := by
  intro j
  induction j with
  | zero =>
    intro idx ψ
    have h1 : partialDeriv idx ⇑ψ = ⇑ψ := funext (sa16j_pd_zero idx _)
    rw [h1]
    exact funext (sa16j_pd_zero idx _)
  | succ j ih =>
    intro idx ψ
    funext x
    set tl : Fin j → Fin d := fun l => idx l.succ with htl
    have hcd := sa16q_gen_contDiff_top hm hWI ψ
    have h1 := sa16y_pd_succN (N := j + 1) (hcd.of_le (by exact_mod_cast le_top)) (le_refl _) idx x
    rw [h1, ih tl ψ]
    have hψ' : partialDeriv tl ⇑ψ = ⇑(∂^{fun l => (EuclideanSpace.single (tl l) (1 : ℝ) : Euc d)} ψ) :=
      sa16j_pd_schwartz ψ tl
    rw [hψ', (sa16q_gen_fderiv hm hWI _ x _).2]
    congr 1
    funext y
    congr 1
    rw [← hψ']
    exact (sa16y_pd_succN (N := j + 1) (ψ.smooth' |>.of_le (by exact_mod_cast le_top)) (le_refl _) idx
      (x - y)).symm

end Gen

section Conv
variable (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

theorem sa16q_conv_fderiv_schwartz (ψ : 𝓢(Euc d, ℝ)) (x e : Euc d) :
    DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) x ∧
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) x e =
      HRS.Whole.convFun (rieszKernel d s) (fun z => fderiv ℝ ψ z e) x := by
  have h := sa16q_gen_fderiv (sa16q_g_meas d s) (sa16q_g_WI hd hs hs2) ψ x e
  rw [sa16q_conv_eq d s ψ, sa16q_conv_eq d s (fun z => fderiv ℝ ψ z e)]
  exact h

theorem sa16q_conv_contDiff (n : ℕ) (ψ : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ n (HRS.Whole.convFun (rieszKernel d s) ψ) := by
  rw [sa16q_conv_eq d s ψ]
  exact sa16q_gen_contDiff (sa16q_g_meas d s) (sa16q_g_WI hd hs hs2) n ψ

theorem sa16q_conv_contDiff_top (ψ : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) := by
  rw [sa16q_conv_eq d s ψ]
  exact sa16q_gen_contDiff_top (sa16q_g_meas d s) (sa16q_g_WI hd hs hs2) ψ

theorem sa16q_conv_pd (j : ℕ) (idx : Fin j → Fin d) (ψ : 𝓢(Euc d, ℝ)) :
    partialDeriv idx (HRS.Whole.convFun (rieszKernel d s) ψ) =
      HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx ⇑ψ) := by
  rw [sa16q_conv_eq d s ψ, sa16q_conv_eq d s (partialDeriv idx ⇑ψ)]
  exact sa16q_gen_pd (sa16q_g_meas d s) (sa16q_g_WI hd hs hs2) j idx ψ

end Conv

/-- partial derivatives commute with the derivative in a coordinate direction -/
lemma sa16q_pd_comm {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ∀ (j : ℕ) (idx : Fin j → Fin d) (x : Euc d),
      partialDeriv idx (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x =
        fderiv ℝ (partialDeriv idx f) x (EuclideanSpace.single i 1) := by
  intro j
  induction j with
  | zero =>
    intro idx x
    rw [sa16j_pd_zero idx (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x,
      show partialDeriv idx f = f from funext (sa16j_pd_zero idx f)]
  | succ j ih =>
    intro idx x
    obtain ⟨k, r, rfl⟩ : ∃ (k : Fin d) (r : Fin j → Fin d), idx = Fin.cons k r :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hh : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hw : ContDiff ℝ ∞ (partialDeriv r f) := sa16j_pd_smooth hf r
    rw [sa16s_pd_cons hh k r x]
    have e1 : partialDeriv r (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) =
        fun y => fderiv ℝ (partialDeriv r f) y (EuclideanSpace.single i 1) :=
      funext fun y => ih r y
    have e2 : partialDeriv (Fin.cons k r : Fin (j + 1) → Fin d) f =
        fun y => fderiv ℝ (partialDeriv r f) y (EuclideanSpace.single k 1) :=
      funext fun y => sa16s_pd_cons hf k r y
    rw [e1, e2]
    -- symmetry of the second derivative of `w = ∂^r f`
    set w := partialDeriv r f with hwdef
    have hdw : Differentiable ℝ (fderiv ℝ w) := by
      have := (hw.fderiv_right (m := ∞) (by simp))
      exact this.differentiable (by simp)
    have hsym : IsSymmSndFDerivAt ℝ w x := (hw.contDiffAt).isSymmSndFDerivAt (by simp)
    have hA : ∀ u v : Euc d, fderiv ℝ (fun y => fderiv ℝ w y u) x v = fderiv ℝ (fderiv ℝ w) x v u := by
      intro u v
      have := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ w) (u := fun _ : Euc d => u) (x := x)
        (hdw x) (differentiableAt_const u)
      rw [this]
      simp
    rw [hA, hA]
    exact (hsym.eq _ _).symm

end Sm1

end HRS.Whole.AppendixA.Phase2SA16Q
