import HRS.MS.S104bNL5
import HRS.MS.S104bOrb1
import HRS.MS.R2GenInitNL4
import HRS.MS.WsPrepAux12

/-!
# S10.5 (nonlinear), packet S104b-NL6: the Duhamel identity for the gradient of the adjoint orbit from `S104nOrbit`

`s104b_duhamel`: for a classical adjoint orbit with the terminal-time regularity `S104nOrbit` the Duhamel identity of `OscAdjointInput.duhamel` holds:
`∂_aU(r,t)φ(x) - ∂_aφ(x) = ∫_r^t ∂_aU(r,s)L_sφ(x) ds` with integrable right side.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S53 HRS.MS.R2WinErr

variable {d : ℕ}

lemma s104b_abs_gradComp_le {f : Euc d → ℝ} (a : Fin d) (x : Euc d) :
    |gradComp a f x| ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [norm_iteratedFDeriv_one]
  have h1 : |gradient f x a| ≤ ‖gradient f x‖ := by
    have := PiLp.norm_apply_le (gradient f x) a
    simpa [Real.norm_eq_abs] using this
  have h2 : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := s53_norm_gradient f x
  exact h1.trans h2.le

lemma s104b_gradComp_lin {f g h : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (c : ℝ) (a : Fin d) (x : Euc d) :
    gradComp a (fun z => c * (f z - g z) - h z) x =
      c * (gradComp a f x - gradComp a g x) - gradComp a h x := by
  unfold gradComp
  simp only [q09_gradient_apply]
  have hdf := hf.differentiable one_ne_zero x
  have hdg := hg.differentiable one_ne_zero x
  have hdh := hh.differentiable one_ne_zero x
  have hA : DifferentiableAt ℝ (fun y => c * (f y - g y)) x := (hdf.sub hdg).const_mul c
  have hB : DifferentiableAt ℝ (fun y => f y - g y) x := hdf.sub hdg
  rw [fderiv_fun_sub hA hdh, fderiv_const_mul hB c, fderiv_fun_sub hdf hdg]
  simp


lemma s104b_grad_hasDeriv {T : ℝ} {G G' : ℝ → Euc d → ℝ} (hG : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G τ))
    (hG' : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G' τ)) (hdiff : S53Diff T G G') (a : Fin d) (x : Euc d) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun τ => gradComp a (G τ) x) (gradComp a (G' y) x) (Icc 0 T) y := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hdiff y hy (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun τ hτ hd => ?_⟩
  have hτT : τ ∈ Icc (0 : ℝ) T := hτ.1
  have hne : τ ≠ y := hτ.2
  set h := τ - y with hhdef
  have h0 : h ≠ 0 := sub_ne_zero.2 hne
  have hyh : y + h = τ := by rw [hhdef]; ring
  have hq := hh h h0 (by rw [Real.dist_eq] at hd; exact hd) (by rw [hyh]; exact hτT) 1 (by norm_num) x
  rw [hyh] at hq
  have hlin := s104b_gradComp_lin ((hG τ hτT).1.of_le (by norm_num)) ((hG y hy).1.of_le (by norm_num))
    ((hG' y hy).1.of_le (by norm_num)) h⁻¹ a x
  rw [Real.dist_eq]
  have e : slope (fun τ => gradComp a (G τ) x) y τ - gradComp a (G' y) x =
      gradComp a (fun z => h⁻¹ * (G τ z - G y z) - G' y z) x := by
    rw [hlin, slope_def_field]
    simp only [hhdef]
    ring
  rw [e]
  exact lt_of_le_of_lt ((s104b_abs_gradComp_le a x).trans hq) (by linarith)

lemma s104b_grad_contOn {T : ℝ} {G' : ℝ → Euc d → ℝ} (hG' : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G' τ))
    (hc : S53Cont T G') (a : Fin d) (x : Euc d) : ContinuousOn (fun τ => gradComp a (G' τ) x) (Icc 0 T) := by
  intro y hy
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := hc y hy (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun τ hτ hd => ?_⟩
  have hq := hh τ hτ (by rw [Real.dist_eq] at hd; exact hd) 1 (by norm_num) x
  have e : gradComp a (G' τ) x - gradComp a (G' y) x = gradComp a (fun z => G' τ z - G' y z) x := by
    unfold gradComp
    rw [HRS.MS.Fcau.fcau_gradient_sub ((hG' τ hτ).1.of_le (by norm_num)) ((hG' y hy).1.of_le (by norm_num))]
    rfl
  rw [Real.dist_eq, e]
  exact lt_of_le_of_lt ((s104b_abs_gradComp_le a x).trans hq) (by linarith)

theorem s104b_duhamel {C : WholeCoeff d} {φ : Euc d → ℝ} {T0 : ℝ} (horb : S104nOrbit C φ T0) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T0) (a : Fin d) (x : Euc d) :
    IntegrableOn (fun s => gradComp a (propagatorW C r s (generatorW C s φ)) x) (Icc r t) ∧
      gradComp a (propagatorW C r t φ) x - gradComp a φ x =
        ∫ s in Icc r t, gradComp a (propagatorW C r s (generatorW C s φ)) x := by
  have hr' : r ∈ Icc (0 : ℝ) T0 := ⟨hr, hrt.trans htT⟩
  obtain ⟨G2, hG2, hd12⟩ := horb.diff12 r hr'
  have hG : ∀ τ ∈ Icc (0 : ℝ) (T0 - r), MemCb 2 (propagatorW C r (r + τ) φ) := fun τ hτ => horb.cb0 hr' hτ
  have hG' : ∀ τ ∈ Icc (0 : ℝ) (T0 - r), MemCb 2 (propagatorW C r (r + τ) (generatorW C (r + τ) φ)) :=
    fun τ hτ => horb.cb1 hr' hτ
  have hdiff := horb.diff01 r hr'
  have hc' : S53Cont (T0 - r) (fun τ => propagatorW C r (r + τ) (generatorW C (r + τ) φ)) :=
    s53_cont_of_diff hG' hG2 hd12
  have hder : ∀ y ∈ Icc (0 : ℝ) (T0 - r), HasDerivWithinAt (fun τ => gradComp a (propagatorW C r (r + τ) φ) x)
      (gradComp a (propagatorW C r (r + y) (generatorW C (r + y) φ)) x) (Icc 0 (T0 - r)) y :=
    fun y hy => s104b_grad_hasDeriv hG hG' hdiff a x hy
  have hcG' := s104b_grad_contOn hG' hc' a x
  have hτ0 : t - r ∈ Icc (0 : ℝ) (T0 - r) := ⟨by linarith, by linarith⟩
  have hsub : Icc (0 : ℝ) (t - r) ⊆ Icc 0 (T0 - r) := Icc_subset_Icc_right hτ0.2
  have hcont : ContinuousOn (fun τ => gradComp a (propagatorW C r (r + τ) φ) x) (Icc 0 (t - r)) :=
    (show ContinuousOn (fun τ => gradComp a (propagatorW C r (r + τ) φ) x) (Icc 0 (T0 - r)) from
      fun y hy => (hder y hy).continuousWithinAt).mono hsub
  have hint : IntervalIntegrable (fun σ => gradComp a (propagatorW C r (r + σ) (generatorW C (r + σ) φ)) x)
      volume 0 (t - r) := (hcG'.mono hsub).intervalIntegrable_of_Icc (by linarith)
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by linarith : (0 : ℝ) ≤ t - r) hcont
    (fun y hy => by
      have hyT : y ∈ Ioo (0 : ℝ) (T0 - r) := ⟨hy.1, lt_of_lt_of_le hy.2 hτ0.2⟩
      exact ((hder y ⟨hy.1.le, hyT.2.le⟩).hasDerivAt (Icc_mem_nhds hyT.1 hyT.2)).hasDerivWithinAt) hint
  have hterm : propagatorW C r r φ = φ := (s104n_prop_cl (horb.ex0 r hr')).terminal
  have e1 : ∫ s in Icc r t, gradComp a (propagatorW C r s (generatorW C s φ)) x =
      ∫ σ in (0 : ℝ)..(t - r), gradComp a (propagatorW C r (r + σ) (generatorW C (r + σ) φ)) x := by
    rw [intervalIntegral.integral_comp_add_left (fun s => gradComp a (propagatorW C r s (generatorW C s φ)) x) r]
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    simp only [add_zero, add_sub_cancel]
  refine ⟨?_, ?_⟩
  · have hc2 : ContinuousOn (fun s => gradComp a (propagatorW C r (r + (s - r)) (generatorW C (r + (s - r)) φ)) x)
        (Icc r t) :=
      (hcG'.mono hsub).comp (continuousOn_id.sub continuousOn_const)
        (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hfe : (fun s => gradComp a (propagatorW C r (r + (s - r)) (generatorW C (r + (s - r)) φ)) x) =
        fun s => gradComp a (propagatorW C r s (generatorW C s φ)) x := by
      funext s; simp only [add_sub_cancel]
    rw [hfe] at hc2
    exact hc2.integrableOn_Icc
  · rw [e1, key]
    have e2 : r + (t - r) = t := by ring
    simp only [e2, add_zero, hterm]

end HRS.MS.S104b
