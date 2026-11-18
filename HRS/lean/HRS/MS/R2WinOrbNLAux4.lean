import HRS.MS.R2WinOrbNLAux3
import HRS.MS.S67NlBD26

/-!
# S10.3 (nonlinear branch), part 4: the generator difference at a fixed time for an arbitrary `C²_b` function

Prefix `s103n_`, namespace `HRS.MS.R2WinOrbNL`.  For a trajectory `ρ` of the S6.3 small class and `t ≥ 0`, write `v = movV ρ_β ρ t`
(so `ρ_t = ρ_β + √ρ_β v`).  `s103n_force_add`: `∇g*ρ_t = ∇g*ρ_β + F[v]`.  `s103n_gen_diff`: for `u ∈ C¹`,
`L_t u - L_β u = (J(ρ_t) - J(ρ_β)) u - F[v]·∇u` (pointwise).  `s103n_gen_diff_K`: for `u ∈ C²_b`,
`√ρ_β (L_t u - L_β u) = K(v, ψ_u)` with `ψ_u = s67psi ρ_β u` (the identity of S6.7nl.26 for an arbitrary function instead of
`f_r`; the proof of `s67bd_generator_difference` is used with the bounded jets of `u`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.BreakdownS67 HRS.MS.Mov63 HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.MovOsc
open HRS.MS.MovForce HRS.MS.MovC2

variable {d : ℕ}

theorem s103n_density_split {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {m : ℕ}
    {R0 c0 : ℝ} {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s a β ρβ m R0 c0 f0 ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    ρ t x = ρβ x + Real.sqrt (ρβ x) * movV ρβ ρ t x := by
  obtain ⟨-, hρpos⟩ := mov2d_rho_data H
  have : Real.sqrt (ρβ x) ≠ 0 := (Real.sqrt_pos.2 (hρpos x)).ne'
  simp only [movV]
  field_simp
  ring

theorem s103n_force_add {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {m : ℕ}
    (hm : (d : ℝ) / 2 + 7 < m) {R0 c0 : ℝ} {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s a β ρβ m R0 c0 f0 ρ) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    movForce d s (ρ t) x = movForce d s ρβ x + s67bd_F d s ρβ (movV ρβ ρ t) x := by
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρβ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hsq2 : MemLp (fun x => Real.sqrt (ρβ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hρ0I : Integrable ρβ volume := by
    by_contra hni
    have h1 := H.hρ.2.1.integral_one
    rw [integral_undef hni] at h1
    exact zero_ne_one h1
  set v : Euc d → ℝ := movV ρβ ρ t with hvdef
  have hvcont : Continuous v := by
    show Continuous (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x))
    refine ((hρ.regular t ht).sub hρsm.continuous).div hsqsm.continuous
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  obtain ⟨hvm, -⟩ := hρ.weighted t ht
  have hvC2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) v :=
    (mn_force_bound H.hd H.hs0 H.hsd β a H.hβ H.hq ρβ H.hρ 0 m (by linarith)).choose_spec.2 v
      hvcont hvm |>.1
  have hvC1 : ContDiff ℝ 1 v := hvC2.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 (fun x => Real.sqrt (ρβ x) * v x) := (hsqsm.of_le (by simp)).mul hvC1
  have hgI : Integrable (fun x => Real.sqrt (ρβ x) * v x) volume := hsq2.integrable_mul hvm.1
  have := s67bd26_force_add H.hd H.hs0 H.hsd (hρsm.of_le (by simp)) hg1 hρ0I hgI x
  unfold s67bd_F
  rw [← this]
  congr 1
  funext y
  exact s103n_density_split H hρ ht y

theorem s103n_gen_diff {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {m : ℕ}
    (hm : (d : ℝ) / 2 + 7 < m) {R0 c0 : ℝ} {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s a β ρβ m R0 c0 f0 ρ) {t : ℝ} (ht : 0 ≤ t) (u : Euc d → ℝ) (x : Euc d) :
    generatorW ((quadraticGradientDyn d s a β).coeff ρ) t u x -
        generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t u x =
      (s67J d s (ρ t) u x - s67J d s ρβ u x) -
        inner ℝ (s67bd_F d s ρβ (movV ρβ ρ t) x) (gradient u x) := by
  have e1 : generatorW ((quadraticGradientDyn d s a β).coeff ρ) t u x =
      generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ t)) t u x := by
    rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]
  rw [e1, s67_gen_eq s a β (ρ t) t u x, s67_gen_eq s a β ρβ t u x, s103n_force_add H hm hρ ht x]
  simp only [inner_sub_left, inner_add_left, inner_neg_left]
  ring

set_option maxHeartbeats 1600000 in
theorem s103n_gen_diff_K {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {m : ℕ}
    (hm : (d : ℝ) / 2 + 7 < m) {R0 c0 : ℝ} {f0 : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s a β ρβ m R0 c0 f0 ρ) {t : ℝ} (ht : 0 ≤ t) (u : Euc d → ℝ)
    (hu : MemCb 2 u) (x : Euc d) :
    Real.sqrt (ρβ x) * (generatorW ((quadraticGradientDyn d s a β).coeff ρ) t u x -
        generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) t u x) =
      s67bd_K d s ρβ (movV ρβ ρ t) (s67psi ρβ u) x := by
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρβ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hsq2 : MemLp (fun x => Real.sqrt (ρβ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hρ0I : Integrable ρβ volume := by
    by_contra hni
    have h1 := H.hρ.2.1.integral_one
    rw [integral_undef hni] at h1
    exact zero_ne_one h1
  have hu2 : ContDiff ℝ 2 u := hu.1
  have hu1 : ContDiff ℝ 1 u := hu2.of_le (by norm_num)
  obtain ⟨B1, hB1⟩ := hu.2 1 (by norm_num)
  have hDu1 : ∀ i : Fin d, ContDiff ℝ 1 (s67bd_D i u) := fun i => by
    unfold s67bd_D
    exact (hu2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDub : ∀ (i : Fin d) y, |s67bd_D i u y| ≤ B1 := by
    intro i y
    have h1 := (fderiv ℝ u y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    have h2 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [h2, mul_one, ← norm_iteratedFDeriv_one] at h1
    unfold s67bd_D
    rw [← Real.norm_eq_abs]
    exact h1.trans (hB1 ⟨y, rfl⟩)
  set v : Euc d → ℝ := movV ρβ ρ t with hvdef
  have hvcont : Continuous v := by
    show Continuous (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x))
    refine ((hρ.regular t ht).sub hρsm.continuous).div hsqsm.continuous
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  obtain ⟨hvm, -⟩ := hρ.weighted t ht
  have hvC2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) v :=
    (mn_force_bound H.hd H.hs0 H.hsd β a H.hβ H.hq ρβ H.hρ 0 m (by linarith)).choose_spec.2 v
      hvcont hvm |>.1
  have hvC1 : ContDiff ℝ 1 v := hvC2.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 (fun x => Real.sqrt (ρβ x) * v x) := (hsqsm.of_le (by simp)).mul hvC1
  have hgI : Integrable (fun x => Real.sqrt (ρβ x) * v x) volume := hsq2.integrable_mul hvm.1
  set c : ℝ := ∫ y, u y * ρβ y with hc
  have hψfun : s67psi ρβ u = fun y => Real.sqrt (ρβ y) * (u y - c) := rfl
  have hW : ∀ (i : Fin d) x, s67bd_W ρβ i (s67psi ρβ u) x = Real.sqrt (ρβ x) * s67bd_D i u x := by
    intro i x
    rw [hψfun]
    exact s67bd26_W_eq hρsm hρpos hu1 c i x
  have hgrad : ∀ (i : Fin d) x, gradient u x i = s67bd_D i u x := fun i x => mov2d_grad_coord u x i
  have hρ0c1 : ContDiff ℝ 1 ρβ := hρsm.of_le (by simp)
  have hF2 : ∀ (j : Fin d) x, movForce d s (fun y => ρβ y * s67bd_D j u y) x +
      movForce d s (fun y => v y * s67bd_W ρβ j (s67psi ρβ u) y) x =
      movForce d s (fun y => ρ t y * gradient u y j) x := by
    intro j x
    have hc1 : ContDiff ℝ 1 (fun y => ρβ y * s67bd_D j u y) := hρ0c1.mul (hDu1 j)
    have hWfun : (fun y => v y * s67bd_W ρβ j (s67psi ρβ u) y) =
        fun y => (Real.sqrt (ρβ y) * v y) * s67bd_D j u y := by
      funext y; rw [hW]; ring
    have hc2 : ContDiff ℝ 1 (fun y => v y * s67bd_W ρβ j (s67psi ρβ u) y) := by
      rw [hWfun]; exact hg1.mul (hDu1 j)
    have hI1 : Integrable (fun y => ρβ y * s67bd_D j u y) volume :=
      hρ0I.mul_bdd (hDu1 j).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hDub j y)
    have hI2 : Integrable (fun y => v y * s67bd_W ρβ j (s67psi ρβ u) y) volume := by
      rw [hWfun]
      exact hgI.mul_bdd (hDu1 j).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hDub j y)
    have := s67bd26_force_add hd hs0 hsd hc1 hc2 hI1 hI2 x
    rw [← this]
    congr 1
    funext y
    rw [s103n_density_split H hρ ht y, hgrad, hW]; ring
  have e1 : generatorW ((quadraticGradientDyn d s a β).coeff ρ) t u x =
      generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ t)) t u x := by
    rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]
  rw [e1, s67_gen_eq s a β (ρ t) t u x, s67_gen_eq s a β ρβ t u x]
  have hJ : ∀ (ρ' : Euc d → ℝ), s67J d s ρ' u x =
      ∑ j : Fin d, movForce d s (fun y => ρ' y * gradient u y j) x j := fun ρ' => rfl
  rw [hJ, hJ]
  have hJd : ∑ j : Fin d, movForce d s (fun y => ρ t y * gradient u y j) x j -
      ∑ j : Fin d, movForce d s (fun y => ρβ y * gradient u y j) x j =
      ∑ j : Fin d, movForce d s (fun y => v y * s67bd_W ρβ j (s67psi ρβ u) y) x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := hF2 j x
    have h3 : (fun y => ρβ y * gradient u y j) = fun y => ρβ y * s67bd_D j u y := by
      funext y; rw [hgrad]
    rw [h3, ← h2]
    simp
  have hFd : movForce d s (ρ t) x = movForce d s ρβ x +
      movForce d s (fun y => Real.sqrt (ρβ y) * v y) x := s103n_force_add H hm hρ ht x
  unfold s67bd_K s67bd_F
  have hin1 : inner ℝ (-(a • x) - movForce d s (ρ t) x) (gradient u x) -
      inner ℝ (-(a • x) - movForce d s ρβ x) (gradient u x) =
      -∑ i : Fin d, movForce d s (fun y => Real.sqrt (ρβ y) * v y) x i * s67bd_D i u x := by
    rw [← inner_sub_left, hFd, s67bd26_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgrad]
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.neg_apply]
    ring
  have hlin : ∀ a I1 J1 I0 J0 : ℝ, (a + I1 + J1) - (a + I0 + J0) = (I1 - I0) + (J1 - J0) := by
    intros; ring
  rw [hlin, hin1, hJd]
  simp only [hW]
  have hsum : ∑ i : Fin d, movForce d s (fun y => Real.sqrt (ρβ y) * v y) x i *
      (Real.sqrt (ρβ x) * s67bd_D i u x) =
      Real.sqrt (ρβ x) * ∑ i : Fin d, movForce d s (fun y => Real.sqrt (ρβ y) * v y) x i *
        s67bd_D i u x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

end HRS.MS.R2WinOrbNL

end
