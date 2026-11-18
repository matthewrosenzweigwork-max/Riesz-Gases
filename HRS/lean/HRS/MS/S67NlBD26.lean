import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.MovAdjNlAux1
import HRS.MS.S67NlBD14
import HRS.MS.S67NlBD24

/-!
# S6.7 nonlinear breakdown, packet 26: generator difference

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4766-4780 area, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: both generators have the form `ν Δ u + ⟨-q x - F[ρ], ∇u⟩ + J[ρ] u` (`s67_gen_eq`, the
coefficient at time `r` only sees `ρ r`); `ρ r = ρ₀ + √ρ₀ v`; the cancellation force is additive
on `C¹ ∩ L¹` (integrability from 14); `W_i ψ = √ρ₀ ∂_i u` for `ψ = s67psi ρ₀ u`; the two integrability
claims follow from the linear growth of the generators (given for the moving one, `s67a_L0_growth`
for the stationary one) and `s67a_int_lin`.
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

/-- additivity of the cancellation force on `C¹ ∩ L¹` -/
lemma s67bd26_force_add (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h1 h2 : Euc d → ℝ}
    (hc1 : ContDiff ℝ 1 h1) (hc2 : ContDiff ℝ 1 h2) (hI1 : Integrable h1 volume)
    (hI2 : Integrable h2 volume) (x : Euc d) :
    movForce d s (fun y => h1 y + h2 y) x = movForce d s h1 x + movForce d s h2 x := by
  have i1 := (s67bd_force_split hd hs0 hsd h1 hc1 hI1 x).1
  have i2 := (s67bd_force_split hd hs0 hsd h2 hc2 hI2 x).1
  unfold movForce convGradConvW
  rw [← integral_add i1 i2]
  congr 1
  funext y
  by_cases hy : ‖x - y‖ ≤ 1 / 4
  · simp only [hy, if_true]
    rw [← add_smul]; congr 1; ring
  · simp only [hy, if_false]
    rw [← add_smul]

/-- `W_i ψ = √ρ₀ ∂_i u` for `ψ = √ρ₀ (u - c)` -/
lemma s67bd26_W_eq (hρsm : ContDiff ℝ ∞ ρ₀) (hpos : ∀ x, 0 < ρ₀ x) {u : Euc d → ℝ}
    (hu : ContDiff ℝ 1 u) (c : ℝ) (i : Fin d) (x : Euc d) :
    s67bd_W ρ₀ i (fun y => Real.sqrt (ρ₀ y) * (u y - c)) x = Real.sqrt (ρ₀ x) * s67bd_D i u x := by
  have hρd : HasFDerivAt ρ₀ (fderiv ℝ ρ₀ x) x :=
    ((hρsm.differentiable (by simp)) x).hasFDerivAt
  have hud : HasFDerivAt u (fderiv ℝ u x) x := ((hu.differentiable one_ne_zero) x).hasFDerivAt
  have hsq := hρd.sqrt (hpos x).ne'
  have hlog := hρd.log (hpos x).ne'
  have hprod := hsq.mul (hud.sub_const c)
  have hprod' : fderiv ℝ (fun y => Real.sqrt (ρ₀ y) * (u y - c)) x =
      Real.sqrt (ρ₀ x) • fderiv ℝ u x + (u x - c) • ((1 / (2 * Real.sqrt (ρ₀ x))) • fderiv ℝ ρ₀ x) :=
    hprod.fderiv
  unfold s67bd_W s67bd_D
  rw [hprod', hlog.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hs : Real.sqrt (ρ₀ x) ^ 2 = ρ₀ x := Real.sq_sqrt (hpos x).le
  have hs0 : 0 < Real.sqrt (ρ₀ x) := Real.sqrt_pos.2 (hpos x)
  set sx := Real.sqrt (ρ₀ x) with hsx
  have hρx : ρ₀ x = sx ^ 2 := hs.symm
  rw [hρx]
  field_simp
  ring

lemma s67bd26_inner (a b : Euc d) : inner ℝ a b = ∑ i, a i * b i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

set_option maxHeartbeats 1000000 in
theorem s67bd_generator_difference (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ∀ r ∈ Icc (0 : ℝ) T,
      Integrable (fun y =>
        generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y * ρ₀ y) volume ∧
      Integrable (fun y =>
        generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) r (f r) y * ρ₀ y) volume ∧
      ∀ x : Euc d, Real.sqrt (ρ₀ x) *
        (generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) x -
         generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) r (f r) x) =
        s67bd_K d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x := by
  intro r hr
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hsq2 : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hρ0I : Integrable ρ₀ volume := by
    by_contra hni
    have h1 := H.hρ.2.1.integral_one
    rw [integral_undef hni] at h1
    exact zero_ne_one h1
  -- the data of `f r`
  have hu2 : ContDiff ℝ 2 (f r) := hf.c2 r hr
  have hu1 : ContDiff ℝ 1 (f r) := hu2.of_le (by norm_num)
  have hmemcb : MemCb 2 (f r) := by
    refine ⟨hu2, fun j hj => ?_⟩
    obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  have hDu1 : ∀ i : Fin d, ContDiff ℝ 1 (s67bd_D i (f r)) := fun i => by
    unfold s67bd_D
    exact (hu2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDub : ∀ (i : Fin d) y, |s67bd_D i (f r) y| ≤ B1 := by
    intro i y
    have h1 := (fderiv ℝ (f r) y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    have h2 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [h2, mul_one, ← norm_iteratedFDeriv_one] at h1
    unfold s67bd_D
    rw [← Real.norm_eq_abs]
    exact h1.trans (hB1 r hr y)
  -- the moving density
  set v : Euc d → ℝ := movV ρ₀ ρ r with hvdef
  have hρr : ∀ x, ρ r x = ρ₀ x + Real.sqrt (ρ₀ x) * v x := by
    intro x
    have : Real.sqrt (ρ₀ x) ≠ 0 := (Real.sqrt_pos.2 (hρpos x)).ne'
    simp only [hvdef, movV]
    field_simp
    ring
  have hvcont : Continuous v := by
    show Continuous (fun x => (ρ r x - ρ₀ x) / Real.sqrt (ρ₀ x))
    refine ((hρ.regular r hr.1).sub hρsm.continuous).div hsqsm.continuous
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  obtain ⟨hvm, -⟩ := hρ.weighted r hr.1
  have hvC2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) v :=
    (mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ 0 m (by linarith)).choose_spec.2 v
      hvcont hvm |>.1
  have hvC1 : ContDiff ℝ 1 v := hvC2.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * v x) := (hsqsm.of_le (by simp)).mul hvC1
  have hgI : Integrable (fun x => Real.sqrt (ρ₀ x) * v x) volume := hsq2.integrable_mul hvm.1
  -- the weights
  set c : ℝ := ∫ y, f r y * ρ₀ y with hc
  have hψfun : s67psi ρ₀ (f r) = fun y => Real.sqrt (ρ₀ y) * (f r y - c) := rfl
  have hW : ∀ (i : Fin d) x, s67bd_W ρ₀ i (s67psi ρ₀ (f r)) x =
      Real.sqrt (ρ₀ x) * s67bd_D i (f r) x := by
    intro i x
    rw [hψfun]
    exact s67bd26_W_eq hρsm hρpos hu1 c i x
  have hgrad : ∀ (i : Fin d) x, gradient (f r) x i = s67bd_D i (f r) x := fun i x =>
    mov2d_grad_coord (f r) x i
  -- additivity pieces
  have hρ0c1 : ContDiff ℝ 1 ρ₀ := hρsm.of_le (by simp)
  have hF1 : ∀ x, movForce d s ρ₀ x + movForce d s (fun y => Real.sqrt (ρ₀ y) * v y) x =
      movForce d s (ρ r) x := by
    intro x
    have := s67bd26_force_add hd hs0 hsd hρ0c1 hg1 hρ0I hgI x
    rw [← this]
    congr 1
    funext y
    exact (hρr y).symm
  have hF2 : ∀ (j : Fin d) x, movForce d s (fun y => ρ₀ y * s67bd_D j (f r) y) x +
      movForce d s (fun y => v y * s67bd_W ρ₀ j (s67psi ρ₀ (f r)) y) x =
      movForce d s (fun y => ρ r y * gradient (f r) y j) x := by
    intro j x
    have hc1 : ContDiff ℝ 1 (fun y => ρ₀ y * s67bd_D j (f r) y) := hρ0c1.mul (hDu1 j)
    have hWfun : (fun y => v y * s67bd_W ρ₀ j (s67psi ρ₀ (f r)) y) =
        fun y => (Real.sqrt (ρ₀ y) * v y) * s67bd_D j (f r) y := by
      funext y; rw [hW]; ring
    have hc2 : ContDiff ℝ 1 (fun y => v y * s67bd_W ρ₀ j (s67psi ρ₀ (f r)) y) := by
      rw [hWfun]; exact hg1.mul (hDu1 j)
    have hI1 : Integrable (fun y => ρ₀ y * s67bd_D j (f r) y) volume :=
      hρ0I.mul_bdd (hDu1 j).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hDub j y)
    have hI2 : Integrable (fun y => v y * s67bd_W ρ₀ j (s67psi ρ₀ (f r)) y) volume := by
      rw [hWfun]
      exact hgI.mul_bdd (hDu1 j).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hDub j y)
    have := s67bd26_force_add hd hs0 hsd hc1 hc2 hI1 hI2 x
    rw [← this]
    congr 1
    funext y
    rw [hρr y, hgrad, hW]; ring
  -- the two integrability claims
  have hmovI : Integrable (fun y =>
      generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y * ρ₀ y) volume := by
    obtain ⟨Bt, hBt⟩ := hf.bdd_time_deriv
    have hmap : Continuous (fun y : Euc d => ((⟨r, hr⟩ : Set.Icc (0 : ℝ) T), y)) :=
      continuous_const.prodMk continuous_id
    have hcont : Continuous (fun y => generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y) :=
      (hf.cont_time_deriv.comp hmap : _)
    have := HRS.MS.MovAdjNl.s67a_int_lin H hcont.aestronglyMeasurable
      (fun x => hBt r hr x) ψs
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    have h := congrFun hψs y
    beta_reduce
    rw [h, Real.mul_self_sqrt (hρpos y).le]
  have hstatI : Integrable (fun y =>
      generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) r (f r) y * ρ₀ y) volume := by
    obtain ⟨Bt, hBt0, hBt⟩ := HRS.MS.MovAdjNl.s67a_L0_growth H hmemcb r
    have := HRS.MS.MovAdjNl.s67a_int_lin H (HRS.MS.MovAdjNl.s67a_L0_meas H hmemcb r)
      hBt ψs
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    have h := congrFun hψs y
    beta_reduce
    rw [h, Real.mul_self_sqrt (hρpos y).le]
  refine ⟨hmovI, hstatI, fun x => ?_⟩
  -- the pointwise identity
  have e1 : generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) x =
      generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ r)) r (f r) x := by
    rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]
  rw [e1, s67_gen_eq s q β (ρ r) r (f r) x, s67_gen_eq s q β ρ₀ r (f r) x]
  have hJ : ∀ (ρ' : Euc d → ℝ), s67J d s ρ' (f r) x =
      ∑ j : Fin d, movForce d s (fun y => ρ' y * gradient (f r) y j) x j := fun ρ' => rfl
  rw [hJ, hJ]
  have hJd : ∑ j : Fin d, movForce d s (fun y => ρ r y * gradient (f r) y j) x j -
      ∑ j : Fin d, movForce d s (fun y => ρ₀ y * gradient (f r) y j) x j =
      ∑ j : Fin d, movForce d s (fun y => v y * s67bd_W ρ₀ j (s67psi ρ₀ (f r)) y) x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := hF2 j x
    have h3 : (fun y => ρ₀ y * gradient (f r) y j) = fun y => ρ₀ y * s67bd_D j (f r) y := by
      funext y; rw [hgrad]
    rw [h3, ← h2]
    simp
  have hFd : movForce d s (ρ r) x = movForce d s ρ₀ x +
      movForce d s (fun y => Real.sqrt (ρ₀ y) * v y) x := (hF1 x).symm
  unfold s67bd_K s67bd_F
  have hin1 : inner ℝ (-(q • x) - movForce d s (ρ r) x) (gradient (f r) x) -
      inner ℝ (-(q • x) - movForce d s ρ₀ x) (gradient (f r) x) =
      -∑ i : Fin d, movForce d s (fun y => Real.sqrt (ρ₀ y) * v y) x i * s67bd_D i (f r) x := by
    rw [← inner_sub_left, hFd, s67bd26_inner, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgrad]
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.neg_apply]
    ring
  have hlin : ∀ a I1 J1 I0 J0 : ℝ, (a + I1 + J1) - (a + I0 + J0) = (I1 - I0) + (J1 - J0) := by
    intros; ring
  rw [hlin, hin1, hJd]
  simp only [hW]
  have hsum : ∑ i : Fin d, movForce d s (fun y => Real.sqrt (ρ₀ y) * v y) x i *
      (Real.sqrt (ρ₀ x) * s67bd_D i (f r) x) =
      Real.sqrt (ρ₀ x) * ∑ i : Fin d, movForce d s (fun y => Real.sqrt (ρ₀ y) * v y) x i *
        s67bd_D i (f r) x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

end HRS.MS.BreakdownS67
