import HRS.Commutator.Whole.XNRSAux1

/-!
# Packet X-NRS, part 2: the recursion `J_m → J_{m-1} + R_m`

For a temperate vector field `v` (`XTVF`) and a Schwartz function `h` Fourier-localised away from `0`,
`J(σ,h) = ∫ (Λ^σ h) (v·∇h)`.  Integration by parts gives
`J(γ+2,h) = ∑_a J(γ,∂_a h) + ∑_{a,c} ∫ Λ^γ(∂_a h) (∂_a v_c) ∂_c h`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- A temperate vector field: each coordinate function has temperate growth. -/
def XTVF (v : Euc d → Euc d) : Prop := ∀ c : Fin d, (fun x => v x c).HasTemperateGrowth

/-- `∂_a v_c`. -/
def xw (v : Euc d → Euc d) (a c : Fin d) (x : Euc d) : ℝ :=
  lineDeriv ℝ (fun y => v y c) x (xe a)

lemma xw_eq_fderiv (v : Euc d → Euc d) (a c : Fin d) (hv : XTVF v) (x : Euc d) :
    xw v a c x = fderiv ℝ (fun y => v y c) x (xe a) := by
  unfold xw
  exact ((hv c).1.differentiable (by simp) x).lineDeriv_eq_fderiv

lemma xtg_xw {v : Euc d → Euc d} (hv : XTVF v) (a c : Fin d) : (xw v a c).HasTemperateGrowth := by
  have h1 : (fderiv ℝ (fun y => v y c)).HasTemperateGrowth := by
    refine ⟨(hv c).1.fderiv_right (m := ∞) (by simp), fun n => ?_⟩
    obtain ⟨k, C, hC⟩ := (hv c).2 (n + 1)
    exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hC x⟩
  have h2 : (fun x => (fderiv ℝ (fun y => v y c) x) (xe a)).HasTemperateGrowth :=
    (((ContinuousLinearMap.apply ℝ ℝ (xe a)).hasTemperateGrowth)).comp h1
  have : xw v a c = fun x => (fderiv ℝ (fun y => v y c) x) (xe a) := by
    funext x; exact xw_eq_fderiv v a c hv x
  rw [this]; exact h2

/-- The Schwartz function `∑_c v_c ∂_c h`. -/
def xadv (v : Euc d → Euc d) (h : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ) :=
  ∑ c, SchwartzMap.smulLeftCLM ℂ (fun x => v x c) (xdr c h)

lemma xadv_apply {v : Euc d → Euc d} (hv : XTVF v) (h : 𝓢(Euc d, ℂ)) (x : Euc d) :
    xadv v h x = ∑ c, ((v x c : ℝ) : ℂ) * xdr c h x := by
  unfold xadv
  rw [SchwartzMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [SchwartzMap.smulLeftCLM_apply_apply (hv c)]
  simp [Complex.real_smul]

/-- multiplication by `∂_a v_c`. -/
def xwmul (v : Euc d → Euc d) (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (xw v a c) Γ

lemma xwmul_apply {v : Euc d → Euc d} (hv : XTVF v) (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)) (x : Euc d) :
    xwmul v a c Γ x = ((xw v a c x : ℝ) : ℂ) * Γ x := by
  unfold xwmul
  rw [SchwartzMap.smulLeftCLM_apply_apply (xtg_xw hv a c)]
  simp [Complex.real_smul]


lemma xdr_comm (a c : Fin d) (h : 𝓢(Euc d, ℂ)) : xdr a (xdr c h) = xdr c (xdr a h) := by
  refine xschwartz_ext_fourier fun ξ => ?_
  rw [fourier_xdr, fourier_xdr, fourier_xdr, fourier_xdr]; ring

lemma xdr_xlam {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (γ : ℝ)
    (a : Fin d) : xdr a (xlam γ ρ h) = xlam γ ρ (xdr a h) := by
  refine xschwartz_ext_fourier fun ξ => ?_
  rw [fourier_xdr, fourier_xlam_of_inD hρ hh, fourier_xlam_of_inD hρ (xInD_xdr hh a), fourier_xdr]
  ring

lemma xint_mul (f g : 𝓢(Euc d, ℂ)) : Integrable (fun x => f x * g x) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 g, fun x => ?_⟩
    simpa using SchwartzMap.le_seminorm ℝ 0 0 g x
  refine (f.integrable.norm.mul_const M).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (f.continuous.mul g.continuous).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)

lemma xdr_xadv {v : Euc d → Euc d} (hv : XTVF v) (a : Fin d) (h : 𝓢(Euc d, ℂ)) :
    xdr a (xadv v h) = ∑ c, xwmul v a c (xdr c h) + xadv v (xdr a h) := by
  ext x
  rw [xdr_apply]
  have hfun : (xadv v h : Euc d → ℂ) = fun y => ∑ c, ((v y c : ℝ) : ℂ) * xdr c h y :=
    funext (xadv_apply hv h)
  rw [hfun]
  have hderiv : ∀ c : Fin d, HasFDerivAt (fun y => ((v y c : ℝ) : ℂ) * xdr c h y)
      (((v x c : ℝ) : ℂ) • fderiv ℝ (xdr c h) x +
        (xdr c h x) • (Complex.ofRealCLM.comp (fderiv ℝ (fun y => v y c) x))) x := by
    intro c
    have h1 : HasFDerivAt (fun y => ((v y c : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (fun y => v y c) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x
        (((hv c).1.differentiable (by simp)) x).hasFDerivAt
    have h2 : HasFDerivAt (fun y => xdr c h y) (fderiv ℝ (xdr c h) x) x :=
      (xdr c h).differentiableAt.hasFDerivAt
    exact h1.mul h2
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ => hderiv c)
  rw [(hsum.hasLineDerivAt (xe a)).lineDeriv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  rw [xadv_apply hv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : fderiv ℝ (xdr c h) x (xe a) = xdr c (xdr a h) x := by
    rw [← xdr_comm, xdr_apply]
    exact ((xdr c h).differentiableAt).lineDeriv_eq_fderiv.symm
  have e2 : fderiv ℝ (fun y => v y c) x (xe a) = xw v a c x := (xw_eq_fderiv v a c hv x).symm
  rw [e1, e2, xwmul_apply hv]
  ring


/-- `J(σ,h) = ∫ (Λ^σ h) (v·∇h)`. -/
def xJ (v : Euc d → Euc d) (ρ : Euc d → ℝ) (σ : ℝ) (h : 𝓢(Euc d, ℂ)) : ℂ :=
  ∫ x, xlam σ ρ h x * xadv v h x

lemma xlam_two {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {u : 𝓢(Euc d, ℂ)} (hu : XInD ρ u) :
    xlam 2 ρ u = -∑ a, xdr a (xdr a u) := by
  refine xschwartz_ext_fourier fun ξ => ?_
  have hF : 𝓕 (-∑ a, xdr a (xdr a u)) = -∑ a, 𝓕 (xdr a (xdr a u)) := by
    have h := map_neg (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := Euc d))
      (∑ a, xdr a (xdr a u))
    have h2 := map_sum (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := Euc d))
      (fun a => xdr a (xdr a u)) Finset.univ
    simpa [h2] using h
  rw [fourier_xlam_of_inD hρ hu, hF, SchwartzMap.neg_apply, SchwartzMap.sum_apply]
  simp only [fourier_xdr]
  have h1 : ∑ a : Fin d, (2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ)) *
      ((2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ)) * 𝓕 u ξ) =
      -((2 * Real.pi * ‖ξ‖ : ℝ) ^ 2 : ℝ) * 𝓕 u ξ := by
    have hs : ∑ a : Fin d, (ξ a) ^ 2 = ‖ξ‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have : ∑ a : Fin d, (2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ)) *
        ((2 * (Real.pi : ℂ) * Complex.I * ((ξ a : ℝ) : ℂ)) * 𝓕 u ξ) =
        (-(4 * (Real.pi : ℂ) ^ 2) * ((∑ a : Fin d, (ξ a) ^ 2 : ℝ) : ℂ)) * 𝓕 u ξ := by
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      have : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination (4 * (Real.pi : ℂ) ^ 2 * ((ξ a : ℝ) : ℂ) ^ 2 * 𝓕 u ξ) * this
    rw [this, hs]
    push_cast
    ring
  rw [h1]
  simp only [neg_neg, Real.rpow_two]
  push_cast
  ring

lemma xlam_add_two {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (γ : ℝ) :
    xlam (γ + 2) ρ h = -∑ a, xdr a (xdr a (xlam γ ρ h)) := by
  rw [← xlam_two hρ (xInD_xlam hρ hh γ), xlam_comp hρ hh, add_comm]


lemma xrec {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {v : Euc d → Euc d} (hv : XTVF v)
    {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) (γ : ℝ) :
    xJ v ρ (γ + 2) h = ∑ a, xJ v ρ γ (xdr a h) +
      ∑ a, ∑ c, ∫ x, xlam γ ρ (xdr a h) x * xwmul v a c (xdr c h) x := by
  set u : 𝓢(Euc d, ℂ) := xlam γ ρ h with hu
  set ψ : 𝓢(Euc d, ℂ) := xadv v h with hψ
  unfold xJ
  rw [xlam_add_two hρ hh γ, ← hu]
  have step1 : ∫ x, (-∑ a, xdr a (xdr a u)) x * ψ x = ∑ a, ∫ x, xdr a u x * xdr a ψ x := by
    have e : ∀ x, (-∑ a, xdr a (xdr a u)) x * ψ x =
        ∑ a, (-(xdr a (xdr a u) x * ψ x)) := by
      intro x
      rw [SchwartzMap.neg_apply, SchwartzMap.sum_apply, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
    simp_rw [e]
    have hint : ∀ a ∈ (Finset.univ : Finset (Fin d)),
        Integrable (fun x => -(xdr a (xdr a u) x * ψ x)) := fun a _ => (xint_mul _ _).neg
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_neg]
    have := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume)
      (xdr a u) ψ (xe a)
    simp only [xdr] at this ⊢
    rw [this]
  rw [step1]
  have step2 : ∀ a : Fin d, ∫ x, xdr a u x * xdr a ψ x =
      (∫ x, xlam γ ρ (xdr a h) x * xadv v (xdr a h) x) +
      ∑ c, ∫ x, xlam γ ρ (xdr a h) x * xwmul v a c (xdr c h) x := by
    intro a
    rw [hψ, xdr_xadv hv a h, hu, xdr_xlam hρ hh γ a]
    have e : ∀ x, xlam γ ρ (xdr a h) x * (∑ c, xwmul v a c (xdr c h) + xadv v (xdr a h)) x =
        xlam γ ρ (xdr a h) x * xadv v (xdr a h) x +
        ∑ c, xlam γ ρ (xdr a h) x * xwmul v a c (xdr c h) x := by
      intro x
      rw [SchwartzMap.add_apply, SchwartzMap.sum_apply, mul_add, Finset.mul_sum]
      ring
    simp_rw [e]
    rw [integral_add (xint_mul _ _) (integrable_finsetSum _ fun c _ => xint_mul _ _),
      integral_finsetSum _ (fun c _ => xint_mul _ _)]
  simp_rw [step2]
  rw [Finset.sum_add_distrib]

end HRS.Commutator.Whole.XNRS
