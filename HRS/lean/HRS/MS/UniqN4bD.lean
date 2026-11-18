import HRS.MS.UniqN4bC

/-!
# N4b of `UniqPlan.md`, part D: the near-field integration by parts

For `θ ∈ C¹_c` supported in a measurable set `E` and `f ∈ C¹`, with `H = g * ∂_iψ` and `ρ' ∈ C¹` bounded by `Cρ`:
`∫ θ f (∂_jρ' H + ρ' ∂_jH) = -∫ ρ' H (θ ∂_j f + f ∂_jθ)` and hence
`|∫ θ f (...)| ≤ Cρ ‖1_E H‖₂ (‖1_E ∂_j f‖₂ + Lθ ‖1_E f‖₂)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1
  HRS.MS.UniqNDefs HRS.MS.UniqN2b HRS.MS.UniqN0 HRS.MS.UniqN1c

variable {d : ℕ}

theorem n4b_kcd_contDiff {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    ContDiff ℝ 1 (kernelConvDeriv d s i ψ) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hconv : kernelConvDeriv d s i ψ =
      convolution (D1 i ψ) (rieszKernel d s) (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext y
    show HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) y = _
    simp only [HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1; funext t; ring
  rw [hconv]
  exact (D1_supp hψc i).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    (D1_contDiff hψ i) hl

/-- The derivative of `ρ' H_i` as a sum of two products. -/
theorem n4b_X_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ' : Euc d → ℝ}
    (hρ : ContDiff ℝ 1 ρ') {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin d) (y : Euc d) :
    fderiv ℝ (fun y => ρ' y * kernelConvDeriv d s i ψ y) y (EuclideanSpace.single j (1 : ℝ)) =
      D1 j ρ' y * kernelConvDeriv d s i ψ y + ρ' y * D1 j (kernelConvDeriv d s i ψ) y := by
  rw [n2b_fderiv_prod hs0 hsd hρ hψ hψc i j y, n1c_D1_kcd hs0 hsd hψ hψc i j y]

theorem n4b_X_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ' : Euc d → ℝ}
    (hρ : ContDiff ℝ 1 ρ') {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin d) :
    Continuous (fun y => D1 j ρ' y * kernelConvDeriv d s i ψ y +
      ρ' y * D1 j (kernelConvDeriv d s i ψ) y) := by
  have h1 : Continuous (D1 j ρ') := (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h2 : Continuous (kernelConvDeriv d s i ψ) :=
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  exact (h1.mul h2).add (hρ.continuous.mul (n1c_D1_kcd_cont hs0 hsd hψ hψc i j))

/-- **The near-field estimate.** -/
theorem n4b_near {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {ρ' : Euc d → ℝ}
    (hρ : ContDiff ℝ 1 ρ') {Cρ : ℝ} (hCρ : 0 ≤ Cρ) (hρb : ∀ y, |ρ' y| ≤ Cρ)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    {f θ : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    {E : Set (Euc d)} (hEm : MeasurableSet E) (hθE : tsupport θ ⊆ E)
    {Lθ : ℝ} (hLθ : 0 ≤ Lθ) (hθ1 : ∀ y, |θ y| ≤ 1) (hθ' : ∀ y, |D1 j θ y| ≤ Lθ)
    {h G m : ℝ} (hh : 0 ≤ h) (hG : 0 ≤ G) (hm : 0 ≤ m)
    (hH : eLpNorm (E.indicator (kernelConvDeriv d s i ψ)) 2 volume ≤ ENNReal.ofReal h)
    (hG' : eLpNorm (E.indicator (D1 j f)) 2 volume ≤ ENNReal.ofReal G)
    (hm' : eLpNorm (E.indicator f) 2 volume ≤ ENNReal.ofReal m) :
    |∫ y, θ y * f y * (D1 j ρ' y * kernelConvDeriv d s i ψ y +
        ρ' y * D1 j (kernelConvDeriv d s i ψ) y)| ≤ Cρ * h * (G + Lθ * m) := by
  set H : Euc d → ℝ := kernelConvDeriv d s i ψ with hHdef
  set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
  have hHc : ContDiff ℝ 1 H := n4b_kcd_contDiff hs0 hsd hψ hψc i
  set k : Euc d → ℝ := fun y => ρ' y * H y with hk
  have hkC : ContDiff ℝ 1 k := hρ.mul hHc
  set F : Euc d → ℝ := fun y => θ y * f y with hF
  have hFC : ContDiff ℝ 1 F := hθ.mul hf
  have hFc : HasCompactSupport F := hθc.mul_right
  -- integration by parts
  have hibp := n0_ibp hFC hFc (fun t _ => hkC.contDiffAt) e
  have hrew : ∫ y, θ y * f y * (D1 j ρ' y * H y + ρ' y * D1 j H y) =
      -∫ y, k y * fderiv ℝ F y e := by
    have h1 : ∀ y, θ y * f y * (D1 j ρ' y * H y + ρ' y * D1 j H y) = fderiv ℝ k y e * F y := by
      intro y
      have := n4b_X_eq hs0 hsd hρ hψ hψc i j y
      rw [hk, ← this, hF]
      ring
    simp_rw [h1]
    have : ∫ y, k y * fderiv ℝ F y e = -∫ y, fderiv ℝ k y e * F y := hibp
    rw [this, neg_neg]
  rw [hrew, abs_neg]
  -- Cauchy–Schwarz
  have hFd : ∀ t, fderiv ℝ F t e = θ t * D1 j f t + f t * D1 j θ t := by
    intro t
    have := fderiv_fun_mul (hθ.differentiable one_ne_zero t) (hf.differentiable one_ne_zero t)
    rw [hF, this]
    simp [D1, he]
  have hF0 : ∀ t, t ∉ E → fderiv ℝ F t = 0 := by
    intro t ht
    by_contra h0
    have h1 : t ∈ tsupport F := (support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h0)
    have h2 : tsupport F ⊆ tsupport θ :=
      closure_mono (Function.support_mul_subset_left θ f)
    exact ht (hθE (h2 h1))
  have hHm : AEStronglyMeasurable (E.indicator H) volume :=
    hHc.continuous.aestronglyMeasurable.indicator hEm
  have hv1 : AEStronglyMeasurable (E.indicator (D1 j f)) volume :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable.indicator hEm
  have hv2 : AEStronglyMeasurable (fun t => Lθ * E.indicator f t) volume :=
    (hf.continuous.aestronglyMeasurable.indicator hEm).const_mul Lθ
  have hv2b : eLpNorm (fun t => Lθ * E.indicator f t) 2 volume ≤ ENNReal.ofReal (Lθ * m) := by
    have : (fun t => Lθ * E.indicator f t) = Lθ • E.indicator f := by
      funext t; simp
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hLθ,
      ENNReal.ofReal_mul hLθ]
    gcongr
  refine n4b_cs (w := fun y => k y * fderiv ℝ F y e) hHm hv1 hv2 hCρ hh hG (mul_nonneg hLθ hm)
    ?_ hH hG' hv2b
  intro t
  by_cases ht : t ∈ E
  · simp only [Set.indicator_of_mem ht, hk, hFd t]
    have h1 : |ρ' t| ≤ Cρ := hρb t
    have h2a : |θ t * D1 j f t| ≤ |D1 j f t| := by
      rw [abs_mul]
      calc |θ t| * |D1 j f t| ≤ 1 * |D1 j f t| := mul_le_mul_of_nonneg_right (hθ1 t) (abs_nonneg _)
        _ = _ := one_mul _
    have h2b : |f t * D1 j θ t| ≤ |Lθ * f t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hLθ]
      calc |f t| * |D1 j θ t| ≤ |f t| * Lθ := mul_le_mul_of_nonneg_left (hθ' t) (abs_nonneg _)
        _ = _ := mul_comm _ _
    have h2 : |θ t * D1 j f t + f t * D1 j θ t| ≤ |D1 j f t| + |Lθ * f t| :=
      (abs_add_le _ _).trans (add_le_add h2a h2b)
    rw [abs_mul, abs_mul]
    calc |ρ' t| * |H t| * |θ t * D1 j f t + f t * D1 j θ t|
        ≤ Cρ * |H t| * (|D1 j f t| + |Lθ * f t|) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2 (abs_nonneg _) ?_
          positivity
      _ = _ := by ring
  · have := hF0 t ht
    simp only [hk, Set.indicator_of_notMem ht, this]
    simp

end HRS.MS.UniqN4b
