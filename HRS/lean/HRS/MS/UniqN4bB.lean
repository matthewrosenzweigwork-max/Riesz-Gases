import HRS.MS.UniqN4bA
import HRS.MS.UniqM2

/-!
# N4b of `UniqPlan.md`, part B: the `H¹` norm of a `C¹_c` function from its gradient

* `n4b_diff_bound`: for `ψ ∈ C¹_c`, `∫ (ψ x - ψ (x - h))² ≤ ‖h‖² ∫ ‖∇ψ‖²`
  (fundamental theorem of calculus along `s ↦ x - h + s h`, Jensen, Tonelli, translation invariance).
* `n4b_sob_one`: if `‖ψ‖₂ ≤ a` and `∫ ‖∇ψ‖² ≤ Γ²`, then `ψ ∈ H¹`, `sobolevNormE 0 ψ ≤ a` and
  `sobolevNormE 1 ψ ≤ a + √d Γ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.MS.UniqM1 HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- Jensen on `[0,1]` for continuous functions. -/
theorem n4b_sq_integral_le {u : ℝ → ℝ} (hu : Continuous u) :
    (∫ s in (0 : ℝ)..1, u s) ^ 2 ≤ ∫ s in (0 : ℝ)..1, (u s) ^ 2 := by
  set m : ℝ := ∫ s in (0 : ℝ)..1, u s with hm
  have hi1 : IntervalIntegrable u volume 0 1 := hu.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => (u s) ^ 2) volume 0 1 := (hu.pow 2).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun s => 2 * m * u s - m ^ 2) volume 0 1 :=
    ((continuous_const.mul hu).sub continuous_const).intervalIntegrable _ _
  have hle : ∫ s in (0 : ℝ)..1, (2 * m * u s - m ^ 2) ≤ ∫ s in (0 : ℝ)..1, (u s) ^ 2 := by
    refine intervalIntegral.integral_mono_on zero_le_one hi3 hi2 fun s _ => ?_
    nlinarith [sq_nonneg (u s - m)]
  have heq : ∫ s in (0 : ℝ)..1, (2 * m * u s - m ^ 2) = m ^ 2 := by
    rw [intervalIntegral.integral_sub (hi1.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, ← hm]
    simp
    ring
  linarith

theorem n4b_fderiv_cont {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) : Continuous (fun x => ‖fderiv ℝ ψ x‖ ^ 2) :=
  ((hψ.continuous_fderiv one_ne_zero).norm).pow 2

theorem n4b_fderiv_supp {ψ : Euc d → ℝ} (hψc : HasCompactSupport ψ) :
    HasCompactSupport (fun x => ‖fderiv ℝ ψ x‖ ^ 2) := by
  refine (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun v : Euc d →L[ℝ] ℝ => ‖v‖ ^ 2) (by simp)

/-- Pointwise: `(ψ x - ψ (x - h))² ≤ ‖h‖² ∫₀¹ ‖∇ψ(x - h + s h)‖² ds`. -/
theorem n4b_diff_pt {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (h x : Euc d) :
    (ψ x - ψ (x - h)) ^ 2 ≤
      ‖h‖ ^ 2 * ∫ s in (0 : ℝ)..1, ‖fderiv ℝ ψ (x - h + s • h)‖ ^ 2 := by
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hder : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ψ (x - h + s • h)) (fderiv ℝ ψ (x - h + s • h) h) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x - h + s • h) h s := by
      simpa using ((hasDerivAt_id s).smul_const h).const_add (x - h)
    exact (hdiff _).hasFDerivAt.comp_hasDerivAt s h1
  have hcont : Continuous (fun s : ℝ => fderiv ℝ ψ (x - h + s • h) h) :=
    ((hψ.continuous_fderiv one_ne_zero).comp (by fun_prop : Continuous fun s : ℝ => x - h + s • h)).clm_apply
      continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun s _ => hder s) (hcont.intervalIntegrable _ _)
  simp only [one_smul, zero_smul, add_zero, sub_add_cancel] at hftc
  rw [← hftc]
  refine (n4b_sq_integral_le hcont).trans ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one ((hcont.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul ((n4b_fderiv_cont hψ).comp
      (by fun_prop : Continuous fun s : ℝ => x - h + s • h))).intervalIntegrable _ _) fun s _ => ?_
  have := (fderiv ℝ ψ (x - h + s • h)).le_opNorm h
  have h0 : |fderiv ℝ ψ (x - h + s • h) h| ≤ ‖fderiv ℝ ψ (x - h + s • h)‖ * ‖h‖ := by
    simpa [Real.norm_eq_abs] using this
  calc (fderiv ℝ ψ (x - h + s • h) h) ^ 2 = |fderiv ℝ ψ (x - h + s • h) h| ^ 2 := (sq_abs _).symm
    _ ≤ (‖fderiv ℝ ψ (x - h + s • h)‖ * ‖h‖) ^ 2 := by gcongr
    _ = ‖h‖ ^ 2 * ‖fderiv ℝ ψ (x - h + s • h)‖ ^ 2 := by ring

theorem n4b_diff_bound {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (h : Euc d) :
    ∫ x, (ψ x - ψ (x - h)) ^ 2 ≤ (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) * ‖h‖ ^ 2 := by
  set Φ : Euc d → ℝ := fun x => ‖fderiv ℝ ψ x‖ ^ 2 with hΦ
  have hΦc : Continuous Φ := n4b_fderiv_cont hψ
  have hΦi : Integrable Φ volume := hΦc.integrable_of_hasCompactSupport (n4b_fderiv_supp hψc)
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => by simp only [hΦ]; positivity
  have hPc : Continuous (fun x => (ψ x - ψ (x - h)) ^ 2) :=
    ((hψ.continuous.sub (hψ.continuous.comp (continuous_id.sub continuous_const))).pow 2)
  have hPs : HasCompactSupport (fun x => (ψ x - ψ (x - h)) ^ 2) := by
    have h1 : HasCompactSupport (fun x => ψ x - ψ (x - h)) :=
      hψc.sub (hψc.comp_homeomorph (Homeomorph.subRight h))
    exact h1.comp_left (g := fun y : ℝ => y ^ 2) (by simp)
  have hPi : Integrable (fun x => (ψ x - ψ (x - h)) ^ 2) volume :=
    hPc.integrable_of_hasCompactSupport hPs
  have hmap : Continuous (fun p : Euc d × ℝ => p.1 - h + p.2 • h) := by fun_prop
  set Θ : Euc d → ℝ := fun x => ∫ s in (0 : ℝ)..1, Φ (x - h + s • h) with hΘ
  -- `ofReal Θ` as an iterated lintegral
  have hΘl : ∀ x, ENNReal.ofReal (Θ x) = ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (Φ (x - h + s • h)) := by
    intro x
    have hc : Continuous (fun s : ℝ => Φ (x - h + s • h)) :=
      hΦc.comp (by fun_prop : Continuous fun s : ℝ => x - h + s • h)
    simp only [hΘ]
    rw [intervalIntegral.integral_of_le zero_le_one,
      ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Ioc)
        (Eventually.of_forall fun s => hΦ0 _)]
  have hswap : ∫⁻ x, ENNReal.ofReal (Θ x) = ENNReal.ofReal (∫ x, Φ x) := by
    simp_rw [hΘl]
    rw [lintegral_lintegral_swap]
    · have : ∀ s : ℝ, ∫⁻ x, ENNReal.ofReal (Φ (x - h + s • h)) = ∫⁻ x, ENNReal.ofReal (Φ x) := by
        intro s
        have := lintegral_add_right_eq_self (μ := (volume : Measure (Euc d)))
          (fun x => ENNReal.ofReal (Φ x)) (s • h - h)
        simp only [← this]
        congr 1; ext x; congr 2; abel
      simp_rw [this]
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
      simp [ofReal_integral_eq_lintegral_ofReal hΦi (Eventually.of_forall hΦ0)]
    · exact (ENNReal.measurable_ofReal.comp (hΦc.comp hmap).measurable).aemeasurable
  have hle : ENNReal.ofReal (∫ x, (ψ x - ψ (x - h)) ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2) * ENNReal.ofReal (∫ x, Φ x) := by
    rw [← hswap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ofReal_integral_eq_lintegral_ofReal hPi (Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (n4b_diff_pt hψ h x)
  rw [← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (integral_nonneg hΦ0))] at hle
  linarith

/-- **`H¹` norm from the gradient.** -/
theorem n4b_sob_one {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    {a Γ : ℝ} (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (h0 : eLpNorm ψ 2 volume ≤ ENNReal.ofReal a)
    (h1 : ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 ≤ Γ ^ 2) :
    HRS.PDE.ToolboxRd.MemSobolev 1 ψ ∧ sobolevNormE 0 ψ ≤ ENNReal.ofReal a ∧
      sobolevNormE 1 ψ ≤ ENNReal.ofReal (a + Real.sqrt d * Γ) := by
  have hmem : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hC := n4b_diff_bound hψ hψc
  have hS1 : HRS.PDE.ToolboxRd.MemSobolev 1 ψ :=
    memSobolev_one_of_diff_bound hmem _ hC
  have hE0 : sobolevNormE 0 ψ ≤ ENNReal.ofReal a := by
    rw [sobolevNormE_zero_eq hmem]; exact h0
  refine ⟨hS1, hE0, ?_⟩
  obtain ⟨_, hsq0⟩ := HRS.MS.UniqM2.memSobolev_of_sobolevNormE_le ha hE0
  have e0 : sobolevNormSq 0 ψ = ∫ ξ : Euc d, ‖fourierL2 ψ ξ‖ ^ 2 := by
    rw [sobolevNormSq_eq]
    simp only [Real.rpow_zero, one_mul]
  have hint0 := integrable_norm_sq_fourierL2 hmem
  have hcoord := fun i => coord_integrable hmem _ hC i
  have e1 : sobolevNormSq 1 ψ = (∫ ξ : Euc d, ‖fourierL2 ψ ξ‖ ^ 2) +
      ∑ i : Fin d, ∫ ξ : Euc d, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2 := by
    rw [sobolevNormSq_eq]
    have hsI : Integrable (fun ξ : Euc d => ∑ i : Fin d,
        4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2) volume :=
      integrable_finsetSum _ fun i _ => (hcoord i).1
    rw [← integral_finsetSum _ fun i _ => (hcoord i).1, ← integral_add hint0 hsI]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [Real.rpow_one]
    have hn : ‖ξ‖ ^ 2 = ∑ i : Fin d, (ξ i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp
    simp only [wt, hn, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hsum : ∑ i : Fin d, ∫ ξ : Euc d, 4 * Real.pi ^ 2 * (ξ i) ^ 2 * ‖fourierL2 ψ ξ‖ ^ 2 ≤
      d * Γ ^ 2 := by
    calc _ ≤ ∑ i : Fin d, ((∫ x, ‖fderiv ℝ ψ x‖ ^ 2) * 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := (hcoord i).2
          simpa using this
      _ ≤ ∑ i : Fin d, Γ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_one]; exact h1
      _ = d * Γ ^ 2 := by simp
  have hsq1 : sobolevNormSq 1 ψ ≤ a ^ 2 + d * Γ ^ 2 := by
    rw [e1]; rw [e0] at hsq0; linarith
  have hE1 : sobolevNormE 1 ψ = ENNReal.ofReal (Real.sqrt (sobolevNormSq 1 ψ)) := by
    unfold sobolevNormE
    rw [if_pos hS1]
  rw [hE1]
  refine ENNReal.ofReal_le_ofReal ?_
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hd : Real.sqrt d ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  nlinarith [mul_nonneg (mul_nonneg ha (Real.sqrt_nonneg (d : ℝ))) hΓ]

/-- From an `L²` bound on the gradient (as an `eLpNorm`) to the integral bound. -/
theorem n4b_int_le_of_eLp {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    {Γ : ℝ} (hΓ : 0 ≤ Γ) (h : eLpNorm (fun x => ‖fderiv ℝ ψ x‖) 2 volume ≤ ENNReal.ofReal Γ) :
    ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 ≤ Γ ^ 2 := by
  have hm : AEStronglyMeasurable (fun x => ‖fderiv ℝ ψ x‖) volume :=
    (hψ.continuous_fderiv one_ne_zero).norm.aestronglyMeasurable
  have hsq := sq_eLpNorm_two hm
  have hI : Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2) volume :=
    (n4b_fderiv_cont hψ).integrable_of_hasCompactSupport (n4b_fderiv_supp hψc)
  have h1 : ENNReal.ofReal (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) = eLpNorm (fun x => ‖fderiv ℝ ψ x‖) 2 volume ^ 2 := by
    rw [hsq, ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    simp
  have h2 : ENNReal.ofReal (∫ x, ‖fderiv ℝ ψ x‖ ^ 2) ≤ ENNReal.ofReal (Γ ^ 2) := by
    rw [h1, ENNReal.ofReal_pow hΓ]
    exact pow_le_pow_left' h 2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **`H¹` norm from an `L²` bound of the gradient.** -/
theorem n4b_sob_one' {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    {a Γ : ℝ} (ha : 0 ≤ a) (hΓ : 0 ≤ Γ) (h0 : eLpNorm ψ 2 volume ≤ ENNReal.ofReal a)
    (h1 : eLpNorm (fun x => ‖fderiv ℝ ψ x‖) 2 volume ≤ ENNReal.ofReal Γ) :
    HRS.PDE.ToolboxRd.MemSobolev 1 ψ ∧ sobolevNormE 0 ψ ≤ ENNReal.ofReal a ∧
      sobolevNormE 1 ψ ≤ ENNReal.ofReal (a + Real.sqrt d * Γ) :=
  n4b_sob_one hψ hψc ha hΓ h0 (n4b_int_le_of_eLp hψ hψc hΓ h1)

/-- Integral bound on a measurable set to an `eLpNorm` bound of the indicator. -/
theorem n4b_eLp_le {u : Euc d → ℝ} {E : Set (Euc d)} (hu : AEStronglyMeasurable u volume)
    (hE : MeasurableSet E) (hint : IntegrableOn (fun y => u y ^ 2) E volume) {G : ℝ} (hG : 0 ≤ G)
    (h : ∫ y in E, u y ^ 2 ≤ G ^ 2) : eLpNorm (E.indicator u) 2 volume ≤ ENNReal.ofReal G := by
  have hind : AEStronglyMeasurable (E.indicator u) volume := hu.indicator hE
  have hsq : eLpNorm (E.indicator u) 2 volume ^ 2 ≤ ENNReal.ofReal G ^ 2 := by
    rw [sq_eLpNorm_two hind]
    have hl : ∫⁻ y, ‖E.indicator u y‖ₑ ^ 2 = ∫⁻ y in E, ‖u y‖ₑ ^ 2 := by
      rw [← lintegral_indicator hE]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ E <;> simp [hy]
    rw [hl, ← ENNReal.ofReal_pow hG]
    have : ∫⁻ y in E, ‖u y‖ₑ ^ 2 = ENNReal.ofReal (∫ y in E, u y ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => sq_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
      simp
    rw [this]
    exact ENNReal.ofReal_le_ofReal h
  by_contra hlt
  exact absurd hsq (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hlt)))

end HRS.MS.UniqN4b
