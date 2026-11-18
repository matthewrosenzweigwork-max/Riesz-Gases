import HRS.PDE.TorusFPExistAux10

/-!
# D1 existence, helper 11: the weak equation for smooth time-independent tests
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem d1_isCk_of_isSmooth {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) (k : ℕ) :
    Torus.IsCk (k : WithTop ℕ∞) φ := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) := hφ
  refine h.of_le ?_
  have h0 : (((k : ℕ) : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  simpa using h0

/-- `d1_gen` of a smooth function is continuous. -/
theorem d1_gen_smooth_continuous {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) : Continuous (d1_gen κ (d1_gradDrift U) φ) :=
  d1_gen_continuous (d1_gradDrift_continuous hU) (by simpa using d1_isCk_of_isSmooth hφ 2)

section WeakSmooth

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

/-- Right derivative of `s ↦ ∫ φ dμ_s`. -/
theorem d1_hasDerivWithinAt_Ioi {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t => ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ t))
      (∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) (Set.Ioi s) s := by
  have := d1_mu_prob hn hκ hU μ₀ s
  rw [hasDerivWithinAt_iff_tendsto_slope]
  rw [show Set.Ioi s \ {s} = Set.Ioi s by simp]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := d1_P_diff_quot hn hκ hU hφ (half_pos hε)
  refine ⟨δ, hδ, fun y hy hyδ => ?_⟩
  have hy' : s < y := hy
  have hpos : 0 < y - s := by linarith
  have hyδ' : y - s < δ := by
    have := hyδ
    rw [Real.dist_eq, abs_of_pos hpos] at this
    exact this
  have hy0 : 0 ≤ y := by linarith
  have hφc : Continuous φ := StaticLimitAux.continuous_of_smooth hφ
  have hPc : Continuous (d1_P hn hκ hU (y - s) φ) := d1_P_continuous hn hκ hU hpos.le hφ
  -- A y - A s = ∫ (P_h φ - φ) dμ_s
  have hA : ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ y) - ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ s) =
      ∫ x, (d1_P hn hκ hU (y - s) φ x - φ x) ∂(d1_mu hn hκ hU μ₀ s) := by
    have h1 := d1_mu_semigroup hn hκ hU μ₀ hs hpos.le hφ
    rw [show s + (y - s) = y by ring] at h1
    rw [d1_mu_integral hn hκ hU μ₀ hy0 hφ, ← h1]
    rw [integral_sub (hPc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hφc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hslope : slope (fun t => ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ t)) s y =
      ∫ x, (d1_P hn hκ hU (y - s) φ x - φ x) / (y - s) ∂(d1_mu hn hκ hU μ₀ s) := by
    rw [slope_def_field, hA, integral_div]
  rw [hslope, Real.dist_eq]
  have hc1 : Continuous fun x => (d1_P hn hκ hU (y - s) φ x - φ x) / (y - s) :=
    (hPc.sub hφc).div_const _
  have := d1_abs_integral_sub_le (ρ := d1_mu hn hκ hU μ₀ s) hc1
    (d1_gen_smooth_continuous (κ := κ) hU hφ) (c := ε / 2) (fun x => hδ' (y - s) hpos hyδ' x)
  linarith

/-- **Weak equation for smooth time-independent tests.** -/
theorem d1_weak_smooth {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ τ) = ∫ x, φ x ∂μ₀ +
      ∫ s in Set.Icc 0 τ, ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s) := by
  have hφc : Continuous φ := StaticLimitAux.continuous_of_smooth hφ
  have hcont := d1_narrow hn hκ hU μ₀ hφc τ
  have hcont' := d1_narrow hn hκ hU μ₀ (d1_gen_smooth_continuous (κ := κ) hU hφ) τ
  have hint : IntervalIntegrable (fun s => ∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s))
      volume 0 τ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hτ]; exact hcont'
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ hcont
    (fun s hs => d1_hasDerivWithinAt_Ioi hn hκ hU μ₀ hφ hs.1.le) hint
  rw [intervalIntegral.integral_of_le hτ, ← integral_Icc_eq_integral_Ioc] at this
  rw [d1_mu_of_nonpos hn hκ hU μ₀ le_rfl] at this
  linarith

end WeakSmooth

end HRS
