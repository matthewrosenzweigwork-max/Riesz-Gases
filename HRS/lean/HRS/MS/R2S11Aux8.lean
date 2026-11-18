import HRS.MS.R2S11Aux7

/-!
# S11.4 items (2), (3): uniform-in-time moment transfer from the actual-density bound of item (1)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole HRS.MS.R2Mt
open HRS (Euc)

variable {d : ℕ}

/-- `ρ ≤ C ρ₀` pointwise gives `ρ dx ≤ C ρ₀ dx` as measures. -/
theorem s11_wd_le {ρ ρ₀ : Euc d → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ρ x ≤ C * ρ₀ x) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal C • HRS.Whole.withDensityReal ρ₀ := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (h x)

/-- Transfer of the iterated second moment under `μ ≤ c • μ'`. -/
theorem s11_S2_transfer {μ μ' : Measure (Euc d)} {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : μ ≤ c • μ')
    (g : Euc d → Euc d → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ y, g x y ∂μ ∂μ ≤ c * c * ∫⁻ x, ∫⁻ y, g x y ∂μ' ∂μ' := by
  have h1 : ∀ x, ∫⁻ y, g x y ∂μ ≤ c * ∫⁻ y, g x y ∂μ' := fun x => by
    calc ∫⁻ y, g x y ∂μ ≤ ∫⁻ y, g x y ∂(c • μ') := lintegral_mono' h le_rfl
      _ = c * ∫⁻ y, g x y ∂μ' := by rw [lintegral_smul_measure, smul_eq_mul]
  calc ∫⁻ x, ∫⁻ y, g x y ∂μ ∂μ ≤ ∫⁻ x, c * ∫⁻ y, g x y ∂μ' ∂μ := lintegral_mono h1
    _ ≤ ∫⁻ x, c * ∫⁻ y, g x y ∂μ' ∂(c • μ') := lintegral_mono' h le_rfl
    _ = c * (c * ∫⁻ x, ∫⁻ y, g x y ∂μ' ∂μ') := by
        rw [lintegral_smul_measure, smul_eq_mul, lintegral_const_mul' _ _ hc]
    _ = _ := by ring

/-- The difference kernel of a uniformly approximated family is bounded by `(C₂ B + B)(1 + W_s)`. -/
theorem s11_diff_unif {Θ : Type*} {s C₂ B : ℝ} {μ : Measure (Euc d)} {h : Θ → Euc d → Euc d → ℝ}
    {hj : Θ → ℕ → Euc d → Euc d → ℝ} (hh : ∀ θ, IsBoundedPairKernel s B (h θ))
    (hu : IsR2UniformApprox s C₂ B μ h hj) (θ : Θ) (j : ℕ) :
    IsBoundedPairKernel s (C₂ * B + B) (fun x y => hj θ j x y - h θ x y) where
  measurable := by
    obtain ⟨m, c, u, hu', e⟩ := hu.finiteRank θ j
    have h1 : Measurable (Function.uncurry (hj θ j)) := by
      rw [e]; exact s92_finiteRank_meas hu'
    exact h1.sub (hh θ).measurable
  symm := by
    obtain ⟨m, c, u, hu', e⟩ := hu.finiteRank θ j
    intro x y
    rw [e, s92_finiteRank_symm hu' x y, (hh θ).symm x y]
  bound := by
    intro x y hxy
    have h1 := hu.envelope θ j x y hxy
    have h2 := (hh θ).bound x y hxy
    calc |hj θ j x y - h θ x y| ≤ |hj θ j x y| + |h θ x y| := abs_sub _ _
      _ ≤ C₂ * B * (1 + rieszWeight s (x - y)) + B * (1 + rieszWeight s (x - y)) := add_le_add h1 h2
      _ = (C₂ * B + B) * (1 + rieszWeight s (x - y)) := by ring

/-- The class-uniform tail: `R2ActualFTailFam` along the moving references. -/
theorem s11_tail_fam_class (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ₀ : Euc d → ℝ} {ρ : ℝ → Euc d → ℝ} {M L pinf K B rr C₁ C₂ : ℝ} (hβ : 0 < β) (hpinf : 1 < pinf)
    (hrr : 1 ≤ rr) (hC₁ : 0 ≤ C₁) (hprob₀ : HRS.Whole.IsProbDensity ρ₀)
    (hρle : ∀ t : ℝ≥0, ∀ x, ρ t x ≤ C₁ * ρ₀ x)
    (hR2 : ∀ t : ℝ≥0, IsRound2Density d s M L (ρ t))
    {Pf : ℝ≥0 → ∀ N, Measure (EucConfig d N)}
    (hAD : ∀ (t : ℝ≥0) (N : ℕ), 2 ≤ N → HasR2ActualDensity s β pinf K (HRS.Whole.withDensityReal (ρ t)) (Pf t N))
    {Θ : Type} {h : Θ → Euc d → Euc d → ℝ} {hj : Θ → ℕ → Euc d → Euc d → ℝ}
    (hh : ∀ θ, IsBoundedPairKernel s B (h θ)) (hu : IsR2UniformApprox s C₂ B (HRS.Whole.withDensityReal ρ₀) h hj) :
    R2ActualFTailFam (fun t : ℝ≥0 => HRS.Whole.withDensityReal (ρ t)) rr h hj Pf := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  set c : ℝ≥0∞ := ENNReal.ofReal C₁ with hc
  have hcne : c ≠ ⊤ := ENNReal.ofReal_ne_top
  set τ : ℕ → ℝ≥0∞ := fun j => c * c * (⨆ θ : Θ, eLpNorm (fun q : Euc d × Euc d => hj θ j q.1 q.2 - h θ q.1 q.2)
    (ENNReal.ofReal 2) ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀))) ^ 2 with hτdef
  have hτ : Tendsto τ atTop (𝓝 0) := by
    have h0 := hu.converges 2 (by norm_num) (by linarith)
    have hc2 : Tendsto (fun x : ℝ≥0∞ => c * c * x ^ 2) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun x : ℝ≥0∞ => c * c * x ^ 2) :=
        (ENNReal.continuous_const_mul (ENNReal.mul_ne_top hcne hcne)).comp (ENNReal.continuous_pow 2)
      simpa using this.tendsto 0
    exact hc2.comp h0
  have hμ : ∀ t : ℝ≥0, IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ t)) := fun t => s92_isProb_mu (hR2 t).prob
  have key := s11_tailFam (ι := ℝ≥0) (Θ := Θ) hd hs0 hs M L β pinf K B rr C₂ hβ hpinf hrr hR2 hAD
    (h := h) (hj := hj) (fun θ j => s11_diff_unif hh hu θ j) hτ ?_
  · exact key
  · intro θ i j
    haveI := hμ i
    have hDm : Measurable (Function.uncurry fun x y => hj θ j x y - h θ x y) :=
      (s11_diff_unif hh hu θ j).measurable
    have hle := s11_wd_le hC₁ (hρle i)
    haveI := s92_isProb_mu hprob₀
    rw [← s92_S2_eq (f := fun x y => hj θ j x y - h θ x y) hDm]
    calc ∫⁻ x, ∫⁻ y, ‖hj θ j x y - h θ x y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal (ρ i)) ∂(HRS.Whole.withDensityReal (ρ i))
        ≤ c * c * ∫⁻ x, ∫⁻ y, ‖hj θ j x y - h θ x y‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ₀) ∂(HRS.Whole.withDensityReal ρ₀) :=
          s11_S2_transfer hcne hle _
      _ = c * c * (eLpNorm (fun q : Euc d × Euc d => hj θ j q.1 q.2 - h θ q.1 q.2) (ENNReal.ofReal 2)
            ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀))) ^ 2 := by
          rw [s92_S2_eq (f := fun x y => hj θ j x y - h θ x y) hDm]
      _ ≤ τ j := by
          have := le_iSup (fun θ' : Θ => eLpNorm (fun q : Euc d × Euc d => hj θ' j q.1 q.2 - h θ' q.1 q.2)
            (ENNReal.ofReal 2) ((HRS.Whole.withDensityReal ρ₀).prod (HRS.Whole.withDensityReal ρ₀))) θ
          exact mul_le_mul_right (pow_le_pow_left' this 2) _

end HRS.MS.R2S11
