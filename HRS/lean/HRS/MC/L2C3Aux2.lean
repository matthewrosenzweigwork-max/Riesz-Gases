import HRS.MC.L2C3a
import HRS.MC.L2C1Aux2

/-!
# Packet L2C-3, helper 2: the generator perturbation for continuous (and `L²(μ_β)`) test functions

`l2c3_pert_cont` is `HRS.MC.L2C3a.l2c3a_proof` with the smooth test function `h` replaced by a continuous one
(the proof is identical: smoothness of `h` was used only through its continuity).  `l2c3_pert_Lp` extends the form
bound to every element of `L²(μ_β)` by density of the continuous functions.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.MC.L2C3a HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_pert_cont (R : Regime d) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 ≤ t → ∀ f h : Torus d → ℝ, Torus.IsSmooth f → Continuous h →
      |∫ x, (backwardGenerator R.D (R.ρ t) f x - backwardGenerator R.D R.ρβ f x) * h x| ≤
        C * Real.exp (-κ * t) * Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2) * Real.sqrt (PDE.l2NormSq h) := by
  obtain ⟨C0, c0, hc0, H0⟩ := HRS.MC.RegSet.relax_proof R 0
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R 0
  have hs : R.D.s + 1 < d := by
    have h1 := R.hs
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast R.hd
    linarith
  obtain ⟨CG, hG, hGi⟩ := l2c3a_kernel R.hd R.D.hs0 hs
  set k : Torus d → ℝ := fun z => ‖periodicRieszGrad d R.D.s z‖ with hk
  have hki : Integrable k := hGi.norm
  have hk0 : ∀ z, 0 ≤ k z := fun z => norm_nonneg _
  have hkm : Measurable k := hG.meas.norm
  set N := ∫ z, k z with hN
  have hN0 : 0 ≤ N := integral_nonneg hk0
  refine ⟨2 * N * C0, c0, hc0, ?_⟩
  intro t ht f h hf hhc
  have hρ1 := (hΛ t t ⟨ht, le_rfl⟩).1
  have hρ1c : Continuous (R.ρ t) := l2c3a_cont_of_isCk0 hρ1
  have hρβ := l2c3a_isCk_of_smooth R.thermal.2.1 0
  have hρβc : Continuous R.ρβ := l2c3a_cont_of_isCk0 hρβ
  obtain ⟨B₁, hB₁0, hB₁⟩ := l2c3a_bdd_of_cont _ hρ1c
  obtain ⟨B₂, hB₂0, hB₂⟩ := l2c3a_bdd_of_cont _ hρβc
  have hδ : Torus.IsCk ((0 : ℕ) : WithTop ℕ∞) (fun x => R.ρ t x - R.ρβ x) :=
    hρ1.sub hρβ
  set ε := C0 * Real.exp (-c0 * t) with hεdef
  have hε : ∀ x, |R.ρ t x - R.ρβ x| ≤ ε := fun x =>
    (HRS.PDE.R2Aux.abs_le_cbNorm hδ x).trans (H0 t ht)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0)
  have hf1 := l2c3a_isCk_of_smooth hf 1
  have hgc : Continuous (Torus.grad f) := HRS.PDE.MFLinear.continuous_grad hf1
  obtain ⟨Bg, hBg0, hBg⟩ := l2c3a_bdd_of_cont _ hgc
  obtain ⟨Bh, hBh0, hBh⟩ := l2c3a_bdd_of_cont _ hhc
  set a : Torus d → ℝ := fun x => ‖Torus.grad f x‖ with ha
  set b : Torus d → ℝ := fun x => |h x| with hb
  have ham : Measurable a := hgc.measurable.norm
  have hbm : Measurable b := hhc.measurable.abs
  have haB : ∀ x, |a x| ≤ Bg := fun x => by
    simp only [ha, abs_norm]; exact hBg x
  have hbB : ∀ x, |b x| ≤ Bh := fun x => by
    simp only [hb, abs_abs]; simpa using hBh x
  have hpt : ∀ x, |backwardGenerator R.D (R.ρ t) f x - backwardGenerator R.D R.ρβ f x| ≤
      ε * (N * a x + ∫ z, k z * a (x - z)) := fun x =>
    l2c3a_diff_bound R.D R.hd R.hM hs hρ1c.measurable hρβc.measurable
      (fun x => by simpa using hB₁ x) (fun x => by simpa using hB₂ x) hε hf1 x
  have hint1 : Integrable (fun x => a x * b x) := l2c3a_integrable_of_bdd (ham.mul hbm)
    (B := Bg * Bh) fun x => by
      rw [abs_mul]; exact mul_le_mul (haB x) (hbB x) (abs_nonneg _) hBg0 |>.trans_eq rfl
  have hint2 := l2c3a_conv_mul_integrable hki hk0 ham hbm haB hbB
  have hrhs : Integrable (fun x => ε * (N * (a x * b x) + (∫ z, k z * a (x - z)) * b x)) :=
    ((hint1.const_mul N).add hint2).const_mul ε
  have step1 : |∫ x, (backwardGenerator R.D (R.ρ t) f x - backwardGenerator R.D R.ρβ f x) * h x| ≤
      ∫ x, ε * (N * (a x * b x) + (∫ z, k z * a (x - z)) * b x) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hrhs
      (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_right (hpt x) (abs_nonneg (h x))
    calc _ ≤ ε * (N * a x + ∫ z, k z * a (x - z)) * |h x| := this
      _ = _ := by simp only [hb]; ring
  have hcs := l2c3a_cs ham hbm haB hbB
  have hsch := l2c3a_schur hki hk0 ham hbm haB hbB
  have hbsq : ∫ x, b x ^ 2 = PDE.l2NormSq h := by
    simp only [hb, sq_abs]; rfl
  have hasq : ∫ x, a x ^ 2 = ∫ x, ‖Torus.grad f x‖ ^ 2 := rfl
  rw [hbsq, hasq] at hcs hsch
  rw [integral_const_mul, integral_add (hint1.const_mul N) hint2, integral_const_mul] at step1
  have hex : Real.exp (-c0 * t) = Real.exp (-c0 * t) := rfl
  refine step1.trans ?_
  set A := Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2)
  set H := Real.sqrt (PDE.l2NormSq h)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  calc ε * ((N * ∫ x, a x * b x) + ∫ x, (∫ z, k z * a (x - z)) * b x)
      ≤ ε * (N * (A * H) + N * (A * H)) := by
        gcongr
    _ = 2 * N * C0 * Real.exp (-c0 * t) * A * H := by simp only [hεdef]; ring


/-- A bound `|⟨e, g⟩| ≤ M ‖g‖` on the continuous functions extends to all of `L²(μ)`. -/
theorem l2c3_inner_dense {μ : Measure (Torus d)} [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (e : Lp ℝ 2 μ) (M : ℝ)
    (h : ∀ g : C(Torus d, ℝ), |inner ℝ e (ContinuousMap.toLp (E := ℝ) 2 μ ℝ g)| ≤
      M * ‖ContinuousMap.toLp (E := ℝ) 2 μ ℝ g‖) (w : Lp ℝ 2 μ) : |inner ℝ e w| ≤ M * ‖w‖ := by
  have hdense := ContinuousMap.toLp_denseRange (α := Torus d) ℝ μ ℝ (p := 2) (by norm_num)
  exact DenseRange.induction_on (p := fun b : Lp ℝ 2 μ => |inner ℝ e b| ≤ M * ‖b‖) hdense w
    (isClosed_le (continuous_abs.comp (continuous_const.inner continuous_id))
      (continuous_const.mul continuous_norm)) h

/-- The generator perturbation as a form on `L²(μ_β)`: for every class `e` of `𝓛_s f - 𝓛_β f` and every
`w ∈ L²(μ_β)`, `|⟨e, w⟩_{L²(μ_β)}| ≤ C e^{-κ s} ‖∇f‖_{L²(dx)} √Λ ‖w‖_{L²(μ_β)}`. -/
theorem l2c3_pert_Lp (R : Regime d) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ Λ : ℝ, (∀ x, R.ρβ x ≤ Λ) → ∀ s : ℝ, 0 ≤ s → ∀ f : Torus d → ℝ,
      Torus.IsSmooth f → ∀ e : Lp ℝ 2 (withDensityReal R.ρβ),
      ⇑e =ᵐ[withDensityReal R.ρβ]
        (fun x => backwardGenerator R.D (R.ρ s) f x - backwardGenerator R.D R.ρβ f x) →
      ∀ w : Lp ℝ 2 (withDensityReal R.ρβ),
        |inner ℝ e w| ≤ C * Real.exp (-κ * s) * Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2) *
          Real.sqrt Λ * ‖w‖ := by
  obtain ⟨C, κ, hκ, H⟩ := l2c3_pert_cont R
  refine ⟨max C 0, κ, le_max_right _ _, hκ, fun Λ hΛ s hs f hf e he w => ?_⟩
  have hprob : IsProbDensity R.ρβ := R.thermal.1.1
  have hρc : Continuous R.ρβ := l2c3a_cont_of_isCk0 (l2c3a_isCk_of_smooth R.thermal.2.1 0)
  have : IsProbabilityMeasure (withDensityReal R.ρβ) := MFSemigroup.isProb_withDensityReal hprob
  refine l2c3_inner_dense e _ (fun g => ?_) w
  set W : Lp ℝ 2 (withDensityReal R.ρβ) := ContinuousMap.toLp (E := ℝ) 2 (withDensityReal R.ρβ) ℝ g
  have hW : ⇑W =ᵐ[withDensityReal R.ρβ] ⇑g := ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (𝕜 := ℝ) _ g
  set Ef : Torus d → ℝ := fun x => backwardGenerator R.D (R.ρ s) f x - backwardGenerator R.D R.ρβ f x
  have h1 : inner ℝ e W = ∫ x, Ef x * (R.ρβ x * g x) := by
    rw [innerLp_eq_l2Inner, l2Inner_congr_ae he hW, l2Inner_mu hprob]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have h2 : ‖W‖ * ‖W‖ = ∫ x, R.ρβ x * (g x * g x) := by
    rw [← real_inner_self_eq_norm_mul_norm, innerLp_eq_l2Inner, l2Inner_congr_ae hW hW,
      l2Inner_mu hprob]
  have hΛ0 : 0 ≤ Λ := (hprob.nonneg 0).trans (hΛ 0)
  have h3 : PDE.l2NormSq (fun x => R.ρβ x * g x) ≤ Λ * (‖W‖ * ‖W‖) := by
    rw [h2, ← integral_const_mul]
    unfold PDE.l2NormSq
    have hi : ∀ φ : Torus d → ℝ, Continuous φ → Integrable φ := fun φ hφ =>
      hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine integral_mono (hi _ ((hρc.mul g.continuous).pow 2))
      (hi _ (continuous_const.mul (hρc.mul (g.continuous.mul g.continuous)))) fun x => ?_
    have := hprob.nonneg x
    have := hΛ x
    nlinarith [sq_nonneg (g x), mul_nonneg (hprob.nonneg x) (sq_nonneg (g x))]
  have h4 := H s hs f (fun x => R.ρβ x * g x) hf (hρc.mul g.continuous)
  rw [h1]
  refine h4.trans ?_
  have h5 : Real.sqrt (PDE.l2NormSq (fun x => R.ρβ x * g x)) ≤ Real.sqrt Λ * ‖W‖ := by
    refine (Real.sqrt_le_sqrt h3).trans ?_
    rw [Real.sqrt_mul hΛ0, Real.sqrt_mul_self (norm_nonneg _)]
  have hCm : C ≤ max C 0 := le_max_left _ _
  calc _ ≤ max C 0 * Real.exp (-κ * s) * Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2) *
        Real.sqrt (PDE.l2NormSq (fun x => R.ρβ x * g x)) := by gcongr
    _ ≤ max C 0 * Real.exp (-κ * s) * Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2) *
        (Real.sqrt Λ * ‖W‖) := by gcongr
    _ = _ := by ring

end HRS.MC.L2C3
