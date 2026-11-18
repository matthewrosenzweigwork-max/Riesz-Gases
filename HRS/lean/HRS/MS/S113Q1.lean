import Mathlib

/-!
# S11.3 Q-regularity (worker S11Q), Q1: the class `C^{1,2}` and Steklov averages in time

`s113q_C12 Q`: `Q : ℝ × E → ℝ` is continuous, has a continuous time derivative `d1` and a continuous spatial derivative `d2`
and second spatial derivative `d3` (partial derivatives only; no mixed time-space derivatives).
`s113q_S η G (t,x) = η⁻¹ ∫_0^η G(t+s,x) ds`: the Steklov average in time.  For `Q` of class `C^{1,2}` the average is jointly `C²`
and its time derivative and spatial derivatives are the averages of `d1, d2, d3`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Interval

namespace HRS.MS.S113Q

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]



/-- Steklov average in the time variable. -/
def s113q_S (η : ℝ) (G : ℝ × E → W) (z : ℝ × E) : W := η⁻¹ • ∫ s in (0 : ℝ)..η, G (z.1 + s, z.2)

theorem s113q_S_continuous [CompleteSpace W] {G : ℝ × E → W} (hG : Continuous G) (η : ℝ) :
    Continuous (s113q_S η G) := by
  unfold s113q_S
  refine Continuous.const_smul ?_ _
  have : Continuous (Function.uncurry fun (z : ℝ × E) (s : ℝ) => G (z.1 + s, z.2)) :=
    hG.comp ((continuous_fst.comp continuous_fst |>.add continuous_snd).prodMk (continuous_snd.comp continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 η

theorem s113q_S_eq [CompleteSpace W] (η : ℝ) (G : ℝ × E → W) (z : ℝ × E) :
    s113q_S η G z = η⁻¹ • ∫ r in z.1..z.1 + η, G (r, z.2) := by
  unfold s113q_S
  rw [intervalIntegral.integral_comp_add_left (fun r => G (r, z.2)) z.1]
  simp

theorem s113q_S_hasDerivAt [CompleteSpace W] {G : ℝ × E → W} (hG : Continuous G) (η : ℝ) (t : ℝ) (x : E) :
    HasDerivAt (fun σ => s113q_S η G (σ, x)) (η⁻¹ • (G (t + η, x) - G (t, x))) t := by
  have hc : Continuous fun r : ℝ => G (r, x) := hG.comp (continuous_id.prodMk continuous_const)
  have h1 : HasDerivAt (fun σ => ∫ r in (0 : ℝ)..σ, G (r, x)) (G (t, x)) t :=
    (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have h2 : HasDerivAt (fun σ => ∫ r in (0 : ℝ)..σ + η, G (r, x)) (G (t + η, x)) t :=
    ((hc.integral_hasStrictDerivAt 0 (t + η)).hasDerivAt).comp_add_const t η
  have h3 := (h2.sub h1).const_smul η⁻¹
  refine h3.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · refine Filter.Eventually.of_forall fun σ => ?_
    simp only [s113q_S_eq, Pi.smul_apply, Pi.sub_apply]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (σ + η))
      (hc.intervalIntegrable 0 σ)).symm
  · rfl


theorem s113q_S_hasFDerivAt [ProperSpace E] [CompleteSpace W] {G : ℝ × E → W} {G2 : ℝ × E → E →L[ℝ] W}
    (hG : Continuous G) (hG2 : Continuous G2)
    (hd : ∀ z : ℝ × E, HasFDerivAt (fun y => G (z.1, y)) (G2 z) z.2) (η t : ℝ) (x : E) :
    HasFDerivAt (fun y => s113q_S η G (t, y)) (s113q_S η G2 (t, x)) x := by
  have hK : IsCompact (uIcc (0 : ℝ) η ×ˢ Metric.closedBall x 1) := isCompact_uIcc.prod (isCompact_closedBall x 1)
  have hcont : Continuous fun p : ℝ × E => G2 (t + p.1, p.2) :=
    hG2.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have key : HasFDerivAt (fun y => ∫ s in (0 : ℝ)..η, G (t + s, y)) (∫ s in (0 : ℝ)..η, G2 (t + s, x)) x := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
      (s := Metric.closedBall x 1) (bound := fun _ => C) (F := fun y s => G (t + s, y))
      (F' := fun y s => G2 (t + s, y)) (Metric.closedBall_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun y =>
        ((hG.comp ((continuous_const.add continuous_id).prodMk continuous_const)).aestronglyMeasurable)
    · exact (hG.comp ((continuous_const.add continuous_id).prodMk continuous_const)).intervalIntegrable _ _
    · exact (hG2.comp ((continuous_const.add continuous_id).prodMk continuous_const)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun s hs y hy => ?_
      have hs' : s ∈ uIcc (0 : ℝ) η := uIoc_subset_uIcc hs
      simpa using hC (s, y) ⟨hs', hy⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s _ y _ => hd (t + s, y)
  unfold s113q_S
  exact key.const_smul η⁻¹



theorem s113q_hasFDerivAt_of_partials {f : ℝ × E → W} {f1 : ℝ × E → W} {f2 : ℝ × E → E →L[ℝ] W}
    (c1 : Continuous f1) (c2 : Continuous f2)
    (h1 : ∀ z : ℝ × E, HasDerivAt (fun σ => f (σ, z.2)) (f1 z) z.1)
    (h2 : ∀ z : ℝ × E, HasFDerivAt (fun y => f (z.1, y)) (f2 z) z.2) (z : ℝ × E) :
    HasFDerivAt f (((1 : ℝ →L[ℝ] ℝ).smulRight (f1 z)).coprod (f2 z)) z := by
  have c1' : Continuous fun v : ℝ × E => (1 : ℝ →L[ℝ] ℝ).smulRight (f1 v) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ W (1 : ℝ →L[ℝ] ℝ)).continuous.comp c1
  have := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := z) (f := fun a b => f (a, b))
    (f₁ := fun a b => (1 : ℝ →L[ℝ] ℝ).smulRight (f1 (a, b))) (f₂ := fun a b => f2 (a, b))
    (Filter.Eventually.of_forall fun v => (h1 v).hasFDerivAt) (Filter.Eventually.of_forall h2)
    c1'.continuousAt c2.continuousAt
  exact this.hasFDerivAt


theorem s113q_coprod_eq (A : ℝ →L[ℝ] W) (B : E →L[ℝ] W) :
    A.coprod B = A.comp (ContinuousLinearMap.fst ℝ ℝ E) + B.comp (ContinuousLinearMap.snd ℝ ℝ E) := by
  refine ContinuousLinearMap.ext fun p => ?_
  simp [ContinuousLinearMap.coprod_apply]

theorem s113q_contDiff_one_of_partials {f : ℝ × E → W} {f1 : ℝ × E → W} {f2 : ℝ × E → E →L[ℝ] W}
    (c1 : Continuous f1) (c2 : Continuous f2)
    (h1 : ∀ z : ℝ × E, HasDerivAt (fun σ => f (σ, z.2)) (f1 z) z.1)
    (h2 : ∀ z : ℝ × E, HasFDerivAt (fun y => f (z.1, y)) (f2 z) z.2) : ContDiff ℝ 1 f := by
  have hc : Continuous fun v : ℝ × E => (1 : ℝ →L[ℝ] ℝ).smulRight (f1 v) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ W (1 : ℝ →L[ℝ] ℝ)).continuous.comp c1
  have hc' : Continuous fun v : ℝ × E => ((1 : ℝ →L[ℝ] ℝ).smulRight (f1 v)).coprod (f2 v) := by
    simp only [s113q_coprod_eq]
    exact (hc.clm_comp continuous_const).add (c2.clm_comp continuous_const)
  have := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0) (f := f)).2
    ⟨fun v => ((1 : ℝ →L[ℝ] ℝ).smulRight (f1 v)).coprod (f2 v), by simpa using hc',
      s113q_hasFDerivAt_of_partials c1 c2 h1 h2⟩
  simpa using this

theorem s113q_contDiff_two_of_partials {f : ℝ × E → W} {f1 : ℝ × E → W} {f2 : ℝ × E → E →L[ℝ] W}
    (c1 : ContDiff ℝ 1 f1) (c2 : ContDiff ℝ 1 f2)
    (h1 : ∀ z : ℝ × E, HasDerivAt (fun σ => f (σ, z.2)) (f1 z) z.1)
    (h2 : ∀ z : ℝ × E, HasFDerivAt (fun y => f (z.1, y)) (f2 z) z.2) : ContDiff ℝ 2 f := by
  have hc : ContDiff ℝ 1 fun v : ℝ × E => (1 : ℝ →L[ℝ] ℝ).smulRight (f1 v) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ W (1 : ℝ →L[ℝ] ℝ)).contDiff.comp c1
  have hc' : ContDiff ℝ 1 fun v : ℝ × E => ((1 : ℝ →L[ℝ] ℝ).smulRight (f1 v)).coprod (f2 v) := by
    simp only [s113q_coprod_eq]
    exact (hc.clm_comp contDiff_const).add (c2.clm_comp contDiff_const)
  have := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1) (f := f)).2
    ⟨fun v => ((1 : ℝ →L[ℝ] ℝ).smulRight (f1 v)).coprod (f2 v), by simpa using hc',
      s113q_hasFDerivAt_of_partials c1.continuous c2.continuous h1 h2⟩
  exact_mod_cast this

/-- Steklov averages of a continuous function converge locally uniformly. -/
theorem s113q_S_tendsto_unif [CompleteSpace W] {G : ℝ × E → W} (hG : Continuous G) {C : Set (ℝ × E)}
    (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ → ∀ z ∈ C, ‖s113q_S η G z - G z‖ ≤ ε := by
  have hC' : IsCompact ((fun p : (ℝ × E) × ℝ => (p.1.1 + p.2, p.1.2)) '' (C ×ˢ Icc (0 : ℝ) 1)) :=
    (hC.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (hC'.uniformContinuousOn_of_continuous hG.continuousOn) ε hε
  refine ⟨min 1 δ, lt_min one_pos hδ, fun η hη hηδ z hz => ?_⟩
  have hη1 : η < 1 := lt_of_lt_of_le hηδ (min_le_left _ _)
  have hηδ' : η < δ := lt_of_lt_of_le hηδ (min_le_right _ _)
  have e : s113q_S η G z - G z = η⁻¹ • ∫ s in (0 : ℝ)..η, (G (z.1 + s, z.2) - G z) := by
    unfold s113q_S
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul,
      inv_mul_cancel₀ hη.ne', one_smul]
    · exact (hG.comp ((continuous_const.add continuous_id).prodMk continuous_const)).intervalIntegrable _ _
    · exact intervalIntegrable_const
  rw [e, norm_smul]
  have hb : ∀ s ∈ Ι (0 : ℝ) η, ‖G (z.1 + s, z.2) - G z‖ ≤ ε := by
    intro s hs
    rw [uIoc_of_le hη.le] at hs
    have hm : (z.1 + s, z.2) ∈ (fun p : (ℝ × E) × ℝ => (p.1.1 + p.2, p.1.2)) '' (C ×ˢ Icc (0 : ℝ) 1) :=
      ⟨(z, s), ⟨hz, hs.1.le, hs.2.trans hη1.le⟩, rfl⟩
    have hz' : z ∈ (fun p : (ℝ × E) × ℝ => (p.1.1 + p.2, p.1.2)) '' (C ×ˢ Icc (0 : ℝ) 1) :=
      ⟨(z, 0), ⟨hz, le_rfl, zero_le_one⟩, by simp⟩
    have := hδ' _ hm _ hz' (by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq, add_sub_cancel_left, abs_of_pos hs.1]
      exact max_lt (hs.2.trans_lt hηδ') hδ)
    rw [← dist_eq_norm]
    exact this.le
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := η) (C := ε)
    (f := fun s => G (z.1 + s, z.2) - G z) hb
  rw [sub_zero, abs_of_pos hη] at hI
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos hη]
  calc η⁻¹ * ‖∫ s in (0 : ℝ)..η, (G (z.1 + s, z.2) - G z)‖ ≤ η⁻¹ * (ε * η) := by gcongr
    _ = ε := by field_simp

/-- The time difference quotient. -/
def s113q_D (η : ℝ) (G : ℝ × E → W) (z : ℝ × E) : W := η⁻¹ • (G (z.1 + η, z.2) - G z)

theorem s113q_D_continuous {G : ℝ × E → W} (hG : Continuous G) (η : ℝ) : Continuous (s113q_D η G) := by
  unfold s113q_D
  exact Continuous.const_smul ((hG.comp ((continuous_fst.add continuous_const).prodMk continuous_snd)).sub hG) _

/-- Fundamental theorem of calculus for the average of the time derivative. -/
theorem s113q_S_deriv_eq [CompleteSpace W] {G : ℝ × E → W} {G1 : ℝ × E → W} (hG1 : Continuous G1)
    (h1 : ∀ z : ℝ × E, HasDerivAt (fun σ => G (σ, z.2)) (G1 z) z.1) (η : ℝ) (z : ℝ × E) :
    s113q_S η G1 z = s113q_D η G z := by
  unfold s113q_S s113q_D
  congr 1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := η)
    (f := fun s => G (z.1 + s, z.2)) (f' := fun s => G1 (z.1 + s, z.2))
    (fun s _ => (h1 (z.1 + s, z.2)).comp_const_add z.1 s)
    ((hG1.comp ((continuous_const.add continuous_id).prodMk continuous_const)).intervalIntegrable _ _)
  simpa using this

structure s113q_C12Data (Q : ℝ × E → ℝ) (d1 : ℝ × E → ℝ) (d2 : ℝ × E → E →L[ℝ] ℝ)
    (d3 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) : Prop where
  cQ : Continuous Q
  c1 : Continuous d1
  c2 : Continuous d2
  c3 : Continuous d3
  h1 : ∀ z : ℝ × E, HasDerivAt (fun σ => Q (σ, z.2)) (d1 z) z.1
  h2 : ∀ z : ℝ × E, HasFDerivAt (fun y => Q (z.1, y)) (d2 z) z.2
  h3 : ∀ z : ℝ × E, HasFDerivAt (fun y => d2 (z.1, y)) (d3 z) z.2

/-- The class `C^{1,2}`: continuous time derivative, continuous first and second spatial derivatives. -/
def s113q_C12 (Q : ℝ × E → ℝ) : Prop :=
  ∃ (d1 : ℝ × E → ℝ) (d2 : ℝ × E → E →L[ℝ] ℝ) (d3 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ), s113q_C12Data Q d1 d2 d3

theorem s113q_C12Data.steklov [ProperSpace E] {Q : ℝ × E → ℝ} {d1 : ℝ × E → ℝ} {d2 : ℝ × E → E →L[ℝ] ℝ}
    {d3 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} (h : s113q_C12Data Q d1 d2 d3) (η : ℝ) :
    ContDiff ℝ 2 (s113q_S η Q) ∧
    (∀ z : ℝ × E, HasDerivAt (fun σ => s113q_S η Q (σ, z.2)) (s113q_S η d1 z) z.1) ∧
    (∀ z : ℝ × E, HasFDerivAt (fun y => s113q_S η Q (z.1, y)) (s113q_S η d2 z) z.2) ∧
    (∀ z : ℝ × E, HasFDerivAt (fun y => s113q_S η d2 (z.1, y)) (s113q_S η d3 z) z.2) := by
  have hS1 : ∀ z : ℝ × E, HasDerivAt (fun σ => s113q_S η Q (σ, z.2)) (s113q_S η d1 z) z.1 := fun z => by
    rw [s113q_S_deriv_eq h.c1 h.h1]
    exact s113q_S_hasDerivAt h.cQ η z.1 z.2
  have hS2 : ∀ z : ℝ × E, HasFDerivAt (fun y => s113q_S η Q (z.1, y)) (s113q_S η d2 z) z.2 := fun z =>
    s113q_S_hasFDerivAt h.cQ h.c2 h.h2 η z.1 z.2
  have hS3 : ∀ z : ℝ × E, HasFDerivAt (fun y => s113q_S η d2 (z.1, y)) (s113q_S η d3 z) z.2 := fun z =>
    s113q_S_hasFDerivAt h.c2 h.c3 h.h3 η z.1 z.2
  refine ⟨?_, hS1, hS2, hS3⟩
  have e1 : s113q_S η d1 = s113q_D η Q := funext fun z => s113q_S_deriv_eq h.c1 h.h1 η z
  -- the time derivative `f1 = η⁻¹ (Q(t+η) - Q(t))` is `C¹`
  have cf1 : ContDiff ℝ 1 (s113q_S η d1) := by
    rw [e1]
    refine s113q_contDiff_one_of_partials (f1 := fun z => η⁻¹ • (d1 (z.1 + η, z.2) - d1 z))
      (f2 := fun z => η⁻¹ • (d2 (z.1 + η, z.2) - d2 z)) ?_ ?_ ?_ ?_
    · exact s113q_D_continuous h.c1 η
    · exact s113q_D_continuous h.c2 η
    · intro z
      have h1' : HasDerivAt (fun σ => Q (σ + η, z.2)) (d1 (z.1 + η, z.2)) z.1 :=
        (h.h1 (z.1 + η, z.2)).comp_add_const z.1 η
      exact (h1'.sub (h.h1 z)).const_smul η⁻¹
    · intro z
      have h2' : HasFDerivAt (fun y => Q (z.1 + η, y)) (d2 (z.1 + η, z.2)) z.2 := h.h2 (z.1 + η, z.2)
      exact (h2'.sub (h.h2 z)).const_smul η⁻¹
  have cf2 : ContDiff ℝ 1 (s113q_S η d2) := by
    refine s113q_contDiff_one_of_partials (f1 := fun z => η⁻¹ • (d2 (z.1 + η, z.2) - d2 z))
      (f2 := s113q_S η d3) ?_ (s113q_S_continuous h.c3 η) ?_ hS3
    · exact s113q_D_continuous h.c2 η
    · intro z
      have := s113q_S_hasDerivAt h.c2 η z.1 z.2
      simpa [s113q_D] using this
  exact s113q_contDiff_two_of_partials cf1 cf2 hS1 hS2


/-- The Steklov step `1/(k+2)`. -/
def s113q_eta (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

theorem s113q_eta_pos (k : ℕ) : 0 < s113q_eta k := by unfold s113q_eta; positivity

theorem s113q_eta_le_one (k : ℕ) : s113q_eta k ≤ 1 := by
  unfold s113q_eta
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem s113q_eta_tendsto : Tendsto s113q_eta atTop (𝓝 0) := by
  unfold s113q_eta
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  refine this.congr fun k => ?_
  simp only [Function.comp]
  push_cast
  ring_nf

/-- pointwise convergence of the Steklov averages along the steps `1/(k+2)`. -/
theorem s113q_S_tendsto_pt [CompleteSpace W] {G : ℝ × E → W} (hG : Continuous G) (z : ℝ × E) :
    Tendsto (fun k : ℕ => s113q_S (s113q_eta k) G z) atTop (𝓝 (G z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η₀, hη₀, h⟩ := s113q_S_tendsto_unif hG (isCompact_singleton (x := z)) (ε / 2) (half_pos hε)
  have hlt : ∀ᶠ k in atTop, s113q_eta k < η₀ := s113q_eta_tendsto.eventually (gt_mem_nhds hη₀)
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hlt
  refine ⟨k0, fun k hk => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (h _ (s113q_eta_pos k) (hk0 k hk) z rfl) (half_lt_self hε)

/-- uniform convergence along the steps `1/(k+2)` on a compact set. -/
theorem s113q_S_tendsto_unif' [CompleteSpace W] {G : ℝ × E → W} (hG : Continuous G) {C : Set (ℝ × E)}
    (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ z ∈ C, ‖s113q_S (s113q_eta k) G z - G z‖ ≤ ε := by
  obtain ⟨η₀, hη₀, h⟩ := s113q_S_tendsto_unif hG hC ε hε
  have hlt : ∀ᶠ k in atTop, s113q_eta k < η₀ := s113q_eta_tendsto.eventually (gt_mem_nhds hη₀)
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 hlt
  exact ⟨k0, fun k hk z hz => h _ (s113q_eta_pos k) (hk0 k hk) z hz⟩

theorem s113q_S_pos {Q : ℝ × E → ℝ} (hQ : Continuous Q) {T η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) (T + 1), ∀ x, 0 < Q (t, x)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : E) :
    0 < s113q_S η Q (t, x) := by
  unfold s113q_S
  refine smul_pos (inv_pos.2 hη0) ?_
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun s hs => ?_) hη0
  · exact (hQ.comp ((continuous_const.add continuous_id).prodMk continuous_const)).intervalIntegrable _ _
  · exact hpos _ ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩ x

theorem s113q_C12Data.steklov_data [ProperSpace E] {Q : ℝ × E → ℝ} {d1 : ℝ × E → ℝ} {d2 : ℝ × E → E →L[ℝ] ℝ}
    {d3 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} (h : s113q_C12Data Q d1 d2 d3) (η : ℝ) :
    s113q_C12Data (s113q_S η Q) (s113q_S η d1) (s113q_S η d2) (s113q_S η d3) :=
  ⟨s113q_S_continuous h.cQ η, s113q_S_continuous h.c1 η, s113q_S_continuous h.c2 η, s113q_S_continuous h.c3 η,
    (h.steklov η).2.1, (h.steklov η).2.2.1, (h.steklov η).2.2.2⟩

end HRS.MS.S113Q

end
