import HRS.MC.CepE6DCut

/-!
# Packet CEPE6D, part 3a: the weak-limit lemma W, first half

`b_n : ℝ → ℝ^N` continuous, `a_n(t) = ∫_0^t b_n`, `∫ f da_n := ∫_0^T ⟨f, b_n⟩ ds`.  Here: bounds, integration by parts
for `C¹` test functions, convergence of `∫_0^T ⟨f, b_n⟩` for `C¹` `f` when `a_n → A` uniformly, and polynomial density.
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

variable {N : ℕ}

/-- `∫ f da` for the absolutely continuous path `a(t) = ∫_0^t b`. -/
def Lfun (T : ℝ) (b f : ℝ → Ch6D N) : ℝ := ∫ s in (0 : ℝ)..T, ⟪f s, b s⟫

/-- The primitive `a(t) = ∫_0^t b`. -/
def prim (b : ℝ → Ch6D N) (t : ℝ) : Ch6D N := ∫ s in (0 : ℝ)..t, b s

theorem abs_integral_le_of_le {T : ℝ} (hT : 0 ≤ T) {φ h : ℝ → ℝ}
    (hh : ContinuousOn h (Icc 0 T)) (hle : ∀ s ∈ Icc 0 T, |φ s| ≤ h s) :
    |∫ s in (0 : ℝ)..T, φ s| ≤ ∫ s in (0 : ℝ)..T, h s := by
  have := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) (f := φ) (g := h) hT
    (Filter.Eventually.of_forall fun s hs => by
      simpa [Real.norm_eq_abs] using hle s ⟨hs.1.le, hs.2⟩)
    (hh.intervalIntegrable_of_Icc hT)
  simpa [Real.norm_eq_abs] using this

theorem continuousOn_inner' {T : ℝ} {f g : ℝ → Ch6D N} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) : ContinuousOn (fun s => ⟪f s, g s⟫) (Icc 0 T) :=
  hf.inner hg

theorem integrable_inner {T : ℝ} (hT : 0 ≤ T) {f g : ℝ → Ch6D N} (hf : ContinuousOn f (Icc 0 T))
    (hg : ContinuousOn g (Icc 0 T)) :
    IntervalIntegrable (fun s => ⟪f s, g s⟫) MeasureTheory.volume 0 T :=
  (continuousOn_inner' hf hg).intervalIntegrable_of_Icc hT

/-- `|∫ ⟨f, b⟩| ≤ M ∫ ‖b‖` when `‖f‖ ≤ M` on `[0,T]`. -/
theorem abs_Lfun_le {T : ℝ} (hT : 0 ≤ T) {b f : ℝ → Ch6D N} (hb : ContinuousOn b (Icc 0 T)) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 T, ‖f s‖ ≤ M) :
    |Lfun T b f| ≤ M * ∫ s in (0 : ℝ)..T, ‖b s‖ := by
  have hbn : ContinuousOn (fun s => ‖b s‖) (Icc 0 T) := hb.norm
  have := abs_integral_le_of_le hT (φ := fun s => ⟪f s, b s⟫) (h := fun s => M * ‖b s‖)
    (hbn.const_smul M |>.congr fun s _ => by simp) fun s hs => by
      calc |⟪f s, b s⟫| ≤ ‖f s‖ * ‖b s‖ := by
            simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (f s) (b s)
        _ ≤ M * ‖b s‖ := mul_le_mul_of_nonneg_right (hM s hs) (norm_nonneg _)
  rw [intervalIntegral.integral_const_mul] at this
  exact this

theorem Lfun_sub {T : ℝ} (hT : 0 ≤ T) {b f g : ℝ → Ch6D N} (hb : ContinuousOn b (Icc 0 T))
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T)) :
    Lfun T b (fun s => f s - g s) = Lfun T b f - Lfun T b g := by
  unfold Lfun
  rw [← intervalIntegral.integral_sub (integrable_inner hT hf hb) (integrable_inner hT hg hb)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp [inner_sub_left]

/-- Integration by parts for `C¹` test functions. -/
theorem Lfun_ibp {T : ℝ} (hT : 0 ≤ T) {b : ℝ → Ch6D N} (hb : Continuous b) {f : ℝ → Ch6D N}
    (hf : ContDiff ℝ 1 f) :
    Lfun T b f = ⟪f T, prim b T⟫ - ∫ s in (0 : ℝ)..T, ⟪deriv f s, prim b s⟫ := by
  have ha : ∀ s, HasDerivAt (prim b) (b s) s := fun s =>
    (hb.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hfd : ∀ s, HasDerivAt f (deriv f s) s := fun s =>
    ((hf.differentiable (by simp)) s).hasDerivAt
  have hφ : ∀ s, HasDerivAt (fun s => ⟪f s, prim b s⟫) (⟪f s, b s⟫ + ⟪deriv f s, prim b s⟫) s :=
    fun s => (hfd s).inner ℝ (ha s)
  have hpc : Continuous (prim b) := continuous_iff_continuousAt.2 fun s => (ha s).continuousAt
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hint1 : IntervalIntegrable (fun s => ⟪f s, b s⟫) MeasureTheory.volume 0 T :=
    (hf.continuous.inner hb).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun s => ⟪deriv f s, prim b s⟫) MeasureTheory.volume 0 T :=
    (hdc.inner hpc).intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφ s) (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at key
  have h0 : prim b 0 = 0 := by simp [prim]
  simp only [h0, inner_zero_right, sub_zero] at key
  unfold Lfun
  linarith

/-- Uniform convergence of the second factor passes to the integral. -/
theorem tendsto_integral_inner {T : ℝ} (hT : 0 ≤ T) {g : ℝ → Ch6D N} (hg : ContinuousOn g (Icc 0 T))
    {c : ℕ → ℝ → Ch6D N} {C : ℝ → Ch6D N} (hc : ∀ n, ContinuousOn (c n) (Icc 0 T))
    (hC : ContinuousOn C (Icc 0 T)) (hu : TendstoUniformlyOn c C atTop (Icc 0 T)) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..T, ⟪g s, c n s⟫) atTop (𝓝 (∫ s in (0 : ℝ)..T, ⟪g s, C s⟫)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := by
    by_contra h
    push Not at h
    have := hM 0 ⟨le_rfl, hT⟩
    linarith [norm_nonneg (g 0)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / ((M + 1) * (T + 1)) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu _ hδ] with n hn
  rw [Real.dist_eq]
  have h1 : (∫ s in (0 : ℝ)..T, ⟪g s, c n s⟫) - ∫ s in (0 : ℝ)..T, ⟪g s, C s⟫ =
      ∫ s in (0 : ℝ)..T, ⟪g s, c n s - C s⟫ := by
    rw [← intervalIntegral.integral_sub (integrable_inner hT hg (hc n)) (integrable_inner hT hg hC)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [inner_sub_right]
  rw [h1]
  have hb : ∀ s ∈ Icc (0 : ℝ) T, |⟪g s, c n s - C s⟫| ≤ M * (ε / ((M + 1) * (T + 1))) := by
    intro s hs
    calc |⟪g s, c n s - C s⟫| ≤ ‖g s‖ * ‖c n s - C s‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (g s) (c n s - C s)
      _ ≤ M * (ε / ((M + 1) * (T + 1))) := by
          refine mul_le_mul (hM s hs) ?_ (norm_nonneg _) hM0
          rw [← dist_eq_norm, dist_comm]; exact (hn s hs).le
  have := abs_integral_le_of_le hT (φ := fun s => ⟪g s, c n s - C s⟫)
    (h := fun _ => M * (ε / ((M + 1) * (T + 1)))) continuousOn_const hb
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
  refine lt_of_le_of_lt this ?_
  have hMT : T * (M * (ε / ((M + 1) * (T + 1)))) = ε * (M * T / ((M + 1) * (T + 1))) := by
    field_simp
  rw [hMT]
  have : M * T / ((M + 1) * (T + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  nlinarith

/-- For `C¹` test functions `∫_0^T ⟨f, b_n⟩ → ⟨f(T), A(T)⟩ - ∫_0^T ⟨f', A⟩`. -/
theorem tendsto_Lfun_C1 {T : ℝ} (hT : 0 ≤ T) {b : ℕ → ℝ → Ch6D N} (hb : ∀ n, Continuous (b n))
    {A : ℝ → Ch6D N} (hA : TendstoUniformlyOn (fun n => prim (b n)) A atTop (Icc 0 T))
    {f : ℝ → Ch6D N} (hf : ContDiff ℝ 1 f) :
    Tendsto (fun n => Lfun T (b n) f) atTop
      (𝓝 (⟪f T, A T⟫ - ∫ s in (0 : ℝ)..T, ⟪deriv f s, A s⟫)) := by
  have hpc : ∀ n, Continuous (prim (b n)) := fun n =>
    continuous_iff_continuousAt.2 fun s => ((hb n).integral_hasStrictDerivAt 0 s).hasDerivAt.continuousAt
  have hAc : ContinuousOn A (Icc 0 T) :=
    hA.continuousOn (Filter.Eventually.of_forall fun n => (hpc n).continuousOn).frequently
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have h1 : Tendsto (fun n => ⟪f T, prim (b n) T⟫) atTop (𝓝 ⟪f T, A T⟫) := by
    have := hA.tendsto_at (x := T) ⟨hT, le_rfl⟩
    exact (tendsto_const_nhds.inner this)
  have h2 := tendsto_integral_inner hT hdc.continuousOn (fun n => (hpc n).continuousOn) hAc hA
  have := h1.sub h2
  refine this.congr fun n => ?_
  rw [Lfun_ibp hT (hb n) hf]

/-- `‖x‖ ≤ ∑ |x_j|` in `ℝ^N`. -/
theorem norm_le_sum_abs (x : Ch6D N) : ‖x‖ ≤ ∑ j : Fin N, |x j| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j : Fin N => |x j|)
    (fun j _ => abs_nonneg _)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- Polynomial (hence smooth) approximation of a continuous `ℝ^N`-valued function on `[0,T]`. -/
theorem exists_smooth_approx {T : ℝ} {f : ℝ → Ch6D N} (hf : ContinuousOn f (Icc 0 T)) {η : ℝ}
    (hη : 0 < η) : ∃ g : ℝ → Ch6D N, ContDiff ℝ ∞ g ∧ ∀ s ∈ Icc 0 T, ‖f s - g s‖ ≤ η := by
  have hη' : 0 < η / (N + 1) := by positivity
  have hcoord : ∀ j : Fin N, ∃ p : Polynomial ℝ, ∀ s ∈ Icc 0 T, |f s j - p.eval s| ≤ η / (N + 1) := by
    intro j
    let fj : C(Icc (0 : ℝ) T, ℝ) :=
      ⟨fun x => f x.1 j, (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hf.restrict⟩
    obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 T fj _ hη'
    refine ⟨p, fun s hs => ?_⟩
    have h1 := ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn (Icc 0 T) - fj) ⟨s, hs⟩
    simp only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
      Real.norm_eq_abs] at h1
    have h2 : |p.eval s - f s j| < η / (N + 1) := lt_of_le_of_lt h1 hp
    rw [abs_sub_comm]; exact h2.le
  choose p hp using hcoord
  refine ⟨fun s => ∑ j : Fin N, (p j).eval s • EuclideanSpace.single j (1 : ℝ), ?_, fun s hs => ?_⟩
  · refine ContDiff.sum fun j _ => ?_
    have h1 : ContDiff ℝ ∞ (fun x : ℝ => (p j).eval x) := by
      simpa [Polynomial.coe_aeval_eq_eval] using Polynomial.contDiff_aeval (𝕜 := ℝ) (p j) ∞
    exact h1.smul contDiff_const
  · refine (norm_le_sum_abs _).trans ?_
    have : ∀ j : Fin N, |(f s - ∑ j : Fin N, (p j).eval s • EuclideanSpace.single j (1 : ℝ)) j| ≤
        η / (N + 1) := by
      intro j
      have e : (f s - ∑ j : Fin N, (p j).eval s • EuclideanSpace.single j (1 : ℝ)) j =
          f s j - (p j).eval s := by
        simp [PiLp.sub_apply, Pi.single_apply]
      rw [e]; exact hp j s hs
    calc _ ≤ ∑ _j : Fin N, η / (N + 1) := Finset.sum_le_sum fun j _ => this j
      _ = N * (η / (N + 1)) := by simp
      _ ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

end HRS.MC.CepE6D
