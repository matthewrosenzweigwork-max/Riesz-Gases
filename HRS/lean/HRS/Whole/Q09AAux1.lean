import HRS.Whole.Adjoint

/-!
# Packet Q09-A, part 1: a plane wave has no `L^p` fractional derivative (Remark S.B.6)

Helper lemmas for `HRS.Whole.planeWave_not_fracLp` (`HRS/Whole/AppendixBEnergy.lean`).  Idea: test the
distributional identity `IsFracDerivRep` against the Schwartz functions `φ_R = 𝓕⁻[θ(R(· - k))]` whose
Fourier transform is concentrated near `k` (away from `0`, so the multiplier `(2π|ξ|)^α` is smooth there):
the pairing of the plane wave with `|∇|^α φ_R` is a fixed nonzero constant, while `‖φ_R‖_{L^q} → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped FourierTransform ENNReal ContDiff

namespace HRS.Whole.Q09A

theorem q09a_cos_pair {d : ℕ} (k : Euc d) (H : SchwartzMap (Euc d) ℂ) :
    ∫ x, (((Real.cos (2 * Real.pi * inner ℝ k x) : ℝ) : ℂ)) * (𝓕⁻ (⇑H)) x = (H k + H (-k)) / 2 := by
  set f : SchwartzMap (Euc d) ℂ := 𝓕⁻ H with hf
  have hfc : (⇑f : Euc d → ℂ) = 𝓕⁻ (⇑H) := SchwartzMap.fourierInv_coe H
  have hFf : 𝓕 (⇑f) = ⇑H := by
    rw [← SchwartzMap.fourier_coe, hf, FourierInvPair.fourier_fourierInv_eq]
  rw [← hfc]
  have hint : Integrable (⇑f : Euc d → ℂ) volume := f.integrable
  have h1 : ∀ x : Euc d, (((Real.cos (2 * Real.pi * inner ℝ k x) : ℝ) : ℂ)) * f x =
      (1/2 : ℂ) * (Real.fourierChar (-inner ℝ x (-k)) • f x + Real.fourierChar (-inner ℝ x k) • f x) := by
    intro x
    rw [Complex.ofReal_cos]
    simp only [Complex.cos, Circle.smul_def, Real.fourierChar_apply, real_inner_comm k x, inner_neg_right]
    push_cast
    ring_nf
  simp_rw [h1]
  have hA : Integrable (fun x : Euc d => Real.fourierChar (-inner ℝ x (-k)) • f x) volume := by
    refine hint.norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul f.continuous).aestronglyMeasurable
    · simp [norm_smul]
  have hB : Integrable (fun x : Euc d => Real.fourierChar (-inner ℝ x k) • f x) volume := by
    refine hint.norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul f.continuous).aestronglyMeasurable
    · simp [norm_smul]
  rw [integral_const_mul, integral_add hA hB]
  have e1 := congrFun hFf (-k)
  have e2 := congrFun hFf k
  rw [Real.fourier_eq] at e1 e2
  rw [e1, e2]
  ring


theorem q09a_fourierInv_scaled {d : ℕ} (θ : Euc d → ℂ) (k : Euc d) {R : ℝ} (hR : 0 < R)
    (x : Euc d) :
    𝓕⁻ (fun ξ : Euc d => θ (R • (ξ - k))) x =
      (((R ^ d)⁻¹ : ℝ) : ℂ) * ((Real.fourierChar (inner ℝ k x) : ℂ) * (𝓕⁻ θ) (R⁻¹ • x)) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  have h1 : ∫ v : Euc d, Real.fourierChar (inner ℝ v x) • θ (R • (v - k)) =
      ∫ y : Euc d, Real.fourierChar (inner ℝ (k + y) x) • θ (R • y) := by
    rw [← integral_add_left_eq_self (μ := volume) (fun v : Euc d => Real.fourierChar (inner ℝ v x) • θ (R • (v - k))) k]
    simp
  rw [h1]
  have h2 : ∀ y : Euc d, Real.fourierChar (inner ℝ (k + y) x) • θ (R • y) =
      (Real.fourierChar (inner ℝ k x) : ℂ) * ((fun u : Euc d => Real.fourierChar (inner ℝ u (R⁻¹ • x)) • θ u) (R • y)) := by
    intro y
    simp only [inner_add_left]
    rw [AddChar.map_add_eq_mul, mul_smul, real_inner_smul_left, real_inner_smul_right,
      ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, Circle.smul_def, Circle.smul_def]
    simp
  simp_rw [h2]
  rw [integral_const_mul, Measure.integral_comp_smul (μ := volume)
    (fun u : Euc d => Real.fourierChar (inner ℝ u (R⁻¹ • x)) • θ u) R]
  simp only [finrank_euclideanSpace_fin]
  rw [abs_of_pos (by positivity), Complex.real_smul]
  ring


/-- the test function localized near the frequency `k` at scale `1/R` -/
theorem q09a_test_fn_aux {d : ℕ} (α : ℝ) (k : Euc d) (hk : k ≠ 0) :
    ∃ (θs : SchwartzMap (Euc d) ℂ), ∀ R : ℝ, 2 / ‖k‖ ≤ R →
      ∃ φ : SchwartzMap (Euc d) ℂ,
        (∀ x, φ x = (((R ^ d)⁻¹ : ℝ) : ℂ) * ((Real.fourierChar (inner ℝ k x) : ℂ) * (𝓕⁻ (⇑θs)) (R⁻¹ • x))) ∧
        ∃ H : SchwartzMap (Euc d) ℂ,
          (⇑H = fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) ∧
          H k = (((2 * Real.pi * ‖k‖) ^ α : ℝ) : ℂ) ∧ H (-k) = 0 := by
  have hk0 : 0 < ‖k‖ := norm_pos_iff.mpr hk
  let θ : ContDiffBump (0 : Euc d) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let θc : Euc d → ℂ := fun u => ((θ u : ℝ) : ℂ)
  have hθc_smooth : ContDiff ℝ ∞ θc := Complex.ofRealCLM.contDiff.comp θ.contDiff
  have hθc_supp : HasCompactSupport θc := θ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  let θs : SchwartzMap (Euc d) ℂ := hθc_supp.toSchwartzMap hθc_smooth
  refine ⟨θs, fun R hR => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hRk : 2 ≤ R * ‖k‖ := by
    have := mul_le_mul_of_nonneg_right hR hk0.le
    rwa [div_mul_cancel₀ _ hk0.ne'] at this
  -- the Fourier-side bump
  let G : Euc d → ℂ := fun ξ => θc (R • (ξ - k))
  have hG_smooth : ContDiff ℝ ∞ G :=
    hθc_smooth.comp ((contDiff_const_smul R).comp (contDiff_id.sub contDiff_const))
  have hG_zero : ∀ ξ : Euc d, 1 / R ≤ ‖ξ - k‖ → G ξ = 0 := by
    intro ξ hξ
    have h1 : 1 ≤ ‖R • (ξ - k)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hRpos.le]
      calc (1 : ℝ) = R * (1 / R) := by field_simp
        _ ≤ R * ‖ξ - k‖ := by gcongr
    have h2 : θ (R • (ξ - k)) = 0 := θ.zero_of_le_dist (by simpa [dist_zero_right] using h1)
    simp [G, θc, h2]
  have hG_supp : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_closedBall k (1 / R)) fun ξ hξ => ?_
    apply hG_zero
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hξ
    exact hξ.le
  let Gs : SchwartzMap (Euc d) ℂ := hG_supp.toSchwartzMap hG_smooth
  have hGs : ⇑Gs = G := rfl
  let φ : SchwartzMap (Euc d) ℂ := 𝓕⁻ Gs
  have hφF : 𝓕 (⇑φ) = G := by
    have h : 𝓕 φ = Gs := FourierInvPair.fourier_fourierInv_eq Gs
    rw [← SchwartzMap.fourier_coe, h]
    rfl
  have hφx : ∀ x, φ x = (((R ^ d)⁻¹ : ℝ) : ℂ) *
      ((Real.fourierChar (inner ℝ k x) : ℂ) * (𝓕⁻ (⇑θs)) (R⁻¹ • x)) := by
    intro x
    have h1 : φ x = 𝓕⁻ (⇑Gs) x := by
      rw [← SchwartzMap.fourierInv_coe]
    rw [h1, hGs]
    exact q09a_fourierInv_scaled θc k hRpos x
  -- the multiplied function
  let m : Euc d → ℂ := fun ξ => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ)
  let Hf : Euc d → ℂ := fun ξ => m ξ * G ξ
  have hH_supp : HasCompactSupport Hf := hG_supp.mul_left
  have hG_near0 : ∀ ξ ∈ Metric.ball (0 : Euc d) (‖k‖ / 2), G ξ = 0 := by
    intro ξ hξ
    apply hG_zero
    rw [Metric.mem_ball, dist_zero_right] at hξ
    have h1 : ‖k‖ - ‖ξ‖ ≤ ‖ξ - k‖ := by
      have := norm_sub_norm_le k ξ
      rwa [norm_sub_rev] at this
    have h2 : 1 / R ≤ ‖k‖ / 2 := by
      rw [div_le_div_iff₀ hRpos (by norm_num)]; linarith
    linarith
  have hH_smooth : ContDiff ℝ ∞ Hf := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have : Hf =ᶠ[nhds (0 : Euc d)] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (by positivity : 0 < ‖k‖ / 2)] with η hη
        simp [Hf, hG_near0 η hη]
      exact (contDiffAt_const).congr_of_eventuallyEq this
    · have hm : ContDiffAt ℝ ∞ m ξ := by
        refine Complex.ofRealCLM.contDiff.contDiffAt.comp ξ ?_
        refine ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul (contDiffAt_norm ℝ hξ)) ?_
        have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
        positivity
      exact hm.mul hG_smooth.contDiffAt
  let H : SchwartzMap (Euc d) ℂ := hH_supp.toSchwartzMap hH_smooth
  refine ⟨φ, hφx, H, ?_, ?_, ?_⟩
  · rw [hφF]; rfl
  · show Hf k = _
    have h0 : θ 0 = 1 := θ.one_of_mem_closedBall (Metric.mem_closedBall_self θ.rIn_pos.le)
    have : G k = 1 := by
      simp [G, θc, h0]
    simp [Hf, this, m]
  · show Hf (-k) = 0
    have : G (-k) = 0 := by
      apply hG_zero
      have h2 : -k - k = -((2 : ℝ) • k) := by rw [two_smul]; abel
      rw [h2, norm_neg, norm_smul, Real.norm_of_nonneg (by norm_num)]
      rw [div_le_iff₀ hRpos]
      nlinarith
    simp [Hf, this]


theorem q09a_test_fn {d : ℕ} (α : ℝ) (k : Euc d) (hk : k ≠ 0) :
    ∃ (θs : SchwartzMap (Euc d) ℂ) (φ H : ℝ → SchwartzMap (Euc d) ℂ), ∀ R : ℝ, 2 / ‖k‖ ≤ R →
        (∀ x, φ R x = (((R ^ d)⁻¹ : ℝ) : ℂ) *
          ((Real.fourierChar (inner ℝ k x) : ℂ) * (𝓕⁻ (⇑θs)) (R⁻¹ • x))) ∧
        (⇑(H R) = fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(φ R)) ξ) ∧
          H R k = (((2 * Real.pi * ‖k‖) ^ α : ℝ) : ℂ) ∧ H R (-k) = 0 := by
  obtain ⟨θs, h⟩ := q09a_test_fn_aux α k hk
  refine ⟨θs, ?_⟩
  have h' : ∀ R : ℝ, ∃ (φ H : SchwartzMap (Euc d) ℂ), 2 / ‖k‖ ≤ R →
      (∀ x, φ x = (((R ^ d)⁻¹ : ℝ) : ℂ) *
        ((Real.fourierChar (inner ℝ k x) : ℂ) * (𝓕⁻ (⇑θs)) (R⁻¹ • x))) ∧
      (⇑H = fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) ∧
        H k = (((2 * Real.pi * ‖k‖) ^ α : ℝ) : ℂ) ∧ H (-k) = 0 := by
    intro R
    by_cases hR : 2 / ‖k‖ ≤ R
    · obtain ⟨φ, h1, H, h2, h3, h4⟩ := h R hR
      exact ⟨φ, H, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, 0, fun h => absurd h hR⟩
  choose φ H hφH using h'
  exact ⟨φ, H, hφH⟩

theorem q09a_lq_scaling {d : ℕ} (g : Euc d → ℂ) {R : ℝ} (hR : 0 < R) (q : ℝ) :
    ∫ x : Euc d, (((R ^ d)⁻¹ : ℝ) * ‖g (R⁻¹ • x)‖) ^ q =
      (((R ^ d)⁻¹ : ℝ) ^ q * R ^ d) * ∫ x : Euc d, ‖g x‖ ^ q := by
  have h1 : ∀ x : Euc d, (((R ^ d)⁻¹ : ℝ) * ‖g (R⁻¹ • x)‖) ^ q =
      ((R ^ d)⁻¹ : ℝ) ^ q * ‖g (R⁻¹ • x)‖ ^ q := fun x =>
    Real.mul_rpow (by positivity) (norm_nonneg _)
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_inv_smul (μ := volume) (fun x : Euc d => ‖g x‖ ^ q) R]
  simp only [finrank_euclideanSpace_fin]
  rw [abs_of_pos (by positivity), smul_eq_mul]
  ring

open Filter Topology in
theorem q09a_small {d : ℕ} (hd : 1 ≤ d) (g : SchwartzMap (Euc d) ℂ) (W : Euc d → ℝ)
    (hW0 : ∀ x, 0 ≤ W x) (p : ℝ) (hp : 1 ≤ p) (hW : MemLp W (ENNReal.ofReal p) volume)
    (φ : ℝ → SchwartzMap (Euc d) ℂ) (R0 : ℝ) (hR0 : 0 < R0)
    (hφ : ∀ R : ℝ, R0 ≤ R → ∀ x, ‖φ R x‖ = ((R ^ d)⁻¹ : ℝ) * ‖g (R⁻¹ • x)‖) :
    Tendsto (fun R : ℝ => ∫ x, W x * ‖φ R x‖) atTop (𝓝 0) := by
  have hnonneg : ∀ R : ℝ, 0 ≤ ∫ x, W x * ‖φ R x‖ :=
    fun R => integral_nonneg fun x => mul_nonneg (hW0 x) (norm_nonneg _)
  have hmeas : ∀ R : ℝ, AEStronglyMeasurable (fun x => W x * ‖φ R x‖) volume := fun R =>
    hW.aestronglyMeasurable.mul (φ R).continuous.norm.aestronglyMeasurable
  have hRpos : ∀ᶠ R : ℝ in atTop, R0 ≤ R := eventually_ge_atTop R0
  have hpow : Tendsto (fun R : ℝ => R ^ d) atTop atTop := tendsto_pow_atTop (by omega)
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · -- p = 1
    subst hp1
    have hWi : Integrable W volume := by
      rw [ENNReal.ofReal_one] at hW
      exact memLp_one_iff_integrable.mp hW
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B :=
      ⟨_, fun x => g.toBoundedContinuousFunction.norm_coe_le_norm x⟩
    have hU : Tendsto (fun R : ℝ => (∫ x, W x) * (((R ^ d)⁻¹ : ℝ) * B)) atTop (𝓝 0) := by
      have := ((tendsto_inv_atTop_zero.comp hpow).mul_const B).const_mul (∫ x, W x)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall hnonneg) ?_ hU
    filter_upwards [hRpos] with R hR0R
    have hR : 0 < R := lt_of_lt_of_le hR0 hR0R
    calc ∫ x, W x * ‖φ R x‖ ≤ ∫ x, W x * (((R ^ d)⁻¹ : ℝ) * B) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
            mul_nonneg (hW0 x) (norm_nonneg _)) (hWi.mul_const _) (Eventually.of_forall fun x => ?_)
          beta_reduce
          rw [hφ R hR0R x]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB _) (by positivity))
            (hW0 x)
      _ = _ := integral_mul_const _ _
  · set q := Real.conjExponent p with hq
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
    have hq1 : 1 < q := hpq.symm.lt
    obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∫ x : Euc d, ‖g x‖ ^ q := ⟨_, rfl⟩
    have hU : Tendsto (fun R : ℝ => (∫ x, W x ^ p) ^ (1 / p) *
        ((((R ^ d)⁻¹ : ℝ) ^ q * R ^ d) * B) ^ (1 / q)) atTop (𝓝 0) := by
      have hkey : ∀ u : ℝ, 0 < u → (u⁻¹) ^ q * u = u ^ (-(q - 1)) := by
        intro u hu
        rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le, ← Real.rpow_add_one hu.ne']
        congr 1; ring
      have ht : Tendsto (fun R : ℝ => ((R ^ d)⁻¹ : ℝ) ^ q * R ^ d) atTop (𝓝 0) := by
        have h1 : Tendsto (fun R : ℝ => (R ^ d) ^ (-(q - 1))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop (by linarith)).comp hpow
        refine h1.congr' ?_
        filter_upwards [hRpos] with R hR0R
        have hR : 0 < R := lt_of_lt_of_le hR0 hR0R
        rw [hkey _ (by positivity)]
      have h2 : Tendsto (fun R : ℝ => ((((R ^ d)⁻¹ : ℝ) ^ q * R ^ d) * B) ^ (1 / q)) atTop (𝓝 0) := by
        have := (ht.mul_const B).rpow_const (p := 1 / q) (Or.inr (by positivity))
        have h0 : (0 : ℝ) ^ q⁻¹ = 0 := Real.zero_rpow (inv_ne_zero (by linarith : (0 : ℝ) < q).ne')
        simpa [h0] using this
      simpa using h2.const_mul ((∫ x, W x ^ p) ^ (1 / p))
    refine squeeze_zero' (Eventually.of_forall hnonneg) ?_ hU
    filter_upwards [hRpos] with R hR0R
    have hR : 0 < R := lt_of_lt_of_le hR0 hR0R
    have hmem : MemLp (fun x => ‖φ R x‖) (ENNReal.ofReal q) volume := ((φ R).memLp _ _).norm
    have := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Eventually.of_forall hW0)
      (Eventually.of_forall fun x => norm_nonneg (φ R x)) hW hmem
    refine this.trans (le_of_eq ?_)
    congr 2
    have e1 : ∀ x : Euc d, ‖φ R x‖ ^ q = (((R ^ d)⁻¹ : ℝ) * ‖g (R⁻¹ • x)‖) ^ q := fun x => by
      rw [hφ R hR0R x]
    simp_rw [e1]
    rw [q09a_lq_scaling g hR q, hBdef]


theorem q09a_integrable_prod {d : ℕ} (W : Euc d → ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hW : MemLp W (ENNReal.ofReal p) volume) (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x => W x * ‖φ x‖) volume := by
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    rw [ENNReal.ofReal_one] at hW
    have hbdd : MemLp (fun x => ‖φ x‖) ∞ volume := ((φ.memLp ∞ volume)).norm
    exact hW.integrable_mul hbdd
  · have hpq := Real.HolderConjugate.conjExponent hp1
    have := hpq.ennrealOfReal
    exact hW.integrable_mul ((φ.memLp (ENNReal.ofReal p.conjExponent) volume).norm)

/-- Remark S.B.6 (core): the distributional identity forces `|∇|^α` of a plane wave to be a nonzero
multiple of a plane wave, which is not in `L^p`, `1 ≤ p < ∞`. -/
theorem q09a_planeWave {d : ℕ} (k e : Euc d) (hk : k ≠ 0) (he : e ≠ 0) (α p : ℝ) (hα : 0 < α)
    (hp : 1 ≤ p) :
    ¬ ∃ w : Euc d → Euc d,
      (∀ i, HRS.Whole.IsFracDerivRep α (fun x => Real.cos (2 * Real.pi * inner ℝ k x) * e i)
        (fun x => w x i)) ∧
      MemLp (fun x => ‖w x‖) (ENNReal.ofReal p) volume := by
  rintro ⟨w, hw, hLp⟩
  have hd : 1 ≤ d := by
    by_contra h
    have : d = 0 := by omega
    subst this
    exact hk (Subsingleton.elim _ _)
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (by ext j; simp [h j])
  obtain ⟨θs, φ, H, hφH⟩ := q09a_test_fn α k hk
  have hk0 : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hR0 : 0 < 2 / ‖k‖ := by positivity
  set g : SchwartzMap (Euc d) ℂ := 𝓕⁻ θs with hgdef
  have hg : (⇑g : Euc d → ℂ) = 𝓕⁻ ⇑θs := SchwartzMap.fourierInv_coe θs
  set c0 : ℝ := (2 * Real.pi * ‖k‖) ^ α with hc0def
  have hc0 : 0 < c0 := Real.rpow_pos_of_pos (by positivity) _
  have hpos : 0 < |e i| * c0 / 2 := by
    have := abs_pos.mpr hi
    positivity
  -- lower bound for the pairing
  have hlow : ∀ R : ℝ, 2 / ‖k‖ ≤ R → |e i| * c0 / 2 ≤ ∫ x, ‖w x‖ * ‖φ R x‖ := by
    intro R hR
    obtain ⟨hφx, hH, hHk, hHk'⟩ := hφH R hR
    obtain ⟨hint1, hint2, hid⟩ := hw i (φ R)
    rw [← hH] at hid
    have hL : ∫ x, (((Real.cos (2 * Real.pi * inner ℝ k x) * e i : ℝ) : ℂ)) *
        𝓕⁻ (⇑(H R)) x = (e i : ℂ) * ((c0 : ℂ) / 2) := by
      have h1 : ∀ x : Euc d, (((Real.cos (2 * Real.pi * inner ℝ k x) * e i : ℝ) : ℂ)) *
          𝓕⁻ (⇑(H R)) x = (e i : ℂ) * ((((Real.cos (2 * Real.pi * inner ℝ k x) : ℝ) : ℂ)) *
          𝓕⁻ (⇑(H R)) x) := fun x => by push_cast; ring
      simp_rw [h1]
      rw [integral_const_mul, q09a_cos_pair k (H R), hHk, hHk']
      simp [c0]
    have hnorm : ‖∫ x, ((w x i : ℝ) : ℂ) * φ R x‖ = |e i| * c0 / 2 := by
      rw [← hid, hL, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg hc0.le]
      simp
      ring
    have hintW : Integrable (fun x => ‖w x‖ * ‖φ R x‖) volume :=
      q09a_integrable_prod (fun x => ‖w x‖) p hp hLp (φ R)
    rw [← hnorm]
    calc ‖∫ x, ((w x i : ℝ) : ℂ) * φ R x‖ ≤ ∫ x, ‖((w x i : ℝ) : ℂ) * φ R x‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖w x‖ * ‖φ R x‖ := by
          refine integral_mono hint2.norm hintW fun x => ?_
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (by simpa using PiLp.norm_apply_le (w x) i)
            (norm_nonneg _)
  -- decay
  have hφnorm : ∀ R : ℝ, 2 / ‖k‖ ≤ R → ∀ x, ‖φ R x‖ = ((R ^ d)⁻¹ : ℝ) * ‖g (R⁻¹ • x)‖ := by
    intro R hR x
    obtain ⟨hφx, -⟩ := hφH R hR
    have hRp : 0 < R := lt_of_lt_of_le hR0 hR
    rw [hφx x, hg, norm_mul, norm_mul, Complex.norm_real, Circle.norm_coe, one_mul,
      Real.norm_of_nonneg (by positivity)]
  have hsmall := q09a_small hd g (fun x => ‖w x‖) (fun x => norm_nonneg _) p hp hLp φ (2 / ‖k‖) hR0
    hφnorm
  obtain ⟨R, hR1, hR2⟩ := ((hsmall.eventually (gt_mem_nhds hpos)).and
    (eventually_ge_atTop (2 / ‖k‖))).exists
  exact absurd (hlow R hR2) (not_le.mpr hR1)

end HRS.Whole.Q09A
