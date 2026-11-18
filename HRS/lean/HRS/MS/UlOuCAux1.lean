import HRS.MS.UlOuS

/-!
# UL-3 (d), part 1 (UlOuCAux1): smoothness, decay and small-time convergence of the OU semigroup on `C_c^\infty`

(docstring: see `UlOuC.lean`.)  Helper lemmas carry the prefix `ul3C_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}

/-- the `i`-th derivative of `x ↦ h (E x + y)` -/
theorem ul3C_iter_comp {k : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ k h) (E : Euc d →L[ℝ] Euc d)
    (y : Euc d) {i : ℕ} (hi : i ≤ k) (x : Euc d) :
    iteratedFDeriv ℝ i (fun x => h (E x + y)) x =
      (iteratedFDeriv ℝ i h (E x + y)).compContinuousLinearMap (fun _ => E) := by
  have h1 : ContDiff ℝ (i : WithTop ℕ∞) (fun z => h (z + y)) :=
    (hh.of_le (by exact_mod_cast hi)).comp (contDiff_id.add contDiff_const)
  have := ContinuousLinearMap.iteratedFDeriv_comp_right E h1 x (i := i) le_rfl
  have e : (fun x => h (E x + y)) = (fun z => h (z + y)) ∘ E := rfl
  rw [e, this, iteratedFDeriv_comp_add_right]

/-- smoothness of the Gaussian average composed with `E`, and the formula for its derivatives -/
theorem ul3C_smooth (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) (k : ℕ) {h : Euc d → ℝ}
    (hh : ContDiff ℝ k h) {M : ℝ} (hM : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) :
    ContDiff ℝ k (ouSg Q ν τ h) ∧ ∀ i ≤ k, ∀ x, iteratedFDeriv ℝ i (ouSg Q ν τ h) x =
      ∫ y, (iteratedFDeriv ℝ i h (ouExp Q τ x + y)).compContinuousLinearMap (fun _ => ouExp Q τ)
        ∂(ouLaw Q ν τ) := by
  set E := ouExp Q τ with hE
  have hG : ∀ y : Euc d, ContDiff ℝ (k : WithTop ℕ∞) (fun x => h (E x + y)) := fun y =>
    hh.comp ((E.contDiff).add contDiff_const)
  have hbd : ∀ i ≤ k, ∀ y x, ‖iteratedFDeriv ℝ i (fun x => h (E x + y)) x‖ ≤
      M * (max 1 ‖E‖) ^ k := by
    intro i hi y x
    rw [ul3C_iter_comp hh E y hi x]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h3 : ∏ _i : Fin i, ‖E‖ ≤ (max 1 ‖E‖) ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc ‖E‖ ^ i ≤ (max 1 ‖E‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i
        _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hi
    exact mul_le_mul (hM i hi _) h3 (by positivity) ((norm_nonneg _).trans (hM i hi 0))
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable
      (fun y => iteratedFDeriv ℝ i (fun x => h (E x + y)) x) (ouLaw Q ν τ) := by
    intro i hi x
    have : (fun y => iteratedFDeriv ℝ i (fun x => h (E x + y)) x) = fun y =>
        (iteratedFDeriv ℝ i h (E x + y)).compContinuousLinearMap (fun _ => E) := by
      funext y; exact ul3C_iter_comp hh E y hi x
    rw [this]
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (iteratedFDeriv ℝ i h) :=
      hh.continuous_iteratedFDeriv (by exact_mod_cast hi)
    exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => E)).continuous.comp
      (h1.comp (continuous_const.add continuous_id))
  obtain ⟨hc, hf⟩ := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := ouLaw Q ν τ) (fun y x => h (E x + y)) k hG
    (Φ := fun _ => M * (max 1 ‖E‖) ^ k) (integrable_const _) hbd hmeas
  refine ⟨hc, fun i hi x => ?_⟩
  rw [show ouSg Q ν τ h = fun x => ∫ w, h (E x + w) ∂(ouLaw Q ν τ) from rfl, hf i hi x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact ul3C_iter_comp hh E y hi x


section Pointwise

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- decay of a Gaussian-type average of a compactly supported function -/
theorem ul3C_decay_int (ψ : Euc d → W) (hψ : Continuous ψ) {R M : ℝ}
    (hR : ∀ z, R < ‖z‖ → ψ z = 0) (hM : ∀ z, ‖ψ z‖ ≤ M) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (hμ : Integrable (fun y : Euc d => ‖y‖) μ) (E : Euc d →L[ℝ] Euc d)
    (x : Euc d) {s : ℝ} (hs : 0 < s) (hxs : R + s ≤ ‖E x‖) :
    ‖∫ y, ψ (E x + y) ∂μ‖ ≤ M / s * ∫ y, ‖y‖ ∂μ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hpt : ∀ y, ‖ψ (E x + y)‖ ≤ M / s * ‖y‖ := by
    intro y
    by_cases h0 : ψ (E x + y) = 0
    · rw [h0, norm_zero]; positivity
    · have h1 : ‖E x + y‖ ≤ R := by
        by_contra hc; exact h0 (hR _ (not_le.1 hc))
      have h2 : s ≤ ‖y‖ := by
        have := norm_sub_norm_le (E x) (-y)
        rw [sub_neg_eq_add, norm_neg] at this
        linarith
      calc ‖ψ (E x + y)‖ ≤ M := hM _
        _ = M / s * s := by field_simp
        _ ≤ M / s * ‖y‖ := by gcongr
  have hint : Integrable (fun y => ψ (E x + y)) μ :=
    Integrable.of_bound (hψ.comp (continuous_const.add continuous_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => hM _)
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  exact integral_mono hint.norm (hμ.const_mul _) hpt

/-- uniform small-time convergence of the averages of a compactly supported function -/
theorem ul3C_conv_int (ψ : Euc d → W) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ r c : ℝ, 0 < r ∧ 0 ≤ c ∧ ∀ (E : Euc d →L[ℝ] Euc d), ‖E - 1‖ ≤ r →
      ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ], Integrable (fun y : Euc d => ‖y‖) μ →
      ∀ x : Euc d, ‖(∫ y, ψ (E x + y) ∂μ) - ψ x‖ ≤ ε + c * ∫ y, ‖y‖ ∂μ := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hRs : ∀ z, max R 0 < ‖z‖ → ψ z = 0 := by
    intro z hz
    by_contra h0
    have := hR (subset_tsupport _ h0)
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R 0]
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖ψ z‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hψ.norm.bddAbove_range_of_hasCompactSupport hc.norm)
    exact ⟨M, fun z => hM ⟨z, rfl⟩⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuous_iff.1 (hc.uniformContinuous_of_continuous hψ) ε hε
  set R0 : ℝ := max R 0 with hR0
  set s : ℝ := δ / 2 with hs
  have hs0 : 0 < s := by positivity
  set R1 : ℝ := 2 * (R0 + s) with hR1
  set r : ℝ := min (1 / 2) (s / (R1 + 1)) with hr
  have hR1pos : 0 < R1 + 1 := by have : 0 ≤ R0 := le_max_right _ _; rw [hR1]; positivity
  have hr0 : 0 < r := lt_min (by norm_num) (by positivity)
  refine ⟨r, 2 * M / s, hr0, by positivity, fun E hE μ _ hμ x => ?_⟩
  have hEx : ∀ z : Euc d, ‖E z - z‖ ≤ r * ‖z‖ := fun z => by
    have := (E - 1).le_opNorm z
    simpa using this.trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
  have hpt : ∀ y : Euc d, ‖ψ (E x + y) - ψ x‖ ≤ ε + 2 * M / s * ‖y‖ := by
    intro y
    by_cases hy : s ≤ ‖y‖
    · have h1 : ‖ψ (E x + y) - ψ x‖ ≤ 2 * M := by
        refine (norm_sub_le _ _).trans ?_; linarith [hM (E x + y), hM x]
      calc _ ≤ 2 * M := h1
        _ = 2 * M / s * s := by field_simp
        _ ≤ ε + 2 * M / s * ‖y‖ := by
          have : 2 * M / s * s ≤ 2 * M / s * ‖y‖ := by gcongr
          linarith
    · rw [not_le] at hy
      by_cases hx : ‖x‖ ≤ R1
      · have h2 : ‖(E x + y) - x‖ < δ := by
          have h3 : ‖(E x + y) - x‖ ≤ ‖E x - x‖ + ‖y‖ := by
            calc _ = ‖(E x - x) + y‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
          have h4 : r * ‖x‖ ≤ s := by
            calc r * ‖x‖ ≤ r * R1 := by gcongr
              _ ≤ s / (R1 + 1) * R1 := by gcongr; exact min_le_right _ _
              _ ≤ s := by
                rw [div_mul_eq_mul_div, div_le_iff₀ hR1pos]; nlinarith
          linarith [hEx x]
        have := hunif (a := E x + y) (b := x) (by rw [dist_eq_norm]; exact h2)
        rw [dist_eq_norm] at this
        have : 0 ≤ 2 * M / s * ‖y‖ := by positivity
        linarith
      · rw [not_le] at hx
        have h5 : ψ x = 0 := hRs x (by have := le_max_left R 0; rw [hR1] at hx; linarith [le_max_right R 0])
        have h6 : ‖E x‖ ≥ ‖x‖ / 2 := by
          have h7 : r ≤ 1 / 2 := min_le_left _ _
          have h10 : ‖x‖ ≤ ‖E x‖ + ‖x - E x‖ := by
            calc ‖x‖ = ‖E x + (x - E x)‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
          have h8 : ‖x - E x‖ ≤ r * ‖x‖ := by rw [norm_sub_rev]; exact hEx x
          nlinarith [mul_le_mul_of_nonneg_right h7 (norm_nonneg x)]
        have h9 : ψ (E x + y) = 0 := by
          apply hRs
          have := norm_sub_norm_le (E x) (-y)
          rw [sub_neg_eq_add, norm_neg] at this
          have : R0 + s ≤ ‖x‖ / 2 := by rw [hR1] at hx; linarith
          linarith
        rw [h5, h9]; simp; positivity
  have hint : Integrable (fun y => ψ (E x + y)) μ :=
    Integrable.of_bound (hψ.comp (continuous_const.add continuous_id)).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y => hM _)
  have e : (∫ y, ψ (E x + y) ∂μ) - ψ x = ∫ y, (ψ (E x + y) - ψ x) ∂μ := by
    rw [integral_sub hint (integrable_const _), integral_const]; simp
  rw [e]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint2 : Integrable (fun y => ε + 2 * M / s * ‖y‖) μ := (integrable_const _).add (hμ.const_mul _)
  refine (integral_mono (hint.sub (integrable_const _)).norm hint2 hpt).trans ?_
  rw [integral_add (integrable_const _) (hμ.const_mul _), integral_const_mul]; simp

end Pointwise


/-- the first moment of `ouLaw τ` is `O(√τ)` -/
theorem ul3C_m1 (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ouLaw Q ν τ) ≤ c * Real.sqrt τ := by
  obtain ⟨lam, Lam, hlam, hLam, hcov⟩ := ouCov_bounds Q hν T
  set Cm : ℝ := ∫ w, ‖w‖ ∂(stdGaussian (Euc d)) with hCm
  have hCm0 : 0 ≤ Cm := integral_nonneg fun w => norm_nonneg _
  refine ⟨Real.sqrt Lam * Cm, by positivity, fun τ hτ => ?_⟩
  set S : Euc d →L[ℝ] Euc d := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ)) with hS
  have hPSD := ouCov_posSemidef Q hν.le hτ.1
  have hSn : ‖S‖ ≤ Real.sqrt (Lam * τ) := by
    refine S.opNorm_le_bound (Real.sqrt_nonneg _) fun ξ => ?_
    have h1 := ul3_S_norm_sq hPSD ξ
    have h2 := (hcov τ hτ ξ).2
    rw [← hS] at h1
    have hLt : 0 ≤ Lam * τ := mul_nonneg hLam.le hτ.1
    have h3 : ‖S ξ‖ ^ 2 ≤ (Real.sqrt (Lam * τ) * ‖ξ‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hLt, h1]; nlinarith [sq_nonneg ‖ξ‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  have hSm : Measurable S := S.continuous.measurable
  rw [ouLaw_eq_map, integral_map hSm.aemeasurable continuous_norm.aestronglyMeasurable]
  have hnorm : Integrable (fun w : Euc d => ‖w‖) (stdGaussian (Euc d)) :=
    (IsGaussian.integrable_id (μ := stdGaussian (Euc d))).norm
  have hi1 : Integrable (fun w => ‖S w‖) (stdGaussian (Euc d)) :=
    Integrable.mono' (hnorm.const_mul ‖S‖) (S.continuous.norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using S.le_opNorm w)
  calc ∫ w, ‖S w‖ ∂(stdGaussian (Euc d)) ≤ ∫ w, ‖S‖ * ‖w‖ ∂(stdGaussian (Euc d)) :=
        integral_mono hi1 (hnorm.const_mul _) fun w => S.le_opNorm w
    _ = ‖S‖ * Cm := by rw [integral_const_mul]
    _ ≤ Real.sqrt (Lam * τ) * Cm := by gcongr
    _ = _ := by rw [Real.sqrt_mul hLam.le]; ring


theorem ul3C_bdd {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (i : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M := by
  have h1 : Continuous (iteratedFDeriv ℝ i h) := hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := h1.norm.bddAbove_range_of_hasCompactSupport (hc.iteratedFDeriv i).norm
  exact ⟨max M 0, le_max_right _ _, fun y => (hM ⟨y, rfl⟩).trans (le_max_left _ _)⟩

theorem ul3C_bdd_upto {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (n : ℕ) :
    ∃ M : ℝ, ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M := by
  choose M hM0 hM using ul3C_bdd hh hc
  exact ⟨∑ i ∈ Finset.range (n + 1), M i, fun i hi y => (hM i y).trans
    (Finset.single_le_sum (f := M) (fun j _ => hM0 j) (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))⟩


/-- the operator `T_E : ψ ↦ ψ ∘ (E,…,E)` depends continuously on `E` -/
theorem ul3C_T_cont (j : ℕ) :
    Continuous fun E : Euc d →L[ℝ] Euc d =>
      ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin j => E) := by
  have := (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin j => Euc d) (fun _ : Fin j => Euc d) ℝ).cont
  exact this.comp (continuous_pi fun _ => continuous_id)

/-- derivatives of `ouSg τ h` converge uniformly to those of `h` as `τ → 0+` -/
theorem ul3C_deriv_close (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {h : Euc d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ τ in 𝓝[≥] (0 : ℝ), ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (ouSg Q ν τ h) x - iteratedFDeriv ℝ j h x‖ ≤ ε := by
  obtain ⟨M, hM⟩ := ul3C_bdd_upto hh hc j
  set ψ := iteratedFDeriv ℝ j h with hψ
  have hψc : Continuous ψ := hh.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hψk : HasCompactSupport ψ := hc.iteratedFDeriv (𝕜 := ℝ) j
  set M0 : ℝ := max M 0 with hM0
  have hψM : ∀ z, ‖ψ z‖ ≤ M0 := fun z => (hM j le_rfl z).trans (le_max_left _ _)
  have hM00 : 0 ≤ M0 := le_max_right _ _
  -- the operator `T_E`
  set T : (Euc d →L[ℝ] Euc d) → (ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) := fun E =>
    ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin j => E) with hT
  have hT1 : T 1 = ContinuousLinearMap.id ℝ _ := by
    ext f x
    simp [hT]
  -- choose the small parameters
  set ε2 : ℝ := min 1 (ε / (4 * (M0 + 1))) with hε2
  have hε20 : 0 < ε2 := lt_min one_pos (by positivity)
  have hTc : Continuous T := ul3C_T_cont (d := d) j
  set ε1 : ℝ := ε / 8 with hε1
  obtain ⟨r, c, hr0, hc0, hconv⟩ := ul3C_conv_int ψ hψc hψk (ε := ε1) (by positivity)
  obtain ⟨cm, hcm0, hm1⟩ := ul3C_m1 Q hν 1
  have hE0 : Tendsto (fun τ : ℝ => ouExp Q τ) (𝓝[≥] 0) (𝓝 (1 : Euc d →L[ℝ] Euc d)) := by
    have := (ul2_exp_cont Q).continuousAt (x := 0)
    have h0 := this.tendsto
    rw [ouExp_zero Q] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun τ : ℝ => c * (cm * Real.sqrt τ)) (𝓝[≥] 0) (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).const_mul cm).const_mul c
    simp only [Real.sqrt_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun τ : ℝ => ‖ouExp Q τ - 1‖) (𝓝[≥] 0) (𝓝 0) := by
    simpa using (hE0.sub_const 1).norm
  have hmaxr : ∀ᶠ τ in 𝓝[≥] (0 : ℝ), ‖ouExp Q τ - 1‖ < r := hnorm.eventually (gt_mem_nhds hr0)
  have hTev : ∀ᶠ τ in 𝓝[≥] (0 : ℝ), ‖T (ouExp Q τ) - T 1‖ < ε2 := by
    have := ((hTc.tendsto 1).comp hE0).eventually_mem (Metric.ball_mem_nhds (T 1) hε20)
    filter_upwards [this] with τ hτ
    have h' : dist (T (ouExp Q τ)) (T 1) < ε2 := Metric.mem_ball.1 hτ
    have h'' : dist (T (ouExp Q τ)) (T 1) = ‖T (ouExp Q τ) - T 1‖ := dist_eq_norm (T (ouExp Q τ)) (T 1)
    rwa [h''] at h'
  have hm1s : ∀ᶠ τ in 𝓝[≥] (0 : ℝ), c * (cm * Real.sqrt τ) < ε / 8 :=
    hsq.eventually (gt_mem_nhds (by positivity))
  have hI : ∀ᶠ τ in 𝓝[≥] (0 : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Icc_mem_nhdsGE one_pos] with τ hτ using hτ
  filter_upwards [hmaxr, hTev, hm1s, hI] with τ h1 hTd h2 h3 x
  set E := ouExp Q τ with hE
  have hEr : ‖E - 1‖ ≤ r := h1.le
  have hm1' : ∫ y, ‖y‖ ∂(ouLaw Q ν τ) ≤ cm * Real.sqrt τ := hm1 τ h3
  have hμ1 : Integrable (fun y : Euc d => ‖y‖) (ouLaw Q ν τ) :=
    (IsGaussian.integrable_id (μ := ouLaw Q ν τ)).norm
  have hcv := hconv E hEr (ouLaw Q ν τ) hμ1 x
  have hint : Integrable (fun y => ψ (E x + y)) (ouLaw Q ν τ) :=
    Integrable.of_bound (hψc.comp (continuous_const.add continuous_id)).aestronglyMeasurable M0
      (Filter.Eventually.of_forall fun y => hψM _)
  have hder := (ul3C_smooth Q ν τ j (hh.of_le (by exact_mod_cast le_top)) (M := M)
    (fun i hi y => hM i hi y)).2 j le_rfl x
  have e : iteratedFDeriv ℝ j (ouSg Q ν τ h) x = T E (∫ y, ψ (E x + y) ∂(ouLaw Q ν τ)) := by
    rw [hder, ← ContinuousLinearMap.integral_comp_comm (T E) hint]; rfl
  rw [e]
  set Ψ := ∫ y, ψ (E x + y) ∂(ouLaw Q ν τ) with hΨ
  have hTE : ‖T E‖ ≤ 2 := by
    have : ‖T 1‖ ≤ 1 := by rw [hT1]; exact ContinuousLinearMap.norm_id_le
    have h5 : ‖T E‖ ≤ ‖T 1‖ + ‖T E - T 1‖ := norm_le_norm_add_norm_sub' (T E) (T 1)
    have : ε2 ≤ 1 := min_le_left _ _
    linarith
  calc ‖T E Ψ - ψ x‖ = ‖T E (Ψ - ψ x) + (T E - T 1) (ψ x)‖ := by
        congr 1
        rw [map_sub, ContinuousLinearMap.sub_apply, hT1]
        simp
    _ ≤ ‖T E‖ * ‖Ψ - ψ x‖ + ‖T E - T 1‖ * ‖ψ x‖ :=
        (norm_add_le _ _).trans (add_le_add ((T E).le_opNorm _) ((T E - T 1).le_opNorm _))
    _ ≤ 2 * (ε1 + c * (cm * Real.sqrt τ)) + ε2 * M0 :=
        add_le_add (mul_le_mul hTE (hcv.trans (by have := mul_le_mul_of_nonneg_left hm1' hc0; linarith))
          (norm_nonneg _) (by norm_num)) (mul_le_mul hTd.le (hψM x) (norm_nonneg _) hε20.le)
    _ ≤ ε := by
        have h6 : ε2 * M0 ≤ ε / 4 := by
          have h7 : ε2 ≤ ε / (4 * (M0 + 1)) := min_le_right _ _
          have h8 : ε / (4 * (M0 + 1)) * M0 ≤ ε / 4 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            have : ε / 4 * (4 * (M0 + 1)) = ε * M0 + ε := by ring
            linarith
          exact (mul_le_mul_of_nonneg_right h7 hM00).trans h8
        linarith


/-- `ouSg` is linear on bounded measurable functions -/
theorem ul3C_sub_lin (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {f g : Euc d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {Bf Bg : ℝ} (hBf : ∀ x, |f x| ≤ Bf) (hBg : ∀ x, |g x| ≤ Bg) :
    ouSg Q ν τ (fun x => f x - g x) = fun x => ouSg Q ν τ f x - ouSg Q ν τ g x := by
  funext x
  have hi : ∀ (u : Euc d → ℝ), Measurable u → ∀ B : ℝ, (∀ x, |u x| ≤ B) →
      Integrable (fun y => u (ouExp Q τ x + y)) (ouLaw Q ν τ) := fun u hu B hB =>
    Integrable.of_bound (hu.comp (measurable_const.add measurable_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB _)
  exact integral_sub (hi f hf Bf hBf) (hi g hg Bg hBg)

theorem ul3C_add_const (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {h : Euc d → ℝ} (hm : Measurable h)
    {B : ℝ} (hB : ∀ x, |h x| ≤ B) (c : ℝ) :
    ouSg Q ν τ (fun x => h x + c) = fun x => ouSg Q ν τ h x + c := by
  funext x
  have hi : Integrable (fun y => h (ouExp Q τ x + y)) (ouLaw Q ν τ) :=
    Integrable.of_bound (hm.comp (measurable_const.add measurable_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB _)
  show ∫ y, (h (ouExp Q τ x + y) + c) ∂(ouLaw Q ν τ) = (∫ y, h (ouExp Q τ x + y) ∂(ouLaw Q ν τ)) + c
  rw [integral_add hi (integrable_const c), integral_const]; simp

theorem ul3C_bdd_of_cb {m : ℕ} {f : Euc d → ℝ} (hf : HRS.MemCb m f) : ∃ B : ℝ, ∀ x, |f x| ≤ B :=
  ⟨HRS.cbNorm m f, fun x => by
    have := ul3_cb_apply hf (Nat.zero_le m) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this⟩

/-- elements of `UlClosure` are bounded continuous (for `d/2 < k`) -/
theorem ul3C_closure_bdd (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (hk : (d : ℝ) / 2 < k)
    {f : Euc d → ℝ} (hf : UlClosure k θ f) :
    Continuous f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B := by
  obtain ⟨C, -, hC⟩ := ulClosure_cb k 0 (by simpa using hk) θ hθ
  exact ⟨hf.1.continuous, ul3C_bdd_of_cb (hC f hf).1⟩

/-- boundedness of `ouSg τ` on `UlClosure` in `ulNormE`, uniformly in `τ ∈ [0,T]` -/
theorem ul3C_ulNorm_bdd (Q : Matrix (Fin d) (Fin d) ℝ) (ν T : ℝ) (k : ℕ) (θ : Euc d → ℝ)
    (hθ : IsUlCutoff θ) (hk : (d : ℝ) / 2 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, UlClosure k θ u →
      ulNormE k θ (ouSg Q ν τ u) ≤ ENNReal.ofReal C * ulNormE k θ u := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨Ca, hCa, ha⟩ := ouSg_ulocNormE_le k χ hχ Q ν T
  refine ⟨Ce * Ca * Ce, by positivity, fun τ hτ u hu => ?_⟩
  obtain ⟨hcont, B, hB⟩ := ul3C_closure_bdd k θ hθ hk hu
  calc ulNormE k θ (ouSg Q ν τ u) ≤ ENNReal.ofReal Ce * ulocNormE k χ (ouSg Q ν τ u) := (hequ _).1
    _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal Ca * ulocNormE k χ u) :=
        mul_le_mul' le_rfl (ha τ hτ u hcont.measurable ⟨B, hB⟩)
    _ ≤ ENNReal.ofReal Ce * (ENNReal.ofReal Ca * (ENNReal.ofReal Ce * ulNormE k θ u)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hequ u).2)
    _ = ENNReal.ofReal (Ce * Ca * Ce) * ulNormE k θ u := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hCe.le, ← ENNReal.ofReal_mul (by positivity)]

end HRS.MS.Ul
