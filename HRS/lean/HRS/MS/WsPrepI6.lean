import HRS.MS.WsPrepI5

/-!
# S21T packet 6: the i.i.d. preparation (`β₀ = 0`): ingredients

For the independent preparation `ℚ_{N,0}(μ₀) = (μ₀)^{⊗N}` the window feature vector is `featureVec φ μ₀ X = N^{-1/2} ∑ Y(x_i)` with
`Y(x) = (φ_j(x) - μ₀(φ_j))_j ∈ ℓ²` (`s21iY`), bounded by `2S`, centred.  Nothing beyond boundedness of the window tests in `C_b^{4d+42}`
and the product decay of their norms is used: the finite-rank `ℓ²` projection (rank `≲ Q²`, tails `Q^{-3/4}`) replaces the quantization
of the supplement, and gives the better exponent `N^{-3/34}` (`s21i_rate`).

* `s21iY`, `s21iY_coord`, `s21iY_norm`, `s21iY_meas`, `s21iY_mean`, `s21i_featureVec_eq`;
* `s21i_inner_vec_Y`, `s21i_gauss_iid`, `s21i_fdd0`: the Gaussian of the bridge covariance and its finite-dimensional laws;
* `s21i_tail`, `s21i_iid_linear`, `s21i_rate`: tails, particle variance, exponent algebra.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

theorem s21i_reindex {T : ℝ} (hT : 0 < T) (σ : ℕ ≃ ℕ × MultiIndex d) (t : ℝ) (α : MultiIndex d)
    (a : ℕ × MultiIndex d → ℝ) {v : ℝ}
    (h : HasSum (fun n : ℕ => s11p_kap n * r2CosBasis T n t * a (n, α)) v) :
    HasSum (fun j : ℕ => SeqL2.coord (s21gVec σ hT t α) j * a (σ j)) v := by
  classical
  set g : ℕ → ℕ := fun n => σ.symm (n, α) with hg
  have hginj : Function.Injective g := fun a b hab => by
    have := σ.symm.injective hab
    simpa using this
  set F : ℕ → ℝ := fun j => SeqL2.coord (s21gVec σ hT t α) j * a (σ j) with hF
  have hz : ∀ j ∉ Set.range g, F j = 0 := by
    intro j hj
    simp only [hF, s21gVec_coord]
    by_cases hα : (σ j).2 = α
    · exfalso
      apply hj
      refine ⟨(σ j).1, ?_⟩
      simp only [hg]
      have : ((σ j).1, α) = σ j := Prod.ext rfl hα.symm
      rw [this, Equiv.symm_apply_apply]
    · simp [hα]
  rw [← hginj.hasSum_iff hz]
  convert h using 1
  funext n
  simp only [Function.comp_apply, hF, hg, s21gVec_coord, Equiv.apply_symm_apply, ite_true]

theorem s21i_coord_sum {ι : Type*} (s : Finset ι) (f : ι → SeqL2) (j : ℕ) :
    SeqL2.coord (∑ i ∈ s, f i) j = ∑ i ∈ s, SeqL2.coord (f i) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [s21h_coord_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, s21h_coord_add, ih]

/-- The single-sample centred feature vector `Y(x) = (φ_j(x) - μ₀ φ_j)_j` (the case `N = 1` of `featureVec`). -/
def s21iY (φ : ℕ → Euc d → ℝ) (μ0 : Measure (Euc d)) (x : Euc d) : SeqL2 :=
  featureVec φ μ0 (fun _ : Fin 1 => x)

theorem s21iY_coord {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] (x : Euc d) (j : ℕ) :
    SeqL2.coord (s21iY φ μ0 x) j = φ j x - HRS.Whole.pair μ0 (φ j) := by
  unfold s21iY featureVec
  rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp (le_refl 1) hφ _)]
  rw [HRS.Whole.pair_empirical (by norm_num)]
  simp

theorem s21iY_norm {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] (x : Euc d) : ‖s21iY φ μ0 x‖ ≤ 2 * featureSum J φ := by
  have := S45.s45_featureVec_norm_le (N := 1) (le_refl 1) hφ (ν := μ0) (fun _ : Fin 1 => x)
  simpa [s21iY] using this

theorem s21iY_meas {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] : Measurable (s21iY φ μ0) :=
  (S45.s45_feature_measurable (N := 1) (le_refl 1) hφ).comp (Measurable.of_eval fun _ => measurable_id)

theorem s21iY_mean {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] : ∫ x, s21iY φ μ0 x ∂μ0 = 0 := by
  have hint : Integrable (s21iY φ μ0) μ0 :=
    Integrable.of_bound (s21iY_meas hφ μ0).aestronglyMeasurable (2 * featureSum J φ)
      (ae_of_all _ fun x => s21iY_norm hφ μ0 x)
  refine lp.ext (funext fun k => ?_)
  show SeqL2.coord (∫ x, s21iY φ μ0 x ∂μ0) k = SeqL2.coord 0 k
  rw [← s21h_inner_single, ← integral_inner hint (s21hSingle k)]
  simp_rw [s21h_inner_single, s21iY_coord hφ]
  have hφi : Integrable (φ k) μ0 :=
    Integrable.of_bound (hφ.1 k).1.continuous.aestronglyMeasurable (cbNorm J (φ k))
      (ae_of_all _ fun x => HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x)
  rw [integral_sub hφi (integrable_const _)]
  simp [HRS.Whole.pair, s21h_coord_zero]

theorem s21i_featureVec_eq {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] {N : ℕ} (hN : 1 ≤ N) (X : EucConfig d N) :
    featureVec φ μ0 X = (Real.sqrt N)⁻¹ • ∑ i, s21iY φ μ0 (X i) := by
  refine lp.ext (funext fun j => ?_)
  show SeqL2.coord (featureVec φ μ0 X) j = SeqL2.coord ((Real.sqrt N)⁻¹ • ∑ i, s21iY φ μ0 (X i)) j
  rw [s21h_coord_smul, s21i_coord_sum]
  simp_rw [s21iY_coord hφ]
  unfold featureVec
  rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN hφ X), HRS.Whole.pair_empirical (by omega),
    Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have e1 : Real.sqrt N * (N : ℝ)⁻¹ = (Real.sqrt N)⁻¹ := by
    calc Real.sqrt N * (N : ℝ)⁻¹ = Real.sqrt N * (Real.sqrt N * Real.sqrt N)⁻¹ := by
          rw [Real.mul_self_sqrt hN0.le]
      _ = (Real.sqrt N)⁻¹ := by field_simp
  have e2 : (Real.sqrt N)⁻¹ * (N : ℝ) = Real.sqrt N := by
    calc (Real.sqrt N)⁻¹ * (N : ℝ) = (Real.sqrt N)⁻¹ * (Real.sqrt N * Real.sqrt N) := by
          rw [Real.mul_self_sqrt hN0.le]
      _ = Real.sqrt N := by field_simp
  linear_combination (∑ i, φ j (X i)) * e1 + HRS.Whole.pair μ0 (φ j) * e2

theorem s21i_inner_vec_Y {D : S11pData d} {U : MultiIndex d → ℝ → Euc d → ℝ} {T : ℝ} (hT : 0 < T)
    (hU : S11pSeries D T U) (σ : ℕ ≃ ℕ × MultiIndex d) {J : ℕ}
    (hφ : IsSummableFeatureFamily J (fun j => D.f (σ j))) (μ0 : Measure (Euc d)) [IsProbabilityMeasure μ0]
    (α : MultiIndex d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    inner ℝ (s21gVec σ hT t α) (s21iY (fun j => D.f (σ j)) μ0 x) = U α t x - ∫ y, U α t y ∂μ0 := by
  have h1 := s21i_series hT hU σ t ht α x
  have h2 := s21i_reindex hT σ t α (fun q => ∫ y, D.f q y ∂μ0) (s11p_mu_series μ0 hT hU α t ht)
  have e : inner ℝ (s21gVec σ hT t α) (s21iY (fun j => D.f (σ j)) μ0 x) =
      ∑' j, SeqL2.coord (s21gVec σ hT t α) j * SeqL2.coord (s21iY (fun j => D.f (σ j)) μ0 x) j := by
    show inner ℝ (show lp (fun _ : ℕ => ℝ) 2 from s21gVec σ hT t α)
      (show lp (fun _ : ℕ => ℝ) 2 from s21iY (fun j => D.f (σ j)) μ0 x) = _
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun j => ?_
    simp [SeqL2.coord, mul_comm]
  rw [e]
  simp_rw [s21iY_coord hφ, mul_sub]
  exact (h1.sub h2).tsum_eq

theorem s21i_gauss_iid {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] :
    ∃ γ : Measure SeqL2, IsProbabilityMeasure γ ∧ IsCenteredGaussian γ ∧
      ∀ x y, covarianceBilin γ x y = covarianceBilin (μ0.map (s21iY φ μ0)) x y := by
  have hY := s21iY_meas hφ μ0
  have hYL : MemLp (s21iY φ μ0) 2 μ0 :=
    MemLp.of_bound hY.aestronglyMeasurable (2 * featureSum J φ) (ae_of_all _ fun x => s21iY_norm hφ μ0 x)
  obtain ⟨htc, -⟩ := HRS.isTraceClassCov_covarianceBilin μ0 (s21iY φ μ0) hYL (s21iY_mean hφ μ0)
  exact HRS.exists_centeredGaussian_of_traceClass _ htc

/-- The finite-dimensional laws of `Φ_* γ` for the i.i.d. (bridge) covariance. -/
theorem s21i_fdd0 {D : S11pData d} {U : MultiIndex d → ℝ → Euc d → ℝ} {T m : ℝ} (hT : 0 < T)
    (hU : S11pSeries D T U) (σ : ℕ ≃ ℕ × MultiIndex d) {J : ℕ}
    (hφ : IsSummableFeatureFamily J (fun j => D.f (σ j))) (g : Euc d → ℝ) (μ0 : Measure (Euc d))
    [IsProbabilityMeasure μ0] {γ : Measure SeqL2} [IsGaussian γ] (hγ0 : ∫ z, id z ∂γ = 0)
    (hcov : ∀ x y, covarianceBilin γ x y = covarianceBilin (μ0.map (s21iY (fun j => D.f (σ j)) μ0)) x y) :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun i j => HRS.Whole.susceptibilityCov g μ0 0
        (U (αs i) (ts i)) (U (αs j) (ts j))).PosSemidef ∧
      (γ.map (s21gPhi σ hT m)).map (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
          OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov g μ0 0
          (U (αs i) (ts i)) (U (αs j) (ts j))) := by
  intro p ts hts αs
  set Y := s21iY (fun j => D.f (σ j)) μ0 with hYdef
  have hY : Measurable Y := s21iY_meas hφ μ0
  haveI hμY : IsProbabilityMeasure (μ0.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hYmem : MemLp id 2 (μ0.map Y) := by
    refine MemLp.of_bound aestronglyMeasurable_id (2 * featureSum J (fun j => D.f (σ j))) ?_
    exact (ae_map_iff (μ := μ0) hY.aemeasurable
      (p := fun v : SeqL2 => ‖v‖ ≤ 2 * featureSum J (fun j => D.f (σ j)))
      (isClosed_le continuous_norm continuous_const).measurableSet).2
      (ae_of_all _ fun x => s21iY_norm hφ μ0 x)
  have hYmean : ∫ z, id z ∂(μ0.map Y) = 0 := by
    rw [integral_map hY.aemeasurable aestronglyMeasurable_id]
    exact s21iY_mean hφ μ0
  set w : Fin p → SeqL2 := fun i => s21gVec σ hT (ts i) (αs i) with hw
  have hcovij : ∀ i j, covarianceBilin γ (w i) (w j) =
      HRS.Whole.susceptibilityCov g μ0 0 (U (αs i) (ts i)) (U (αs j) (ts j)) := by
    intro i j
    rw [hcov, covarianceBilin_apply hYmem, hYmean]
    simp only [id, sub_zero]
    rw [integral_map hY.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun z : SeqL2 => inner ℝ (w i) z * inner ℝ (w j) z) (μ0.map Y))]
    obtain ⟨Cb, hCb⟩ := s11p_U_bound hT hU (αs j) (ts j) (hts j)
    rw [s11p_susc μ0 g (s11p_U_continuous hT hU (αs j) (ts j) (hts j)) hCb (U (αs i) (ts i))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hw, hYdef]
    rw [s21i_inner_vec_Y hT hU σ hφ μ0 (αs i) (ts i) (hts i) x,
      s21i_inner_vec_Y hT hU σ hφ μ0 (αs j) (ts j) (hts j) x]
  obtain ⟨hPSD, hlaw⟩ := s21g_fdd_gaussian γ hγ0 w
  have e : (Matrix.of fun i j => covarianceBilin γ (w i) (w j)) =
      Matrix.of fun i j => HRS.Whole.susceptibilityCov g μ0 0 (U (αs i) (ts i)) (U (αs j) (ts j)) := by
    ext i j; exact hcovij i j
  rw [e] at hPSD hlaw
  refine ⟨hPSD, ?_⟩
  have hFm : Measurable (fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
      OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) := by
    have h1 : Continuous fun w : OscPath d m T => (WithLp.toLp 2 fun i =>
        OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p)) := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      exact s11p_coord_at_continuous m T ⟨ts i, hts i⟩ (αs i)
    exact h1.measurable
  rw [Measure.map_map hFm (s21gPhi σ hT m).continuous.measurable]
  convert hlaw using 2
  funext z
  ext i
  simp only [Function.comp_apply]
  rw [s21gAw_apply, s21gPhi_coord_inner]

/-- Projection tail of a law with coordinate second moments `≤ s_k`. -/
theorem s21i_tail (ν : Measure SeqL2) [IsProbabilityMeasure ν] {τ : ℝ} (hτ : 0 ≤ τ) (s : ℕ → ℝ)
    (hs0 : ∀ k, 0 ≤ s k) (hs : Summable s)
    (hsν : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂ν ≤ ENNReal.ofReal (s k)) {Q : ℕ} (hQ : 1 ≤ Q)
    {I : Finset ℕ} (hT : ∑' k : ℕ, (if k ∈ I then 0 else s k) ≤ τ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2)) :
    ∫⁻ v, ‖v - (s21hSpan I).starProjection v‖ₑ ∂ν ≤ ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4)) := by
  classical
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsum : Summable fun k : ℕ => if k ∈ I then 0 else s k :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hs0 k]) (fun k => by split_ifs <;> simp [hs0 k]) hs
  have hT0 : 0 ≤ ∑' k : ℕ, (if k ∈ I then 0 else s k) := tsum_nonneg fun k => by split_ifs <;> simp [hs0 k]
  have hconv : (∑' k : ℕ, if k ∈ I then (0 : ℝ≥0∞) else ENNReal.ofReal (s k)) =
      ENNReal.ofReal (∑' k : ℕ, if k ∈ I then 0 else s k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by split_ifs <;> simp [hs0 k]) hsum]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  refine (s21h_tail_of_coords ν I (fun k => ENNReal.ofReal (s k)) hsν).trans ?_
  rw [hconv, ENNReal.ofReal_rpow_of_nonneg hT0 (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sqrt_eq_rpow]
  exact s21h_sqrt_tail hτ hQ0 hT

theorem s21i_evariance_sum_pi {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (N : ℕ) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i)) (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (N * ∫ x, f x ^ 2 ∂μ) := by
  have hmem : ∀ i : Fin N, MemLp (fun X : Fin N → Euc d => f (X i)) 2 (Measure.pi fun _ : Fin N => μ) :=
    fun i => hf2.comp_measurePreserving (measurePreserving_eval _ i)
  have hS : MemLp (fun X : Fin N → Euc d => ∑ i, f (X i)) 2 (Measure.pi fun _ : Fin N => μ) := by
    have := memLp_finsetSum' (s := Finset.univ) (fun i _ => hmem i)
    convert this using 1
    funext X
    simp [Finset.sum_apply]
  rw [← hS.ofReal_variance_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv := variance_sum_pi (μ := fun _ : Fin N => μ) (X := fun _ => f) (fun _ => hf2)
  have e : (fun X : Fin N → Euc d => ∑ i, f (X i)) = ∑ i : Fin N, fun x : Fin N → Euc d => f (x i) := by
    funext X
    simp [Finset.sum_apply]
  rw [e, hv]
  have h1 : variance f μ ≤ ∫ x, f x ^ 2 ∂μ := by
    have := variance_le_expectation_sq (μ := μ) hf.aestronglyMeasurable
    simpa using this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N)

theorem s21i_iid_linear {μ0 : Measure (Euc d)} [IsProbabilityMeasure μ0] {N : ℕ} (hN : 1 ≤ N) {f : Euc d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ0) :
    evariance (HRS.Whole.linStat f) (Measure.pi fun _ : Fin N => μ0) ≤
      ENNReal.ofReal (1 / N * ∫ x, f x ^ 2 ∂μ0) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (HRS.Whole.linStat f : EucConfig d N → ℝ) = fun X => (N : ℝ)⁻¹ * ∑ i, f (X i) :=
    funext fun X => HRS.Whole.pair_empirical (by omega) X f
  rw [e, evariance_mul]
  refine (mul_le_mul' le_rfl (s21i_evariance_sum_pi hf hf2 N)).trans ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  field_simp

end HRS.MS.S21
