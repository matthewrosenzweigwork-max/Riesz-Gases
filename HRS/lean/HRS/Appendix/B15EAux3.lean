import HRS.Appendix.B15EAux2

/-!
# Packet B15E, part 3: Gibbs weights of continuous potentials, entropy comparison and lower semicontinuity

Generic (potential-independent) versions of the packet-C/B facts that Stage 1 needs: partition functions
of continuous potentials are finite and positive, `U₁ ≤ U₂ ⇒ 𝓗_{U₁} ≤ 𝓗_{U₂}` (the proof of
`b15c_gibbsEntropyGen_le_proof` with the two potentials as parameters), and `𝓗_U(P) ≤ liminf 𝓗_{U_k}(P_k)`
for `U_k → U` pointwise and uniformly bounded, `P_k ⇀ P` (dominated convergence for the normalised
densities, then the abstract lower semicontinuity of `klDiv`, `b15b_klDiv_liminf_le`).
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem b15e_weight_continuous (invβ : ℝ) {U : Config d N → ℝ} (hU : Continuous U) :
    Continuous (b15c_gibbsWeightGen invβ U) := by
  unfold b15c_gibbsWeightGen
  exact Real.continuous_exp.comp (continuous_const.mul hU)

theorem b15e_partition_fin (invβ : ℝ) {U : Config d N → ℝ} (hU : Continuous U) :
    b15c_gibbsPartitionGen invβ U ≠ ⊤ ∧ b15c_gibbsPartitionGen invβ U ≠ 0 := by
  have hw := b15e_weight_continuous invβ hU
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hw.continuousOn
  obtain ⟨x0, -, hx0⟩ := (isCompact_univ (X := Config d N)).exists_isMinOn
    (Set.univ_nonempty) hw.continuousOn
  constructor
  · refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top ?_
    calc b15c_gibbsPartitionGen invβ U
        = ∫⁻ X : Config d N, ENNReal.ofReal (b15c_gibbsWeightGen invβ U X) := rfl
      _ ≤ ∫⁻ X : Config d N, ENNReal.ofReal C :=
          lintegral_mono fun X => ENNReal.ofReal_le_ofReal (by
            have := hC X (mem_univ _); rw [Real.norm_eq_abs] at this; exact (le_abs_self _).trans this)
      _ = ENNReal.ofReal C := by simp
  · intro h0
    have : ENNReal.ofReal (b15c_gibbsWeightGen invβ U x0) ≤ b15c_gibbsPartitionGen invβ U := by
      calc ENNReal.ofReal (b15c_gibbsWeightGen invβ U x0)
          = ∫⁻ X : Config d N, ENNReal.ofReal (b15c_gibbsWeightGen invβ U x0) := by simp
        _ ≤ _ := lintegral_mono fun X => ENNReal.ofReal_le_ofReal (hx0 (mem_univ X))
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
    exact absurd this (not_le.2 (Real.exp_pos _))

theorem b15e_partition_toReal_pos (invβ : ℝ) {U : Config d N → ℝ} (hU : Continuous U) :
    0 < (b15c_gibbsPartitionGen invβ U).toReal :=
  ENNReal.toReal_pos (b15e_partition_fin invβ hU).2 (b15e_partition_fin invβ hU).1

theorem b15e_gibbsRefGen_isProb (invβ : ℝ) {U : Config d N → ℝ} (hU : Continuous U) :
    IsProbabilityMeasure (b15c_gibbsRefGen invβ U) :=
  b15c_gibbsRefGen_isProb invβ U (b15e_partition_fin invβ hU).1 (b15e_partition_fin invβ hU).2

/-- **Monotonicity of the Gibbs entropy in the potential**: `U₁ ≤ U₂ ⇒ 𝓗_{U₁}(P) ≤ 𝓗_{U₂}(P)`
(`G₁ ≥ G₂`; the proof of `b15c_gibbsEntropyGen_le_proof` with the two potentials as parameters). -/
theorem b15e_gibbsEntropyGen_mono {invβ : ℝ} (hβ : 0 < invβ) {U₁ U₂ : Config d N → ℝ}
    (hU₁ : Continuous U₁) (hU₂ : Continuous U₂) (h : ∀ X, U₁ X ≤ U₂ X)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] :
    b15c_gibbsEntropyGen invβ U₁ P ≤ b15c_gibbsEntropyGen invβ U₂ P := by
  classical
  obtain ⟨hGr_ne_top, hGr_ne_zero⟩ := b15e_partition_fin invβ hU₁
  obtain ⟨hGt_ne_top, hGt_ne_zero⟩ := b15e_partition_fin invβ hU₂
  have hApos := b15e_partition_toReal_pos invβ hU₂
  have hBpos := b15e_partition_toReal_pos invβ hU₁
  have hwle : ∀ X, b15c_gibbsWeightGen invβ U₂ X ≤ b15c_gibbsWeightGen invβ U₁ X := by
    intro X
    unfold b15c_gibbsWeightGen
    refine Real.exp_le_exp.mpr ?_
    have hβ' : 0 < invβ⁻¹ := inv_pos.mpr hβ
    nlinarith [h X]
  have hAB : (b15c_gibbsPartitionGen invβ U₂).toReal ≤ (b15c_gibbsPartitionGen invβ U₁).toReal := by
    rw [b15c_gibbsPartitionGen_toReal hU₂, b15c_gibbsPartitionGen_toReal hU₁]
    have hi : ∀ U : Config d N → ℝ, Continuous U → Integrable (b15c_gibbsWeightGen invβ U) :=
      fun U hU => (b15e_weight_continuous invβ hU).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    exact integral_mono (hi U₂ hU₂) (hi U₁ hU₁) hwle
  have hQ := b15c_gibbsRefGen_eq_withDensity invβ U₂ hGt_ne_top hGt_ne_zero
  have hQe := b15c_gibbsRefGen_eq_withDensity invβ U₁ hGr_ne_top hGr_ne_zero
  have : IsProbabilityMeasure (b15c_gibbsRefGen invβ U₂) :=
    b15c_gibbsRefGen_isProb _ _ hGt_ne_top hGt_ne_zero
  have : IsProbabilityMeasure (b15c_gibbsRefGen invβ U₁) :=
    b15c_gibbsRefGen_isProb _ _ hGr_ne_top hGr_ne_zero
  have hna : ∫⁻ X, ENNReal.ofReal
      ((b15c_gibbsPartitionGen invβ U₂).toReal⁻¹ * b15c_gibbsWeightGen invβ U₂ X) ∂volume = 1 := by
    have h := measure_univ (μ := b15c_gibbsRefGen invβ U₂)
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hnb : ∫⁻ X, ENNReal.ofReal
      ((b15c_gibbsPartitionGen invβ U₁).toReal⁻¹ * b15c_gibbsWeightGen invβ U₁ X) ∂volume = 1 := by
    have h := measure_univ (μ := b15c_gibbsRefGen invβ U₁)
    rw [hQe, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hmeasA : Measurable (fun X => (b15c_gibbsPartitionGen invβ U₂).toReal⁻¹ *
      b15c_gibbsWeightGen invβ U₂ X) :=
    measurable_const.mul (b15e_weight_continuous invβ hU₂).measurable
  have hmeasB : Measurable (fun X => (b15c_gibbsPartitionGen invβ U₁).toReal⁻¹ *
      b15c_gibbsWeightGen invβ U₁ X) :=
    measurable_const.mul (b15e_weight_continuous invβ hU₁).measurable
  have hcab : ∀ᵐ X ∂(volume : Measure (Config d N)),
      ((b15c_gibbsPartitionGen invβ U₂).toReal / (b15c_gibbsPartitionGen invβ U₁).toReal) *
        ((b15c_gibbsPartitionGen invβ U₂).toReal⁻¹ * b15c_gibbsWeightGen invβ U₂ X) ≤
      (b15c_gibbsPartitionGen invβ U₁).toReal⁻¹ * b15c_gibbsWeightGen invβ U₁ X := by
    refine Filter.Eventually.of_forall fun X => ?_
    have hA0 := hApos.ne'
    have hB0 := hBpos.ne'
    calc _ = b15c_gibbsWeightGen invβ U₂ X / (b15c_gibbsPartitionGen invβ U₁).toReal := by
          field_simp
      _ ≤ b15c_gibbsWeightGen invβ U₁ X / (b15c_gibbsPartitionGen invβ U₁).toReal :=
          div_le_div_of_nonneg_right (hwle X) hBpos.le
      _ = _ := by rw [div_eq_inv_mul]
  have hc : 0 < (b15c_gibbsPartitionGen invβ U₂).toReal / (b15c_gibbsPartitionGen invβ U₁).toReal :=
    div_pos hApos hBpos
  unfold b15c_gibbsEntropyGen relEntropy
  rw [hQ, hQe]
  have ha0 : ∀ᵐ X ∂(volume : Measure (Config d N)),
      0 < (b15c_gibbsPartitionGen invβ U₂).toReal⁻¹ * b15c_gibbsWeightGen invβ U₂ X :=
    Filter.Eventually.of_forall fun X => mul_pos (inv_pos.mpr hApos) (b15c_gibbsWeightGen_pos _ _ _)
  have hb0 : ∀ᵐ X ∂(volume : Measure (Config d N)),
      0 < (b15c_gibbsPartitionGen invβ U₁).toReal⁻¹ * b15c_gibbsWeightGen invβ U₁ X :=
    Filter.Eventually.of_forall fun X => mul_pos (inv_pos.mpr hBpos) (b15c_gibbsWeightGen_pos _ _ _)
  by_cases hfin : klDiv P (volume.withDensity fun X => ENNReal.ofReal
      ((b15c_gibbsPartitionGen invβ U₂).toReal⁻¹ * b15c_gibbsWeightGen invβ U₂ X)) = ⊤
  · rw [hfin]; simp
  · obtain ⟨hne, hle⟩ := b15c_klDiv_withDensity_le volume P _ _ hmeasA hmeasB ha0 hb0 hna hnb hc hcab hfin
    rw [← EReal.coe_ennreal_toReal hne, ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_sub,
      ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [Real.log_div hApos.ne' hBpos.ne'] at hle
    linarith

/-- Abstract lower semicontinuity of `H(P|Q) - log Z` under narrow convergence of `P_k, Q_k` and convergence
of the (positive) normalisations `Z_k → Z` (the last part of `b15b_gibbsEntropy_liminf_le_proof`). -/
theorem b15e_entropy_liminf_abstract {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] {P Q : Measure α} {Pn Qn : ℕ → Measure α}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [∀ n, IsProbabilityMeasure (Pn n)] [∀ n, IsProbabilityMeasure (Qn n)]
    (hP : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P)))
    (hQ : ∀ φ : α → ℝ, Continuous φ → Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q)))
    {Z : ℝ} {Zn : ℕ → ℝ} (hZ : 0 < Z) (hZt : Tendsto Zn atTop (𝓝 Z)) :
    ((klDiv P Q : ℝ≥0∞) : EReal) - ((Real.log Z : ℝ) : EReal) ≤
      liminf (fun n => ((klDiv (Pn n) (Qn n) : ℝ≥0∞) : EReal) - ((Real.log (Zn n) : ℝ) : EReal)) atTop := by
  have hkl := b15b_klDiv_liminf_le hP hQ
  have hlog : Tendsto (fun n => Real.log (Zn n)) atTop (𝓝 (Real.log Z)) := hZt.log hZ.ne'
  have hLn : Tendsto (fun n => ((-Real.log (Zn n) : ℝ) : EReal)) atTop
      (𝓝 ((-Real.log Z : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 hlog.neg
  have hmono : Monotone (fun x : ℝ≥0∞ => ((x : ℝ≥0∞) : EReal)) :=
    fun x y h => EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  have hcont : Continuous (fun x : ℝ≥0∞ => ((x : ℝ≥0∞) : EReal)) := continuous_coe_ennreal_ereal
  have hc : ((klDiv P Q : ℝ≥0∞) : EReal) ≤
      liminf (fun n => ((klDiv (Pn n) (Qn n) : ℝ≥0∞) : EReal)) atTop :=
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hkl).trans
      (hmono.map_liminf_of_continuousAt (F := atTop) (fun n => klDiv (Pn n) (Qn n))
        hcont.continuousAt).le
  have hfun : (fun n => ((klDiv (Pn n) (Qn n) : ℝ≥0∞) : EReal) - ((Real.log (Zn n) : ℝ) : EReal)) =
      fun n => ((klDiv (Pn n) (Qn n) : ℝ≥0∞) : EReal) + ((-Real.log (Zn n) : ℝ) : EReal) := by
    funext n; rw [sub_eq_add_neg, EReal.coe_neg]
  rw [hfun, sub_eq_add_neg, ← EReal.coe_neg]
  calc _ ≤ liminf (fun n => ((klDiv (Pn n) (Qn n) : ℝ≥0∞) : EReal)) atTop
        + ((-Real.log Z : ℝ) : EReal) := add_le_add hc le_rfl
    _ = liminf (fun n => ((klDiv (Pn n) (Qn n) : ℝ≥0∞) : EReal)) atTop
        + liminf (fun n => ((-Real.log (Zn n) : ℝ) : EReal)) atTop := by rw [hLn.liminf_eq]
    _ ≤ _ := EReal.le_liminf_add

/-- **Lower semicontinuity of the Gibbs entropy in the potential and the law**: for continuous potentials
`U_k → U` pointwise, uniformly bounded, and `P_k ⇀ P` narrowly,
`𝓗_U(P) ≤ liminf 𝓗_{U_k}(P_k)`. -/
theorem b15e_gibbsEntropyGen_liminf_le {invβ : ℝ} (hβ : 0 < invβ) {U : Config d N → ℝ}
    {Uk : ℕ → Config d N → ℝ} (hU : Continuous U) (hUk : ∀ k, Continuous (Uk k)) {B : ℝ}
    (hB : ∀ k X, |Uk k X| ≤ B) (hconv : ∀ X, Tendsto (fun k => Uk k X) atTop (𝓝 (U X)))
    {P : Measure (Config d N)} {Pn : ℕ → Measure (Config d N)}
    [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Pn n)]
    (hP : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂(Pn n)) atTop (𝓝 (∫ x, φ x ∂P))) :
    b15c_gibbsEntropyGen invβ U P ≤ liminf (fun k => b15c_gibbsEntropyGen invβ (Uk k) (Pn k)) atTop := by
  have : IsProbabilityMeasure (b15c_gibbsRefGen invβ U) := b15e_gibbsRefGen_isProb invβ hU
  have : ∀ k, IsProbabilityMeasure (b15c_gibbsRefGen invβ (Uk k)) := fun k =>
    b15e_gibbsRefGen_isProb invβ (hUk k)
  set a : ℝ := invβ⁻¹ with ha
  have hapos : 0 < a := inv_pos.mpr hβ
  set C : ℝ := Real.exp (a * B) with hC
  set c0 : ℝ := Real.exp (-(a * B)) with hc0
  have hc0pos : 0 < c0 := Real.exp_pos _
  have hwk_le : ∀ k X, b15c_gibbsWeightGen invβ (Uk k) X ≤ C := by
    intro k X
    unfold b15c_gibbsWeightGen
    refine Real.exp_le_exp.mpr ?_
    have := (abs_le.1 (hB k X)).1
    nlinarith
  have hwk_ge : ∀ k X, c0 ≤ b15c_gibbsWeightGen invβ (Uk k) X := by
    intro k X
    unfold b15c_gibbsWeightGen
    refine Real.exp_le_exp.mpr ?_
    have := (abs_le.1 (hB k X)).2
    nlinarith
  have hwpt : ∀ X, Tendsto (fun k => b15c_gibbsWeightGen invβ (Uk k) X) atTop
      (𝓝 (b15c_gibbsWeightGen invβ U X)) := by
    intro X
    unfold b15c_gibbsWeightGen
    exact (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul (hconv X))
  have hint : ∀ V : Config d N → ℝ, Continuous V → Integrable (b15c_gibbsWeightGen invβ V) :=
    fun V hV => (b15e_weight_continuous invβ hV).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hZt : Tendsto (fun k => (b15c_gibbsPartitionGen invβ (Uk k)).toReal) atTop
      (𝓝 (b15c_gibbsPartitionGen invβ U).toReal) := by
    simp only [b15c_gibbsPartitionGen_toReal (hUk _), b15c_gibbsPartitionGen_toReal hU]
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun k => (b15e_weight_continuous invβ (hUk k)).measurable.aestronglyMeasurable)
      (integrable_const C) (fun k => Filter.Eventually.of_forall fun X => ?_)
      (Filter.Eventually.of_forall hwpt)
    rw [Real.norm_eq_abs, abs_of_pos (b15c_gibbsWeightGen_pos _ _ _)]
    exact hwk_le k X
  have hZk_ge : ∀ k, c0 ≤ (b15c_gibbsPartitionGen invβ (Uk k)).toReal := by
    intro k
    rw [b15c_gibbsPartitionGen_toReal (hUk k)]
    have := integral_mono (integrable_const c0) (hint _ (hUk k)) (fun X => hwk_ge k X)
    simpa using this
  have hZpos := b15e_partition_toReal_pos invβ hU
  -- narrow convergence of the Gibbs reference measures
  have hQ : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(b15c_gibbsRefGen invβ (Uk k))) atTop
        (𝓝 (∫ x, φ x ∂(b15c_gibbsRefGen invβ U))) := by
    intro φ hφ
    obtain ⟨Bφ, hBφ⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hφ.continuousOn
    have e : ∀ V : Config d N → ℝ, Continuous V → ∫ x, φ x ∂(b15c_gibbsRefGen invβ V) =
        ∫ X, ((b15c_gibbsPartitionGen invβ V).toReal⁻¹ * b15c_gibbsWeightGen invβ V X) * φ X := by
      intro V hV
      rw [b15c_gibbsRefGen_eq_withDensity invβ V (b15e_partition_fin invβ hV).1
        (b15e_partition_fin invβ hV).2]
      exact b15bp_integral_withDensity_ofReal _ _
        (measurable_const.mul (b15e_weight_continuous invβ hV).measurable)
        (fun X => mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (Real.exp_pos _).le) φ
    simp only [e _ (hUk _), e _ hU]
    refine tendsto_integral_of_dominated_convergence (fun _ => c0⁻¹ * C * Bφ)
      (fun k => ((measurable_const.mul (b15e_weight_continuous invβ (hUk k)).measurable).mul
        hφ.measurable).aestronglyMeasurable)
      (integrable_const _) (fun k => Filter.Eventually.of_forall fun X => ?_)
      (Filter.Eventually.of_forall fun X => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
        abs_of_pos (b15c_gibbsWeightGen_pos _ _ _)]
      have h1 : ((b15c_gibbsPartitionGen invβ (Uk k)).toReal)⁻¹ ≤ c0⁻¹ :=
        inv_anti₀ hc0pos (hZk_ge k)
      have h2 := hBφ X (mem_univ _)
      rw [Real.norm_eq_abs] at h2
      have h3 := hwk_le k X
      have h4 : 0 < b15c_gibbsWeightGen invβ (Uk k) X := Real.exp_pos _
      calc _ ≤ c0⁻¹ * C * |φ X| := by gcongr
        _ ≤ _ := by gcongr
    · exact ((hZt.inv₀ hZpos.ne').mul (hwpt X)).mul_const (φ X)
  have hQ' : ∀ φ : Config d N → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(b15c_gibbsRefGen invβ (Uk k))) atTop
        (𝓝 (∫ x, φ x ∂(b15c_gibbsRefGen invβ U))) := hQ
  have key := b15e_entropy_liminf_abstract (P := P) (Q := b15c_gibbsRefGen invβ U)
    (Pn := Pn) (Qn := fun k => b15c_gibbsRefGen invβ (Uk k)) hP hQ' hZpos hZt
  exact key

end HRS
