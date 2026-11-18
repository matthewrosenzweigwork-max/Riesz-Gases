import HRS.Appendix.B15EAux3

/-!
# Packet B15E, part 4: bridges between the configuration space `𝕋^d)^N` and the big torus `𝕋^{Nd}`

`b15c_gibbsRefGen`, `b15c_gibbsEntropyGen`, `b15_fisherInfoGen` (configuration language, packets B/C) versus
`d1_gibbsMeasure`, `relEntropy`, `d1_fisherInfo` (big-torus language, packets D1/D3), transported by the
measure-preserving equivalence `d1_configEquiv`; the downstream copy `b15e_law_eq_fp` of `b15d_law_eq_fp`
with the proved (`_proof`) inputs; and the combined law-entropy inequality `b15e_law_entropy` (D2 + D3).
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Entropy bridge -/

theorem b15e_weight_comp (invβ : ℝ) (U : Config d N → ℝ) (X : Config d N) :
    d1_gibbsWeight invβ (U ∘ (d1_configEquiv d N).symm) (d1_configEquiv d N X) =
      b15c_gibbsWeightGen invβ U X := by
  simp [d1_gibbsWeight, b15c_gibbsWeightGen, neg_mul]

theorem b15e_partition_comp (invβ : ℝ) (U : Config d N → ℝ) :
    (∫⁻ x, ENNReal.ofReal (d1_gibbsWeight invβ (U ∘ (d1_configEquiv d N).symm) x)) =
      b15c_gibbsPartitionGen invβ U := by
  unfold b15c_gibbsPartitionGen
  rw [← (d1_configEquiv_measurePreserving d N).lintegral_comp_emb
    (d1_configEquiv d N).measurableEmbedding]
  simp only [b15e_weight_comp]

theorem b15e_gibbsRefGen_map (invβ : ℝ) (U : Config d N → ℝ) :
    (b15c_gibbsRefGen invβ U).map (d1_configEquiv d N) =
      d1_gibbsMeasure invβ (U ∘ (d1_configEquiv d N).symm) := by
  set e := d1_configEquiv d N with he
  unfold b15c_gibbsRefGen d1_gibbsMeasure d1_gibbsRaw
  rw [b15e_partition_comp, Measure.map_smul]
  · congr 1
    ext s hs
    rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
      withDensity_apply _ hs]
    have := (d1_configEquiv_measurePreserving d N).setLIntegral_comp_preimage_emb
      e.measurableEmbedding (fun y => ENNReal.ofReal (d1_gibbsWeight invβ (U ∘ e.symm) y)) s
    rw [← this]
    refine lintegral_congr fun X => ?_
    rw [b15e_weight_comp]
  · exact e.measurable.aemeasurable

/-- `klDiv` is invariant under a measurable equivalence. -/
theorem b15e_klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] : klDiv (P.map e) (Q.map e) = klDiv P Q := by
  refine le_antisymm (klDiv_map_le P Q e.measurable) ?_
  have h := klDiv_map_le (P.map e) (Q.map e) e.symm.measurable
  rwa [Measure.map_map e.symm.measurable e.measurable, Measure.map_map e.symm.measurable e.measurable,
    show (e.symm : β → α) ∘ e = id from funext e.symm_apply_apply, Measure.map_id, Measure.map_id] at h

theorem b15e_relEntropy_map (invβ : ℝ) (U : Config d N → ℝ) (P : Measure (Config d N))
    [IsFiniteMeasure P] [IsFiniteMeasure (b15c_gibbsRefGen invβ U)] :
    relEntropy (P.map (d1_configEquiv d N)) (d1_gibbsMeasure invβ (U ∘ (d1_configEquiv d N).symm)) =
      relEntropy P (b15c_gibbsRefGen invβ U) := by
  unfold relEntropy
  rw [← b15e_gibbsRefGen_map, b15e_klDiv_map_equiv]

/-! ### Fisher bridge -/

theorem b15e_isSmooth_pushField (ζ : Config d N → (Fin N → Euc d)) (hζ : IsFisherTestField ζ) :
    Torus.IsSmooth (d1_pushField ζ) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [d1_lift_pushField]
  exact (d1_eucEquiv d N).contDiff.comp (hζ.smooth.comp (d1_eucEquiv d N).symm.contDiff)

theorem b15e_fisher_integrand_eq (invβ : ℝ) (U : Config d N → ℝ) (ζ : Config d N → (Fin N → Euc d))
    (hζ : IsFisherTestField ζ) (X : Config d N) :
    (-2 * Torus.div (d1_pushField ζ) (d1_configEquiv d N X)
      + 2 * invβ⁻¹ * inner ℝ (d1_pushField ζ (d1_configEquiv d N X))
          (Torus.grad (U ∘ (d1_configEquiv d N).symm) (d1_configEquiv d N X))
      - ‖d1_pushField ζ (d1_configEquiv d N X)‖ ^ 2) =
    b15c_fisherIntegrand invβ U ζ X := by
  have hdiff : Differentiable ℝ fun Y : Fin N → Euc d => ζ fun i => Torus.mk (Y i) :=
    hζ.smooth.differentiable (by simp)
  rw [d1_div_pushField ζ hdiff X]
  have h1 : d1_pushField ζ (d1_configEquiv d N X) = d1_eucEquiv d N (ζ X) := by
    simp [d1_pushField]
  have hcl : d1_cl (U ∘ (d1_configEquiv d N).symm) =
      fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i)) := by
    funext Z; simp [d1_cl]
  have h2 := d1_fderiv_cl_eq_inner (U ∘ (d1_configEquiv d N).symm) X (ζ X)
  rw [hcl] at h2
  unfold b15c_fisherIntegrand
  rw [h1, h2, d1_norm_sq_eucEquiv, real_inner_comm]

theorem b15e_fisherInfoGen_le (invβ : ℝ) (U : Config d N → ℝ) (P : Measure (Config d N)) :
    b15_fisherInfoGen invβ U P ≤
      d1_fisherInfo invβ (U ∘ (d1_configEquiv d N).symm) (P.map (d1_configEquiv d N)) := by
  rw [b15c_fisherInfoGen_eq]
  refine iSup₂_le fun ζ hζ => ?_
  refine le_trans ?_ (le_iSup₂ (f := fun (ζ' : Torus (N * d) → Euc (N * d)) (_ : Torus.IsSmooth ζ') =>
    ENNReal.ofReal (∫ x, (-2 * Torus.div ζ' x
      + 2 * invβ⁻¹ * inner ℝ (ζ' x) (Torus.grad (U ∘ (d1_configEquiv d N).symm) x)
      - ‖ζ' x‖ ^ 2) ∂(P.map (d1_configEquiv d N)))) (d1_pushField ζ) (b15e_isSmooth_pushField ζ hζ))
  refine le_of_eq ?_
  congr 1
  rw [integral_map_equiv]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  exact (b15e_fisher_integrand_eq invβ U ζ hζ X).symm

/-! ### The law of the smooth regularised SDE: D2 (proved inputs) + D3 -/

/-- Downstream copy of `d1_law_isConfigWeakSolution` using `d1_law_eqT_proof`. -/
theorem b15e_law_isConfigWeakSolution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    (T : ℝ) :
    D1ConfigWeakSolution κ bC T (d1_lawOf P Y) where
  finite t ht :=
    haveI := d1_lawOf_isProbabilityMeasure (P := P) (Y := Y)
      ((hY.adapted t).mono (ℱ.le t) le_rfl)
    inferInstance
  narrow ψ hψ :=
    d1_lawOf_narrow (fun t _ => (hY.adapted t).mono (ℱ.le t) le_rfl)
      (fun ω => by
        by_cases hT : 0 ≤ T
        · exact hY.cont ω T hT (WithTop.coe_lt_top _)
        · simp [Set.Icc_eq_empty (not_le.2 (not_le.1 hT))]) _ hψ
  eqT τ hτ Φ Φt hΦ := d1_law_eqT_proof hW' hκ hbC hY₀ hY τ hτ Φ Φt hΦ

/-- Downstream copy of `b15d_law_eq_fp` with the proved inputs (`d1_law_eqT_proof`,
`b15d_liftedDriftReg_continuous_proof`, `b15d_U_isSmooth_proof`). -/
theorem b15e_law_eq_fp (hNd : 1 ≤ N * d) (D : DynData d) {κ : ℝ} (hκ : 0 < κ) (hDκ : D.invβ = κ)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsSmooth D.V) (M : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} {μ : ℝ → Measure (Torus (N * d))}
    (hμ : D1WeakSolution κ (d1_gradDrift (b15d_U D M)) T μ)
    (h0 : μ 0 = (d1_lawOf P Y 0).map (d1_configEquiv d N)) :
    ∀ t ∈ Set.Icc 0 T, (d1_lawOf P Y t).map (d1_configEquiv d N) = μ t := by
  have hV2 : Torus.IsCk 2 D.V :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.V) from hV).of_le
      (by first | exact WithTop.coe_le_coe.2 le_top | (norm_cast; exact le_top) | simp)
  have hY' : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift (b15d_configDriftReg D M))
      (d1_noise d N κ) Y₀ (fun _ => ⊤) Y := by
    rw [← b15d_liftedDriftReg_eq, ← hDκ]; exact hY
  have hν := b15e_law_isConfigWeakSolution hW' hκ.le (b15d_liftedDriftReg_continuous_proof D hV2 M)
    hY₀ hY' T
  exact d1_config_law_eq hNd hκ (b15d_U_isSmooth_proof D hV M)
    (b15d_pushField_eq_gradDrift D hM hV2 M) hν hμ h0

/-- **D2 + D3 combined**: for smooth `V`, the law `P^t = Law(mk ∘ Y_t)` of the level-`M` regularised SDE
satisfies the free-energy dissipation inequality of `d1_fp_entropy`, in the big-torus language. -/
theorem b15e_law_entropy (hNd : 1 ≤ N * d) (D : DynData d) {κ : ℝ} (hκ : 0 < κ) (hDκ : D.invβ = κ)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsSmooth D.V) (M : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 < T)
    (hfin : relEntropy ((d1_lawOf P Y 0).map (d1_configEquiv d N))
      (d1_gibbsMeasure κ (b15d_U D M)) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy ((d1_lawOf P Y t).map (d1_configEquiv d N)) (d1_gibbsMeasure κ (b15d_U D M)) +
        ENNReal.ofReal κ * ∫⁻ r in Set.Icc 0 t,
          d1_fisherInfo κ (b15d_U D M) ((d1_lawOf P Y r).map (d1_configEquiv d N))
      ≤ relEntropy ((d1_lawOf P Y 0).map (d1_configEquiv d N)) (d1_gibbsMeasure κ (b15d_U D M)) := by
  intro t ht
  have : IsProbabilityMeasure (d1_lawOf P Y 0) :=
    d1_lawOf_isProbabilityMeasure (P := P) (Y := Y) ((hY.adapted 0).mono (ℱ.le 0) le_rfl)
  have : IsProbabilityMeasure ((d1_lawOf P Y 0).map (d1_configEquiv d N)) :=
    (Measure.isProbabilityMeasure_map_iff (d1_configEquiv d N).measurable.aemeasurable).2 inferInstance
  obtain ⟨μ, hμ, h0⟩ := d1_fp_exists_proof hNd hκ (b15d_U_isSmooth_proof D hV M) hT
    ((d1_lawOf P Y 0).map (d1_configEquiv d N))
  have heq := b15e_law_eq_fp hNd D hκ hDκ hM hV M hW' hY₀ hY hμ h0
  have : IsProbabilityMeasure (μ 0) := by rw [h0]; infer_instance
  have hfin' : relEntropy (μ 0) (d1_gibbsMeasure κ (b15d_U D M)) < ⊤ := by rw [h0]; exact hfin
  have key := d1_fp_entropy_proof hNd hκ (b15d_U_isSmooth_proof D hV M) hT hμ hfin' t ht
  rw [h0] at key
  rw [heq t ht]
  have hcongr : ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (b15d_U D M) ((d1_lawOf P Y r).map (d1_configEquiv d N))
      = ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (b15d_U D M) (μ r) := by
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [heq r ⟨hr.1, hr.2.trans ht.2⟩]
  rw [hcongr]
  exact key

end HRS
