import HRS.MS.WrFeatAux1

/-!
# WR-10 (part 2): `FeatHyp`, norms of the feature map, and the energy identity

Packet WR-10 of `docs/WR_B_PLAN.md` (T2), namespace `HRS.MS.Wr`, helper prefix `wr10_`.

Exported declarations (interface contract C1 of the plan):

* `FeatHyp Ψ k`: `Ψ : Euc d → H` is continuous with `⟪Ψ x, Ψ y⟫ = k (x - y)`, `H` a real inner product
  space (completeness and separability are only assumed where used);
* `featMap_hyp`: `FeatHyp (featMap d s τ) (kTau d s τ)` for `0 < s`, `0 < τ`
  (the target is `L²(featMeasure; ℝ²)`, which is complete and separable: `featMap_separableSpace`);
* `featMap_inner` (WrFeatAux1), `featMap_norm_sq`: `‖featMap x‖² = kTau d s τ 0`;
* `FeatHyp.integrable` / `featMap_integrable`: `Ψ` is Bochner integrable against every finite measure;
* `FeatHyp.norm_Xi_le`: `‖Ψ x - ∫ Ψ dμ‖ ≤ 2 √(k 0)` for a probability measure `μ`;
* `energy_identity_E`: for `FeatHyp Ψ k` (`H` complete), a probability measure `μ`, `1 ≤ N`, any `X`,
  `N * pairEnergy (fun x y => k (x - y)) X μ =
     1/2 * ‖(√N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 - 1/2 * k 0`.

Deviations from the plan: (i) `[SeparableSpace H]` is NOT assumed in `FeatHyp` or in the energy identity
(it is never used there; the statements are strictly more general); separability of the concrete
target is proved separately.  (ii) `energy_identity_E` is proved by the direct expansion of the norm
(port of `HRS/MH/FeatureMap3.lean:109`) and does not need `wr7_pairEnergy_eq`, since `pairEnergy`
is already defined by the same sums.  (iii) `featMap` is defined by a dependent `if` on `0 < s ∧ 0 < τ`
(`WrFeatAux1`); the theorems below carry `hs`, `hτ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.Wr

open HRS.Whole HRS.MS.Psd HRS.Whole.Q34

variable {d : ℕ}

/-- Hypothesis of an abstract Hilbert feature map: `Ψ` is continuous and has Gram kernel `k (x - y)`. -/
structure FeatHyp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : Euc d → H) (k : Euc d → ℝ) : Prop where
  continuous : Continuous Ψ
  inner_eq : ∀ x y : Euc d, inner ℝ (Ψ x) (Ψ y) = k (x - y)

theorem wr10_scale {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (N : ℕ) (v : H) :
    ‖(Real.sqrt N)⁻¹ • v‖ ^ 2 = (N : ℝ)⁻¹ * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Pure real algebra of the diagonal bookkeeping (port of `fm3_core`). -/
theorem wr10_core (N : ℕ) (hN : 1 ≤ N) (k : Fin N → Fin N → ℝ) (G : Fin N → ℝ) (Γ g0 : ℝ)
    (hk : ∀ i, k i i = g0) :
    (N : ℝ) * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k i j
        - (1 / (N : ℝ)) * ∑ i, G i + (1 / 2) * Γ) =
      (1 / 2) * ((N : ℝ)⁻¹ * ∑ i, ∑ j, (k i j - G i - G j + Γ)) - (1 / 2) * g0 := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e1 : ∑ i, ∑ j, k i j = ∑ i, ∑ j ∈ Finset.univ.erase i, k i j + N * g0 := by
    have h1 : ∀ i, ∑ j, k i j = g0 + ∑ j ∈ Finset.univ.erase i, k i j := fun i => by
      rw [← hk i, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have e2 : ∑ i, ∑ j, (k i j - G i - G j + Γ) =
      ∑ i, ∑ j, k i j - N * ∑ i, G i - N * ∑ j, G j + (N : ℝ) ^ 2 * Γ := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [e2, e1]
  field_simp
  ring

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Ψ : Euc d → H} {k : Euc d → ℝ}

theorem FeatHyp.norm_sq (h : FeatHyp Ψ k) (x : Euc d) : ‖Ψ x‖ ^ 2 = k 0 := by
  rw [← real_inner_self_eq_norm_sq, h.inner_eq x x, sub_self]

theorem FeatHyp.norm_eq (h : FeatHyp Ψ k) (x : Euc d) : ‖Ψ x‖ = Real.sqrt (k 0) := by
  rw [← h.norm_sq x, Real.sqrt_sq (norm_nonneg _)]

theorem FeatHyp.k_symm (h : FeatHyp Ψ k) (w : Euc d) : k (-w) = k w := by
  have h1 := h.inner_eq 0 w
  have h2 := h.inner_eq w 0
  rw [real_inner_comm] at h1
  simp only [sub_zero, zero_sub] at h1 h2
  rw [← h1, h2]

theorem FeatHyp.k_zero_nonneg (h : FeatHyp Ψ k) : 0 ≤ k 0 := by
  rw [← h.norm_sq 0]; positivity

theorem FeatHyp.k_abs_le (h : FeatHyp Ψ k) (w : Euc d) : |k w| ≤ k 0 := by
  have h1 := h.inner_eq w 0
  rw [sub_zero] at h1
  rw [← h1]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [h.norm_eq, h.norm_eq]
  exact (Real.mul_self_sqrt h.k_zero_nonneg).le

theorem FeatHyp.k_continuous (h : FeatHyp Ψ k) : Continuous k := by
  have : k = fun w => inner ℝ (Ψ w) (Ψ 0) := by
    funext w; rw [h.inner_eq w 0, sub_zero]
  rw [this]
  exact h.continuous.inner continuous_const

/-- `Ψ` is Bochner integrable against every finite measure (it is bounded by `√(k 0)`). -/
theorem FeatHyp.integrable (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsFiniteMeasure μ] :
    Integrable Ψ μ :=
  Integrable.of_bound h.continuous.aestronglyMeasurable (Real.sqrt (k 0))
    (Filter.Eventually.of_forall fun x => le_of_eq (h.norm_eq x))

/-- The centred feature `Ξ x = Ψ x - ∫ Ψ dμ`. -/
def featXi (Ψ : Euc d → H) (μ : Measure (Euc d)) (x : Euc d) : H := Ψ x - ∫ y, Ψ y ∂μ

theorem FeatHyp.norm_integral_le (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    ‖∫ y, Ψ y ∂μ‖ ≤ Real.sqrt (k 0) := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := Real.sqrt (k 0))
    (Filter.Eventually.of_forall fun x => le_of_eq (h.norm_eq x))
  simpa using this

/-- `‖Ξ‖ ≤ 2 √(k 0)`. -/
theorem FeatHyp.norm_Xi_le (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x : Euc d) : ‖featXi Ψ μ x‖ ≤ 2 * Real.sqrt (k 0) := by
  unfold featXi
  calc ‖Ψ x - ∫ y, Ψ y ∂μ‖ ≤ ‖Ψ x‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (k 0) + Real.sqrt (k 0) := by
        rw [h.norm_eq x]; exact add_le_add le_rfl (h.norm_integral_le μ)
    _ = 2 * Real.sqrt (k 0) := by ring

variable [CompleteSpace H]

/-! ### The energy identity -/

theorem wr10_inner_mean (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x : Euc d) : inner ℝ (Ψ x) (∫ y, Ψ y ∂μ) = ∫ y, k (x - y) ∂μ := by
  rw [← integral_inner (h.integrable μ) (Ψ x)]
  simp only [h.inner_eq]

theorem wr10_inner_mean' (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (y : Euc d) : inner ℝ (∫ z, Ψ z ∂μ) (Ψ y) = ∫ z, k (y - z) ∂μ := by
  rw [real_inner_comm (Ψ y) (∫ z, Ψ z ∂μ)]
  exact wr10_inner_mean h μ y

theorem wr10_inner_mm (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    inner ℝ (∫ z, Ψ z ∂μ) (∫ z, Ψ z ∂μ) = ∫ x, ∫ y, k (x - y) ∂μ ∂μ := by
  rw [← integral_inner (h.integrable μ) (∫ z, Ψ z ∂μ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => wr10_inner_mean' h μ y)

theorem wr10_inner_centered (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x y : Euc d) :
    inner ℝ (Ψ x - ∫ z, Ψ z ∂μ) (Ψ y - ∫ z, Ψ z ∂μ) =
      k (x - y) - (∫ z, k (x - z) ∂μ) - (∫ z, k (y - z) ∂μ) + ∫ w, ∫ z, k (w - z) ∂μ ∂μ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, h.inner_eq x y, wr10_inner_mean h μ x,
    wr10_inner_mean' h μ y, wr10_inner_mm h μ]
  ring

theorem wr10_norm_sum_sq (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {N : ℕ} (X : EucConfig d N) :
    ‖∑ i, (Ψ (X i) - ∫ z, Ψ z ∂μ)‖ ^ 2 =
      ∑ i, ∑ j, (k (X i - X j) - (∫ z, k (X i - z) ∂μ) - (∫ z, k (X j - z) ∂μ)
        + ∫ w, ∫ z, k (w - z) ∂μ ∂μ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact wr10_inner_centered h μ (X i) (X j)

/-- **Energy identity** (`O:eq:bounded-diagonal`, Euclidean form).  For a feature map `Ψ` with Gram kernel
`k (x - y)`, every probability measure `μ`, `1 ≤ N` and every configuration `X`,
`N * 𝖥_N^k(X, μ) = ½ ‖N^{-1/2} ∑ (Ψ (X i) - ∫ Ψ dμ)‖² - ½ k 0`. -/
theorem energy_identity_E (h : FeatHyp Ψ k) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 1 ≤ N) (X : EucConfig d N) :
    (N : ℝ) * pairEnergy (fun x y => k (x - y)) X μ =
      (1 / 2) * ‖(Real.sqrt N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 - (1 / 2) * k 0 := by
  have hB : ‖(Real.sqrt N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 =
      (N : ℝ)⁻¹ * ∑ i, ∑ j, (k (X i - X j) - (∫ z, k (X i - z) ∂μ) - (∫ z, k (X j - z) ∂μ)
        + ∫ w, ∫ z, k (w - z) ∂μ ∂μ) := by
    rw [wr10_scale, wr10_norm_sum_sq h μ X]
  rw [hB]
  unfold pairEnergy
  exact wr10_core N hN (fun i j => k (X i - X j)) (fun i => ∫ z, k (X i - z) ∂μ)
    (∫ w, ∫ z, k (w - z) ∂μ ∂μ) (k 0) (fun i => by simp)

end Abstract

/-! ### The concrete feature map -/

section Concrete

variable {s : ℝ} {τ : ℝ}

/-- **`FeatHyp (featMap d s τ) (kTau d s τ)`.** -/
theorem featMap_hyp (hs : 0 < s) (hτ : 0 < τ) : FeatHyp (featMap d s τ) (kTau d s τ) :=
  ⟨wr10_continuous_of_inner (kTau_continuous hs hτ) (featMap_inner hs hτ), featMap_inner hs hτ⟩

/-- `‖featMap x‖² = kTau d s τ 0`. -/
theorem featMap_norm_sq (hs : 0 < s) (hτ : 0 < τ) (x : Euc d) :
    ‖featMap d s τ x‖ ^ 2 = kTau d s τ 0 :=
  (featMap_hyp hs hτ).norm_sq x

theorem featMap_continuous (hs : 0 < s) (hτ : 0 < τ) : Continuous (featMap d s τ) :=
  (featMap_hyp hs hτ).continuous

/-- `featMap` is Bochner integrable against every finite measure. -/
theorem featMap_integrable (hs : 0 < s) (hτ : 0 < τ) (μ : Measure (Euc d)) [IsFiniteMeasure μ] :
    Integrable (featMap d s τ) μ :=
  (featMap_hyp hs hτ).integrable μ

/-- `‖Ξ x‖ ≤ 2 √(kTau d s τ 0)` for the centred feature `Ξ = featMap - ∫ featMap dμ`. -/
theorem featMap_Xi_le (hs : 0 < s) (hτ : 0 < τ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x : Euc d) : ‖featXi (featMap d s τ) μ x‖ ≤ 2 * Real.sqrt (kTau d s τ 0) :=
  (featMap_hyp hs hτ).norm_Xi_le μ x

/-- The target `L²(featMeasure; ℝ²)` is separable. -/
theorem featMap_separableSpace (hs : 0 < s) (hτ : 0 < τ) :
    TopologicalSpace.SeparableSpace
      (Lp (EuclideanSpace ℝ (Fin 2)) 2 (featMeasure d s τ)) := by
  have := isFiniteMeasure_featMeasure (d := d) hs hτ
  have hcg : MeasurableSpace.CountablyGenerated (ℝ × Euc d) := inferInstance
  have hsf : SFinite (featMeasure d s τ) := inferInstance
  have hsep : MeasureTheory.IsSeparable (featMeasure d s τ) := inferInstance
  have hf : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology (Lp (EuclideanSpace ℝ (Fin 2)) 2 (featMeasure d s τ)) :=
    inferInstance
  exact inferInstance

end Concrete

end HRS.MS.Wr
