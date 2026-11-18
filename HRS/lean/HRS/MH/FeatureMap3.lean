import HRS.MH.FeatureMap2

/-!
# Relocated proofs for `HRS/Energy/FeatureMap.lean`, part 3

`energy_identity_of_feature_proof`: for a continuous `Ψ : 𝕋^d → H` into a real Hilbert space with
`⟨Ψ(x),Ψ(y)⟩ = g(x-y)`, the modulated energy is `½ ‖N^{-1/2} ∑ (Ψ(x_i) - μ(Ψ))‖² - ½ g(0)` up to the
factor `N`.  The proof is Hilbert-space algebra: expand the squared norm, use `⟨Ψ(x), μ(Ψ)⟩ = ∫ g(x-y) dμ`
(`integral_inner`), then compare the double sums with the modulated energy.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MH.FeatureMap

open HRS

variable {d : ℕ}

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem fm3_norm_eq (g : Torus d → ℝ) (Ψ : Torus d → H)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (x : Torus d) :
    ‖Ψ x‖ = Real.sqrt (g 0) := by
  calc ‖Ψ x‖ = Real.sqrt (‖Ψ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (g 0) := by rw [← real_inner_self_eq_norm_sq, hg x x, sub_self]

theorem fm3_integrable (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Integrable Ψ μ :=
  MeasureTheory.Integrable.of_bound hΨ.aestronglyMeasurable (Real.sqrt (g 0))
    (Filter.Eventually.of_forall fun x => le_of_eq (fm3_norm_eq g Ψ hg x))

theorem fm3_inner_mean (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (x : Torus d) :
    inner ℝ (Ψ x) (∫ y, Ψ y ∂μ) = ∫ y, g (x - y) ∂μ := by
  rw [← integral_inner (fm3_integrable g Ψ hΨ hg μ) (Ψ x)]
  simp only [hg]

theorem fm3_inner_mean' (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (y : Torus d) :
    inner ℝ (∫ z, Ψ z ∂μ) (Ψ y) = ∫ z, g (y - z) ∂μ := by
  rw [real_inner_comm (Ψ y) (∫ z, Ψ z ∂μ)]
  exact fm3_inner_mean g Ψ hΨ hg μ y

theorem fm3_inner_mm (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] :
    inner ℝ (∫ z, Ψ z ∂μ) (∫ z, Ψ z ∂μ) = ∫ x, ∫ y, g (x - y) ∂μ ∂μ := by
  rw [← integral_inner (fm3_integrable g Ψ hΨ hg μ) (∫ z, Ψ z ∂μ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => fm3_inner_mean' g Ψ hΨ hg μ y)

theorem fm3_inner_centered (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (x y : Torus d) :
    inner ℝ (Ψ x - ∫ z, Ψ z ∂μ) (Ψ y - ∫ z, Ψ z ∂μ) =
      g (x - y) - (∫ z, g (x - z) ∂μ) - (∫ z, g (y - z) ∂μ) + ∫ w, ∫ z, g (w - z) ∂μ ∂μ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hg x y, fm3_inner_mean g Ψ hΨ hg μ x,
    fm3_inner_mean' g Ψ hΨ hg μ y, fm3_inner_mm g Ψ hΨ hg μ]
  ring

theorem fm3_norm_sum_sq (g : Torus d → ℝ) (Ψ : Torus d → H) (hΨ : Continuous Ψ)
    (hg : ∀ x y : Torus d, inner ℝ (Ψ x) (Ψ y) = g (x - y)) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {N : ℕ} (X : Config d N) :
    ‖∑ i, (Ψ (X i) - ∫ z, Ψ z ∂μ)‖ ^ 2 =
      ∑ i, ∑ j, (g (X i - X j) - (∫ z, g (X i - z) ∂μ) - (∫ z, g (X j - z) ∂μ)
        + ∫ w, ∫ z, g (w - z) ∂μ ∂μ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact fm3_inner_centered g Ψ hΨ hg μ (X i) (X j)

omit [CompleteSpace H] in
theorem fm3_scale (N : ℕ) (v : H) : ‖(Real.sqrt N)⁻¹ • v‖ ^ 2 = (N : ℝ)⁻¹ * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

end Hilbert

/-- Pure real algebra behind `O:eq:bounded-diagonal`: with `k i i = g0`, expanding the double sums. -/
theorem fm3_core (N : ℕ) (hN : 1 ≤ N) (k : Fin N → Fin N → ℝ) (G : Fin N → ℝ) (Γ g0 : ℝ)
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

theorem energy_identity_of_feature_proof : type_of% @HRS.energy_identity_of_feature := by
  intro d H _ _ _ g Ψ hΨ hg μ _ N hN X
  have hB : ‖(Real.sqrt N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 =
      (N : ℝ)⁻¹ * ∑ i, ∑ j, (g (X i - X j) - (∫ z, g (X i - z) ∂μ) - (∫ z, g (X j - z) ∂μ)
        + ∫ w, ∫ z, g (w - z) ∂μ ∂μ) := by
    rw [fm3_scale, fm3_norm_sum_sq g Ψ hΨ hg μ X]
  rw [hB]
  exact fm3_core N hN (fun i j => g (X i - X j)) (fun i => ∫ z, g (X i - z) ∂μ)
    (∫ w, ∫ z, g (w - z) ∂μ ∂μ) (g 0) (fun i => by simp)

end HRS.MH.FeatureMap
