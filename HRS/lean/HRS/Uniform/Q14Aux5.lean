import HRS.Uniform.Q14Aux4

/-!
# Q14, part 5: the Bures bound for finite families of vector fields
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section Family

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ξ : Type*} [MeasurableSpace Ξ] {ξ : Measure Ξ} [IsFiniteMeasure ξ]

example (m : ℕ) : IsFiniteMeasure (Measure.count : Measure (Fin m)) := inferInstance


lemma q14_integral_prod_count {m : ℕ} (f : Ξ × Fin m → ℝ) (hf : Measurable f)
    (hB : ∃ B, ∀ p, |f p| ≤ B) :
    ∫ p, f p ∂(ξ.prod Measure.count) = ∑ j, ∫ s, f (s, j) ∂ξ := by
  obtain ⟨B, hB⟩ := hB
  have hi : Integrable f (ξ.prod Measure.count) :=
    Integrable.of_bound (C := B) hf.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hB p)
  have hj : ∀ j, Integrable (fun s => f (s, j)) ξ := fun j =>
    Integrable.of_bound (C := B)
      (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hB _)
  rw [integral_prod f hi]
  simp only [integral_count]
  rw [integral_finset_sum _ fun j _ => hj j]

theorem q14_bures2_le_family {m : ℕ} {u v : Fin m → Ξ → H} (hu : ∀ j, Measurable (u j))
    (hv : ∀ j, Measurable (v j)) {M : ℝ} (hM0 : 0 ≤ M) (hMu : ∀ j s, ‖u j s‖ ≤ M)
    (hMv : ∀ j s, ‖v j s‖ ≤ M) {C D : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : ∀ x y, C x y = ∑ j, ∫ s, inner ℝ (u j s) x * inner ℝ (u j s) y ∂ξ)
    (hD : ∀ x y, D x y = ∑ j, ∫ s, inner ℝ (v j s) x * inner ℝ (v j s) y ∂ξ) :
    Uniform.bures2 C D ≤ ∑ j, ∫ s, ‖u j s - v j s‖ ^ 2 ∂ξ := by
  classical
  let u' : Ξ × Fin m → H := fun p => u p.2 p.1
  let v' : Ξ × Fin m → H := fun p => v p.2 p.1
  have hu' : Measurable u' := measurable_from_prod_countable_left (fun j => hu j)
  have hv' : Measurable v' := measurable_from_prod_countable_left (fun j => hv j)
  have key := fun (f : Ξ × Fin m → ℝ) (hf : Measurable f) (hB : ∃ B, ∀ p, |f p| ≤ B) =>
    q14_integral_prod_count (ξ := ξ) f hf hB
  have hbd : ∀ (x y : H), ∃ B, ∀ p : Ξ × Fin m, |inner ℝ (u' p) x * inner ℝ (u' p) y| ≤ B := by
    intro x y
    refine ⟨M * ‖x‖ * (M * ‖y‖), fun p => ?_⟩
    rw [abs_mul]
    have h1 : |inner ℝ (u' p) x| ≤ M * ‖x‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hMu _ _) (norm_nonneg _))
    have h2 : |inner ℝ (u' p) y| ≤ M * ‖y‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hMu _ _) (norm_nonneg _))
    exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  have hbd' : ∀ (x y : H), ∃ B, ∀ p : Ξ × Fin m, |inner ℝ (v' p) x * inner ℝ (v' p) y| ≤ B := by
    intro x y
    refine ⟨M * ‖x‖ * (M * ‖y‖), fun p => ?_⟩
    rw [abs_mul]
    have h1 : |inner ℝ (v' p) x| ≤ M * ‖x‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hMv _ _) (norm_nonneg _))
    have h2 : |inner ℝ (v' p) y| ≤ M * ‖y‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hMv _ _) (norm_nonneg _))
    exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  have hC' : ∀ x y, C x y = ∫ p, inner ℝ (u' p) x * inner ℝ (u' p) y ∂(ξ.prod Measure.count) := by
    intro x y
    rw [key (fun p => inner ℝ (u' p) x * inner ℝ (u' p) y)
      ((hu'.inner measurable_const).mul (hu'.inner measurable_const)) (hbd x y), hC]
  have hD' : ∀ x y, D x y = ∫ p, inner ℝ (v' p) x * inner ℝ (v' p) y ∂(ξ.prod Measure.count) := by
    intro x y
    rw [key (fun p => inner ℝ (v' p) x * inner ℝ (v' p) y)
      ((hv'.inner measurable_const).mul (hv'.inner measurable_const)) (hbd' x y), hD]
  have hmain := q14_bures2_le_integral (ξ := ξ.prod Measure.count) hu' hv' hM0
    (fun p => hMu _ _) (fun p => hMv _ _) hC' hD'
  refine hmain.trans (le_of_eq ?_)
  rw [key (fun p => ‖u' p - v' p‖ ^ 2) ((hu'.sub hv').norm.pow_const 2)
    ⟨(2 * M) ^ 2, fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]
      refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
      have := hMu p.2 p.1; have := hMv p.2 p.1; linarith⟩]

/-- A form `C x y = ∑_j ∫ ⟨u_j,x⟩⟨u_j,y⟩ dξ` is trace class with trace `∑_j ∫ ‖u_j‖² dξ`. -/
theorem q14_form_of_family {m : ℕ} {u : Fin m → Ξ → H} (hu : ∀ j, Measurable (u j)) {M : ℝ}
    (hM : ∀ j s, ‖u j s‖ ≤ M) {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : ∀ x y, C x y = ∑ j, ∫ s, inner ℝ (u j s) x * inner ℝ (u j s) y ∂ξ)
    {ι : Type} (e : HilbertBasis ι ℝ H) :
    IsTraceClassCov C ∧ traceNormForm C = ∑ j, ∫ s, ‖u j s‖ ^ 2 ∂ξ := by
  classical
  let u' : Ξ × Fin m → H := fun p => u p.2 p.1
  have hu' : Measurable u' := measurable_from_prod_countable_left (fun j => hu j)
  have hbd : ∀ (x y : H), ∃ B, ∀ p : Ξ × Fin m, |inner ℝ (u' p) x * inner ℝ (u' p) y| ≤ B := by
    intro x y
    refine ⟨‖M‖ * ‖x‖ * (‖M‖ * ‖y‖), fun p => ?_⟩
    rw [abs_mul]
    have hM' : ‖u' p‖ ≤ ‖M‖ := (hM _ _).trans (le_abs_self M)
    have h1 : |inner ℝ (u' p) x| ≤ ‖M‖ * ‖x‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hM' (norm_nonneg _))
    have h2 : |inner ℝ (u' p) y| ≤ ‖M‖ * ‖y‖ :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hM' (norm_nonneg _))
    exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  have hC' : ∀ x y, C x y = ∫ p, inner ℝ (u' p) x * inner ℝ (u' p) y ∂(ξ.prod Measure.count) := by
    intro x y
    rw [q14_integral_prod_count (fun p => inner ℝ (u' p) x * inner ℝ (u' p) y)
      ((hu'.inner measurable_const).mul (hu'.inner measurable_const)) (hbd x y), hC]
  obtain ⟨h1, h2⟩ := q14_form_of_integral (ξ := ξ.prod Measure.count) hu' (M := ‖M‖)
    (fun p => (hM _ _).trans (le_abs_self M)) hC' e
  refine ⟨h1, ?_⟩
  rw [h2, q14_integral_prod_count (fun p => ‖u' p‖ ^ 2) (hu'.norm.pow_const 2)
    ⟨‖M‖ ^ 2, fun p => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hM _ _).trans (le_abs_self M)) 2⟩]

end Family

end HRS.Uniform.Q14
