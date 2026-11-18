import HRS.MS.S21G2_K11bB

/-!
# S21G2 K11b (part C) -- bilinear form calculus and the finite-section limit (R26-T3.K11b)

`B(f,g) = ∬ h f ⊗ g`; additivity in each slot, the finite expansion `B(∑ γ_i e_i, ∑ δ_j e_j) = ∑∑ γ_i δ_j B(e_i,e_j)`,
and the `L²` continuity of `B` along the orthonormal expansion.  Helpers carry the prefix `s21g2_k11b_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section BForm

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {h : E → E → ℝ}

/-- The kernel bilinear form `B(f,g) = ∬ h f ⊗ g`. -/
def s21g2_k11b_B (μ : Measure E) (h : E → E → ℝ) (f g : E → ℝ) : ℝ :=
  ∫ z : E × E, h z.1 z.2 * (f z.1 * g z.2) ∂(μ.prod μ)

theorem s21g2_k11b_B_sub_left (hh : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {f f' g : E → ℝ} (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) (hg : MemLp g 2 μ) :
    s21g2_k11b_B μ h (fun x => f x - f' x) g = s21g2_k11b_B μ h f g - s21g2_k11b_B μ h f' g := by
  unfold s21g2_k11b_B
  rw [← integral_sub (s21g2_k11b_B_bound hh hf hg).1 (s21g2_k11b_B_bound hh hf' hg).1]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

theorem s21g2_k11b_B_sub_right (hh : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {f g g' : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hg' : MemLp g' 2 μ) :
    s21g2_k11b_B μ h f (fun x => g x - g' x) = s21g2_k11b_B μ h f g - s21g2_k11b_B μ h f g' := by
  unfold s21g2_k11b_B
  rw [← integral_sub (s21g2_k11b_B_bound hh hf hg).1 (s21g2_k11b_B_bound hh hf hg').1]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

theorem s21g2_k11b_B_finsum (hh : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ)) (n : ℕ)
    (γ δ : ℕ → ℝ) (e : ℕ → E → ℝ) (he : ∀ i, MemLp (e i) 2 μ) :
    s21g2_k11b_B μ h (fun x => ∑ i ∈ Finset.range n, γ i * e i x)
      (fun y => ∑ j ∈ Finset.range n, δ j * e j y) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, γ i * δ j * s21g2_k11b_B μ h (e i) (e j) := by
  unfold s21g2_k11b_B
  have hi : ∀ i j, Integrable (fun z : E × E => h z.1 z.2 * (e i z.1 * e j z.2)) (μ.prod μ) :=
    fun i j => (s21g2_k11b_B_bound hh (he i) (he j)).1
  have : ∀ z : E × E, h z.1 z.2 * ((∑ i ∈ Finset.range n, γ i * e i z.1) * (∑ j ∈ Finset.range n, δ j * e j z.2)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (γ i * δ j) * (h z.1 z.2 * (e i z.1 * e j z.2)) := fun z => by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hi i j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]

end BForm

section BLimit

variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {a : ℕ → HRS.Euc d → ℝ}
  {h : HRS.Euc d → HRS.Euc d → ℝ}

theorem s21g2_k11b_B_tendsto (ha : HRS.Whole.IsR2ZeroMeanONB μ a)
    (hh : MemLp (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2) 2 (μ.prod μ))
    {u v : HRS.Euc d → ℝ} (hu : HRS.Whole.MemL2Zero μ u) (hv : HRS.Whole.MemL2Zero μ v) :
    Tendsto (fun n => s21g2_k11b_B μ h
      (fun x => ∑ i ∈ Finset.range n,
        (∫ y, u y * HRS.Whole.projMean μ (a i) y ∂μ) * HRS.Whole.projMean μ (a i) x)
      (fun x => ∑ i ∈ Finset.range n,
        (∫ y, v y * HRS.Whole.projMean μ (a i) y ∂μ) * HRS.Whole.projMean μ (a i) x))
      atTop (𝓝 (s21g2_k11b_B μ h u v)) := by
  obtain ⟨hFm, hFb, hFt⟩ := s21g2_k11b_expand ha hu.1 hu.2
  obtain ⟨hGm, hGb, hGt⟩ := s21g2_k11b_expand ha hv.1 hv.2
  set F : ℕ → HRS.Euc d → ℝ := fun n x => ∑ i ∈ Finset.range n,
    (∫ y, u y * HRS.Whole.projMean μ (a i) y ∂μ) * HRS.Whole.projMean μ (a i) x with hF
  set G : ℕ → HRS.Euc d → ℝ := fun n x => ∑ i ∈ Finset.range n,
    (∫ y, v y * HRS.Whole.projMean μ (a i) y ∂μ) * HRS.Whole.projMean μ (a i) x with hG
  set c : ℝ := Real.sqrt (∫ z : HRS.Euc d × HRS.Euc d, h z.1 z.2 ^ 2 ∂(μ.prod μ)) with hc
  have hdec : ∀ n, s21g2_k11b_B μ h (F n) (G n) - s21g2_k11b_B μ h u v =
      s21g2_k11b_B μ h (fun x => F n x - u x) (G n) +
        s21g2_k11b_B μ h u (fun x => G n x - v x) := fun n => by
    rw [s21g2_k11b_B_sub_left hh (hFm n) hu.1 (hGm n), s21g2_k11b_B_sub_right hh hu.1 (hGm n) hv.1]
    ring
  have hs0 : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → Tendsto (fun n => Real.sqrt (f n)) atTop (𝓝 0) :=
    fun hf => by simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hf
  have ha1 := hs0 hFt
  have hb1 := hs0 hGt
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hb : Tendsto (fun n => c * (Real.sqrt (∫ x, (F n x - u x) ^ 2 ∂μ) * Real.sqrt (∫ x, v x ^ 2 ∂μ) +
      Real.sqrt (∫ x, u x ^ 2 ∂μ) * Real.sqrt (∫ x, (G n x - v x) ^ 2 ∂μ))) atTop (𝓝 0) := by
    have := ((ha1.mul_const (Real.sqrt (∫ x, v x ^ 2 ∂μ))).add
      (hb1.const_mul (Real.sqrt (∫ x, u x ^ 2 ∂μ)))).const_mul c
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  rw [Real.norm_eq_abs, hdec n]
  have hFu : MemLp (fun x => F n x - u x) 2 μ := (hFm n).sub hu.1
  have hGv : MemLp (fun x => G n x - v x) 2 μ := (hGm n).sub hv.1
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (s21g2_k11b_B_bound hh hFu (hGm n)).2.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hGb n))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · exact (s21g2_k11b_B_bound hh hu.1 hGv).2

end BLimit

end HRS.MS.R26T3
