import HRS.MC.Sec7Vocab

/-!
# Packet `s7_S7e_pairing_identification`, helper 1: expansion of a continuous trilinear form along a
`HasSum` (abstract), and the interchange of a triple series with an integral for uniformly dominated terms.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7e

theorem s7e_update0 {E : Type*} (u v w x : E) : Function.update ![u, v, w] 0 x = ![x, v, w] := by
  ext i; fin_cases i <;> simp
theorem s7e_update1 {E : Type*} (u v w x : E) : Function.update ![u, v, w] 1 x = ![u, x, w] := by
  ext i; fin_cases i <;> simp
theorem s7e_update2 {E : Type*} (u v w x : E) : Function.update ![u, v, w] 2 x = ![u, v, x] := by
  ext i; fin_cases i <;> simp

theorem s7e_expand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (D3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (e : ι → E) (c : ι → ℝ) (ℓ : E)
    (h : HasSum (fun k => c k • e k) ℓ) :
    D3 ![ℓ, ℓ, ℓ] = ∑' k, ∑' l, ∑' j, c k * c l * c j * D3 ![e k, e l, e j] := by
  classical
  have key : ∀ (m : Fin 3 → E) (i : Fin 3), HasSum (fun k => c k * D3 (Function.update m i (e k)))
      (D3 (Function.update m i ℓ)) := by
    intro m i
    have := h.mapL (D3.toContinuousLinearMap m i)
    simpa [map_smul] using this
  have h3 : ∀ k l, D3 ![e k, e l, ℓ] = ∑' j, c j * D3 ![e k, e l, e j] := fun k l => by
    have := key ![e k, e l, ℓ] 2
    simp only [s7e_update2] at this
    exact this.tsum_eq.symm
  have h2 : ∀ k, D3 ![e k, ℓ, ℓ] = ∑' l, c l * ∑' j, c j * D3 ![e k, e l, e j] := fun k => by
    have := key ![e k, ℓ, ℓ] 1
    simp only [s7e_update1] at this
    rw [← this.tsum_eq]
    refine tsum_congr fun l => ?_
    rw [h3 k l]
  have h1 : D3 ![ℓ, ℓ, ℓ] = ∑' k, c k * ∑' l, c l * ∑' j, c j * D3 ![e k, e l, e j] := by
    have := key ![ℓ, ℓ, ℓ] 0
    simp only [s7e_update0] at this
    rw [← this.tsum_eq]
    refine tsum_congr fun k => ?_
    rw [h2 k]
  rw [h1]
  simp_rw [← tsum_mul_left]
  refine tsum_congr fun k => tsum_congr fun l => tsum_congr fun j => ?_
  ring

theorem s7e_tsum_triple {ι : Type*} (h : ι × (ι × ι) → ℝ) (hs : Summable h) :
    ∑' p, h p = ∑' k, ∑' l, ∑' j, h (k, (l, j)) := by
  rw [hs.tsum_prod]
  refine tsum_congr fun k => ?_
  have hk : Summable fun q : ι × ι => h (k, q) := hs.prod_factor k
  rw [hk.tsum_prod]

theorem s7e_summable_triple {ι : Type*} {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) (M : ℝ) :
    Summable fun p : ι × (ι × ι) => M * b p.1 * b p.2.1 * b p.2.2 := by
  have h2 : Summable fun q : ι × ι => b q.1 * b q.2 :=
    Summable.mul_of_nonneg hb hb hb0 hb0
  have h3 : Summable fun p : ι × (ι × ι) => b p.1 * (b p.2.1 * b p.2.2) :=
    Summable.mul_of_nonneg (f := b) (g := fun q : ι × ι => b q.1 * b q.2) hb h2 hb0
      (fun q => mul_nonneg (hb0 _) (hb0 _))
  refine (h3.mul_left M).congr fun p => ?_
  ring

theorem s7e_integral_triple {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) (M : ℝ)
    (g : ι → ι → ι → X → ℝ) (hgi : ∀ k l j, Integrable (g k l j) μ)
    (hg : ∀ k l j x, |g k l j x| ≤ M * b k * b l * b j) :
    ∫ x, ∑' k, ∑' l, ∑' j, g k l j x ∂μ = ∑' k, ∑' l, ∑' j, ∫ x, g k l j x ∂μ := by
  have hM : Summable fun p : ι × (ι × ι) => M * b p.1 * b p.2.1 * b p.2.2 :=
    s7e_summable_triple hb hb0 M
  set F : ι × (ι × ι) → X → ℝ := fun p x => g p.1 p.2.1 p.2.2 x with hF
  have hFi : ∀ p, Integrable (F p) μ := fun p => hgi _ _ _
  have hint : Summable fun p => ∫ x, ‖F p x‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _) (fun p => ?_) hM
    have : ∫ x, ‖F p x‖ ∂μ ≤ ∫ _x, M * b p.1 * b p.2.1 * b p.2.2 ∂μ :=
      integral_mono (hFi p).norm (integrable_const _) fun x => by
        simpa [Real.norm_eq_abs] using hg p.1 p.2.1 p.2.2 x
    simpa using this
  have h1 := integral_tsum_of_summable_integral_norm hFi hint
  have hsx : ∀ x, Summable fun p => F p x := fun x =>
    Summable.of_norm_bounded hM fun p => by simpa [Real.norm_eq_abs] using hg p.1 p.2.1 p.2.2 x
  have hsi : Summable fun p => ∫ x, F p x ∂μ :=
    Summable.of_norm_bounded hM fun p => by
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := F p) (C := M * b p.1 * b p.2.1 * b p.2.2)
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hg p.1 p.2.1 p.2.2 x)
      simpa using this
  have e1 : ∀ x, ∑' p, F p x = ∑' k, ∑' l, ∑' j, g k l j x := fun x =>
    s7e_tsum_triple (fun p => F p x) (hsx x)
  have e2 : ∑' p, ∫ x, F p x ∂μ = ∑' k, ∑' l, ∑' j, ∫ x, g k l j x ∂μ :=
    s7e_tsum_triple (fun p => ∫ x, F p x ∂μ) hsi
  rw [← e2, h1]
  exact integral_congr_ae (Eventually.of_forall fun x => (e1 x).symm)

end HRS.MC.Sec7.S7e

end
