import HRS.MS.S111K4T2

/-!
# S11.1 / T03 (S11K4), Pro `R26-T6.E04`: derivative of a triple integral of `L²`-differentiable bounded functions
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111K4

variable {X : Type*} [MeasurableSpace X]

theorem k4_triple_derivative (μ : Measure X) [IsProbabilityMeasure μ]
    (h : Fin 3 → ℝ → X → ℝ) (dh : Fin 3 → X → ℝ) (v B : ℝ) (hB : 0 ≤ B)
    (hm : ∀ i q, MemLp (h i q) 2 μ) (hdm : ∀ i, MemLp (dh i) 2 μ)
    (hder : ∀ i, HasDerivAt (fun q => (hm i q).toLp (h i q)) ((hdm i).toLp (dh i)) v)
    (hbdd : ∀ᶠ q in 𝓝 v, ∀ i, ∀ᵐ x ∂μ, |h i q x| ≤ B) :
    HasDerivAt (fun q => ∫ x, h 0 q x * h 1 q x * h 2 q x ∂μ)
      (∑ i : Fin 3, ∫ x, dh i x * h (i + 1) v x * h (i + 2) v x ∂μ) v := by
  have hder' : ∀ i, HasDerivAt (fun q => k4_toL μ (h i q)) (k4_toL μ (dh i)) v := by
    intro i
    have e1 : (fun q => k4_toL μ (h i q)) = fun q => (hm i q).toLp (h i q) := by
      funext q; exact k4_toL_eq (hm i q)
    rw [e1, k4_toL_eq (hdm i)]
    exact hder i
  have hslope : ∀ i, Tendsto (slope (fun q => k4_toL μ (h i q)) v) (𝓝[≠] v) (𝓝 (k4_toL μ (dh i))) :=
    fun i => hasDerivAt_iff_tendsto_slope.1 (hder' i)
  have hcont : ∀ i, Tendsto (fun q => k4_toL μ (h i q)) (𝓝 v) (𝓝 (k4_toL μ (h i v))) :=
    fun i => (hder' i).continuousAt
  have hbv : ∀ i, ∀ᵐ x ∂μ, |h i v x| ≤ B := fun i => hbdd.self_of_nhds i
  -- the product classes
  set P0 : ℝ → Lp ℝ 2 μ := fun q => k4_toL μ (fun x => h 1 q x * h 2 q x) with hP0
  set P1 : ℝ → Lp ℝ 2 μ := fun q => k4_toL μ (fun x => h 0 v x * h 2 q x) with hP1
  set P2 : Lp ℝ 2 μ := k4_toL μ (fun x => h 0 v x * h 1 v x) with hP2
  have hP0c : Tendsto P0 (𝓝 v) (𝓝 (P0 v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ q in 𝓝 v, ‖P0 q - P0 v‖ ≤ B * ‖k4_toL μ (h 1 q) - k4_toL μ (h 1 v)‖ +
        B * ‖k4_toL μ (h 2 q) - k4_toL μ (h 2 v)‖ := by
      filter_upwards [hbdd] with q hq
      exact k4_prod_diff_norm hB (hm 1 v) (hm 1 q) (hm 2 v) (hm 2 q) (hbv 1) (hq 2)
    have hz : Tendsto (fun q => B * ‖k4_toL μ (h 1 q) - k4_toL μ (h 1 v)‖ +
        B * ‖k4_toL μ (h 2 q) - k4_toL μ (h 2 v)‖) (𝓝 v) (𝓝 0) := by
      have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 (hcont 1)).const_mul B
      have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 (hcont 2)).const_mul B
      simpa using h1.add h2
    exact squeeze_zero' (Filter.Eventually.of_forall fun q => norm_nonneg _) hb hz
  have hP1c : Tendsto P1 (𝓝 v) (𝓝 (P1 v)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ q in 𝓝 v, ‖P1 q - P1 v‖ ≤ B * ‖k4_toL μ (h 2 q) - k4_toL μ (h 2 v)‖ := by
      filter_upwards [hbdd] with q hq
      have := k4_prod_diff_norm hB (a := h 0 v) (a' := h 0 v) (b := h 2 v) (b' := h 2 q)
        (hm 0 v) (hm 0 v) (hm 2 v) (hm 2 q) (hbv 0) (hq 2)
      simpa using this
    have hz : Tendsto (fun q => B * ‖k4_toL μ (h 2 q) - k4_toL μ (h 2 v)‖) (𝓝 v) (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.1 (hcont 2)).const_mul B
    exact squeeze_zero' (Filter.Eventually.of_forall fun q => norm_nonneg _) hb hz
  -- the slope identity
  have hsl : ∀ᶠ q in 𝓝[≠] v, slope (fun q => ∫ x, h 0 q x * h 1 q x * h 2 q x ∂μ) v q =
      inner ℝ (slope (fun q => k4_toL μ (h 0 q)) v q) (P0 q) +
      inner ℝ (slope (fun q => k4_toL μ (h 1 q)) v q) (P1 q) +
      inner ℝ (slope (fun q => k4_toL μ (h 2 q)) v q) P2 := by
    have hev : ∀ᶠ q in 𝓝[≠] v, ∀ i, ∀ᵐ x ∂μ, |h i q x| ≤ B := nhdsWithin_le_nhds hbdd
    filter_upwards [hev] with q hq
    have hsl' : ∀ i, slope (fun q => k4_toL μ (h i q)) v q =
        k4_toL μ (fun x => (q - v)⁻¹ * (h i q x - h i v x)) := fun i => by
      rw [slope_def_module, k4_toL_combo _ (hm i q) (hm i v)]
    have mS : ∀ i, MemLp (fun x => (q - v)⁻¹ * (h i q x - h i v x)) 2 μ := fun i =>
      ((hm i q).sub (hm i v)).const_mul _
    have m0 : MemLp (fun x => h 1 q x * h 2 q x) 2 μ := k4_mul_memLp (hm 2 q) (hm 1 q).aestronglyMeasurable (hq 1)
    have m1 : MemLp (fun x => h 0 v x * h 2 q x) 2 μ := k4_mul_memLp (hm 2 q) (hm 0 v).aestronglyMeasurable (hbv 0)
    have m2 : MemLp (fun x => h 0 v x * h 1 v x) 2 μ := k4_mul_memLp (hm 1 v) (hm 0 v).aestronglyMeasurable (hbv 0)
    rw [hsl', hsl', hsl', k4_inner_toL (mS 0) m0, k4_inner_toL (mS 1) m1, k4_inner_toL (mS 2) m2]
    have iA : Integrable (fun x => (q - v)⁻¹ * (h 0 q x - h 0 v x) * (h 1 q x * h 2 q x)) μ := (mS 0).integrable_mul m0
    have iB : Integrable (fun x => (q - v)⁻¹ * (h 1 q x - h 1 v x) * (h 0 v x * h 2 q x)) μ := (mS 1).integrable_mul m1
    have iC : Integrable (fun x => (q - v)⁻¹ * (h 2 q x - h 2 v x) * (h 0 v x * h 1 v x)) μ := (mS 2).integrable_mul m2
    have iFq : Integrable (fun x => h 0 q x * h 1 q x * h 2 q x) μ :=
      ((hm 0 q).integrable_mul m0).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    have iFv : Integrable (fun x => h 0 v x * h 1 v x * h 2 v x) μ := by
      have m0v : MemLp (fun x => h 1 v x * h 2 v x) 2 μ := k4_mul_memLp (hm 2 v) (hm 1 v).aestronglyMeasurable (hbv 1)
      exact ((hm 0 v).integrable_mul m0v).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    have iAB : Integrable (fun x => (q - v)⁻¹ * (h 0 q x - h 0 v x) * (h 1 q x * h 2 q x) +
        (q - v)⁻¹ * (h 1 q x - h 1 v x) * (h 0 v x * h 2 q x)) μ := iA.add iB
    rw [slope_def_module, ← integral_add iA iB, ← integral_add iAB iC]
    have e : ∀ x, (q - v)⁻¹ * (h 0 q x - h 0 v x) * (h 1 q x * h 2 q x) +
        (q - v)⁻¹ * (h 1 q x - h 1 v x) * (h 0 v x * h 2 q x) +
        (q - v)⁻¹ * (h 2 q x - h 2 v x) * (h 0 v x * h 1 v x) =
        (q - v)⁻¹ * (h 0 q x * h 1 q x * h 2 q x - h 0 v x * h 1 v x * h 2 v x) := fun x => by ring
    simp_rw [e]
    rw [integral_const_mul, integral_sub iFq iFv, smul_eq_mul]
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum := ((Filter.Tendsto.inner (𝕜 := ℝ) (hslope 0) (hP0c.mono_left nhdsWithin_le_nhds)).add
    (Filter.Tendsto.inner (𝕜 := ℝ) (hslope 1) (hP1c.mono_left nhdsWithin_le_nhds))).add
    (Filter.Tendsto.inner (𝕜 := ℝ) (hslope 2) (tendsto_const_nhds (x := P2)))
  have hlim : inner ℝ (k4_toL μ (dh 0)) (P0 v) + inner ℝ (k4_toL μ (dh 1)) (P1 v) +
      inner ℝ (k4_toL μ (dh 2)) P2 = ∑ i : Fin 3, ∫ x, dh i x * h (i + 1) v x * h (i + 2) v x ∂μ := by
    have m0v : MemLp (fun x => h 1 v x * h 2 v x) 2 μ := k4_mul_memLp (hm 2 v) (hm 1 v).aestronglyMeasurable (hbv 1)
    have m1v : MemLp (fun x => h 0 v x * h 2 v x) 2 μ := k4_mul_memLp (hm 2 v) (hm 0 v).aestronglyMeasurable (hbv 0)
    have m2v : MemLp (fun x => h 0 v x * h 1 v x) 2 μ := k4_mul_memLp (hm 1 v) (hm 0 v).aestronglyMeasurable (hbv 0)
    simp only [hP0, hP1, hP2, k4_inner_toL (hdm 0) m0v, k4_inner_toL (hdm 1) m1v, k4_inner_toL (hdm 2) m2v,
      Fin.sum_univ_three]
    have e1 : ((0 : Fin 3) + 1 = 1) ∧ ((0 : Fin 3) + 2 = 2) ∧ ((1 : Fin 3) + 1 = 2) ∧ ((1 : Fin 3) + 2 = 0) ∧
      ((2 : Fin 3) + 1 = 0) ∧ ((2 : Fin 3) + 2 = 1) := by decide
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := e1
    rw [a1, a2, a3, a4, a5, a6]
    have c0 : ∫ x, dh 0 x * (h 1 v x * h 2 v x) ∂μ = ∫ x, dh 0 x * h 1 v x * h 2 v x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have c1 : ∫ x, dh 1 x * (h 0 v x * h 2 v x) ∂μ = ∫ x, dh 1 x * h 2 v x * h 0 v x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    have c2 : ∫ x, dh 2 x * (h 0 v x * h 1 v x) ∂μ = ∫ x, dh 2 x * h 0 v x * h 1 v x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [c0, c1, c2]
  rw [← hlim]
  exact hsum.congr' (hsl.mono fun q hq => hq.symm)

end HRS.MS.S111K4
