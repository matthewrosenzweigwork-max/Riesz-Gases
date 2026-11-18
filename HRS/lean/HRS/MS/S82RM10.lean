import HRS.MS.S82RM9

/-!
# S8.2 R02 (S82R), M10: one supersolution step
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_Gam_bdd_int {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    {ρ : E → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρi : Integrable ρ μ) (z : E) :
    |s82r_Gam μ Γ ρ z| ≤ G0 * ∫ u, ρ u ∂μ := by
  rw [abs_of_nonneg (s82r_Gam_nonneg hΓ0 hρ0 z)]
  have hf : Integrable (fun u => ρ u * Γ u z) μ :=
    Integrable.mono' (hρi.mul_const G0) ((hρ.mul (hΓ.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 u) (hΓ0 u z))]
        exact mul_le_mul_of_nonneg_left (hG0 u z) (hρ0 u))
  unfold s82r_Gam
  calc ∫ u, ρ u * Γ u z ∂μ ≤ ∫ u, ρ u * G0 ∂μ :=
        integral_mono hf (hρi.mul_const G0) fun u => mul_le_mul_of_nonneg_left (hG0 u z) (hρ0 u)
    _ = G0 * ∫ u, ρ u ∂μ := by rw [integral_mul_const]; ring

lemma s82r_super_step [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    {b : E → ℝ} (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {G0 : ℝ}
    (hG0 : ∀ z u, Γ z u ≤ G0) (hsym : ∀ z u, Γ z u = Γ u z) (hbm : Measurable b)
    (hb0 : ∀ z, 0 ≤ b z) {Bb : ℝ} (hBb : ∀ z, b z ≤ Bb)
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) {ρ : E → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρi : Integrable ρ μ)
    (hsup : ∀ᵐ z ∂μ, (1 - 1 / (n : ℝ)) * ρ z + (((n : ℝ) - 1) / n) * s82r_Gam μ Γ ρ z ≤
      ρ z - (1 / (n : ℝ)) * b z) :
    (1 / (n : ℝ)) * ∑ i, ∫ z, W i z * b z ∂μ + ∑ i, ∫ z, s82r_Sw μ Γ n W i z * ρ z ∂μ ≤
      ∑ i, ∫ z, W i z * ρ z ∂μ := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  choose B hB using hW.bdd
  have hWρ : ∀ i, Integrable (fun z => W i z * ρ z) μ := fun i =>
    (hρi.bdd_mul (c := B i) (hW.meas i).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hW.nonneg i z)]; exact hB i z))
  have hWb : ∀ i, Integrable (fun z => W i z * b z) μ := fun i =>
    Integrable.of_bound ((hW.meas i).mul hbm).aestronglyMeasurable (B i * Bb) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW.nonneg i z) (hb0 z))]
      exact mul_le_mul (hB i z) (hBb z) (hb0 z) ((hW.nonneg i z).trans (hB i z)))
  have hGρm : Measurable (s82r_Gam μ Γ ρ) := s82r_Gam_meas hΓ hρ
  have hWGρ : ∀ i, Integrable (fun z => W i z * s82r_Gam μ Γ ρ z) μ := fun i =>
    Integrable.of_bound ((hW.meas i).mul hGρm).aestronglyMeasurable (B i * (G0 * ∫ u, ρ u ∂μ))
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hW.nonneg i z) (s82r_Gam_nonneg hΓ0 hρ0 z))]
        exact mul_le_mul (hB i z) ((le_abs_self _).trans (s82r_Gam_bdd_int hΓ hΓ0 hG0 hρ hρ0 hρi z))
          (s82r_Gam_nonneg hΓ0 hρ0 z) ((hW.nonneg i z).trans (hB i z)))
  have hGWρ : ∀ i, Integrable (fun u => s82r_Gam μ Γ (W i) u * ρ u) μ := fun i =>
    hρi.bdd_mul (c := B i * G0) (s82r_Gam_meas hΓ (hW.meas i)).aestronglyMeasurable
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs]
        exact s82r_Gam_bdd (μ := μ) hΓ hΓ0 hG0 (hW.meas i) (hW.nonneg i) (hB i) u)
  -- ∫ (S W)_ℓ ρ
  have hSW : ∀ ℓ, ∫ z, s82r_Sw μ Γ n W ℓ z * ρ z ∂μ =
      (1 - 1 / (n : ℝ)) * ∫ z, W ℓ z * ρ z ∂μ + (1 / (n : ℝ)) *
        ∑ i ∈ Finset.univ.erase ℓ, ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ := by
    intro ℓ
    have e : ∀ z, s82r_Sw μ Γ n W ℓ z * ρ z = (1 - 1 / (n : ℝ)) * (W ℓ z * ρ z) +
        (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.erase ℓ, s82r_Gam μ Γ (W i) z * ρ z := by
      intro z
      have h := Finset.sum_mul (Finset.univ.erase ℓ) (fun i => s82r_Gam μ Γ (W i) z) (ρ z)
      unfold s82r_Sw
      rw [← h]; ring
    simp_rw [e]
    rw [integral_add ((hWρ ℓ).const_mul _) ((integrable_finset_sum _ fun i _ => hGWρ i).const_mul _),
      integral_const_mul, integral_const_mul, integral_finset_sum _ fun i _ => hGWρ i]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    exact s82r_Gam_pair hΓ hΓ0 hG0 hsym (hW.meas i) (hW.nonneg i) (hB i) hρ hρ0 hρi
  have hswap : ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ =
      ((n : ℝ) - 1) * ∑ i, ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ := by
    have hs : ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ =
        ∑ i : Fin n, ∑ ℓ ∈ Finset.univ.erase i, ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ := by
      refine Finset.sum_comm' fun i ℓ => ?_
      simp [Finset.mem_erase, eq_comm, and_comm]
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [Nat.cast_sub this]; simp
  have hsumS : ∑ i, ∫ z, s82r_Sw μ Γ n W i z * ρ z ∂μ =
      (1 - 1 / (n : ℝ)) * ∑ i, ∫ z, W i z * ρ z ∂μ + (((n : ℝ) - 1) / n) *
        ∑ i, ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ := by
    simp_rw [hSW]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hswap]
    field_simp
  rw [hsumS]
  have hpt : ∀ i, (1 - 1 / (n : ℝ)) * ∫ z, W i z * ρ z ∂μ + (((n : ℝ) - 1) / n) *
      ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ + (1 / (n : ℝ)) * ∫ z, W i z * b z ∂μ ≤
      ∫ z, W i z * ρ z ∂μ := by
    intro i
    have h1 : ∫ z, W i z * ((1 - 1 / (n : ℝ)) * ρ z + (((n : ℝ) - 1) / n) * s82r_Gam μ Γ ρ z +
        (1 / (n : ℝ)) * b z) ∂μ ≤ ∫ z, W i z * ρ z ∂μ :=
      integral_mono_ae (((((hWρ i).const_mul (1 - 1 / (n : ℝ))).add ((hWGρ i).const_mul (((n : ℝ) - 1) / n))).add
        ((hWb i).const_mul (1 / (n : ℝ)))).congr (ae_of_all _ fun z => by simp only [Pi.add_apply]; ring))
        (hWρ i) (by filter_upwards [hsup] with z hz
                    exact mul_le_mul_of_nonneg_left (by linarith [hz]) (hW.nonneg i z))
    have hA : Integrable (fun z => (1 - 1 / (n : ℝ)) * (W i z * ρ z)) μ := (hWρ i).const_mul _
    have hB' : Integrable (fun z => (((n : ℝ) - 1) / n) * (W i z * s82r_Gam μ Γ ρ z)) μ :=
      (hWGρ i).const_mul _
    have hC : Integrable (fun z => (1 / (n : ℝ)) * (W i z * b z)) μ := (hWb i).const_mul _
    have hAB : Integrable (fun z => (1 - 1 / (n : ℝ)) * (W i z * ρ z) +
        (((n : ℝ) - 1) / n) * (W i z * s82r_Gam μ Γ ρ z)) μ := hA.add hB'
    have e : ∫ z, W i z * ((1 - 1 / (n : ℝ)) * ρ z + (((n : ℝ) - 1) / n) * s82r_Gam μ Γ ρ z +
        (1 / (n : ℝ)) * b z) ∂μ = (1 - 1 / (n : ℝ)) * ∫ z, W i z * ρ z ∂μ + (((n : ℝ) - 1) / n) *
        ∫ z, W i z * s82r_Gam μ Γ ρ z ∂μ + (1 / (n : ℝ)) * ∫ z, W i z * b z ∂μ := by
      have e0 : ∫ z, W i z * ((1 - 1 / (n : ℝ)) * ρ z + (((n : ℝ) - 1) / n) * s82r_Gam μ Γ ρ z +
          (1 / (n : ℝ)) * b z) ∂μ = ∫ z, ((1 - 1 / (n : ℝ)) * (W i z * ρ z) +
          (((n : ℝ) - 1) / n) * (W i z * s82r_Gam μ Γ ρ z) + (1 / (n : ℝ)) * (W i z * b z)) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        ring
      rw [e0, integral_add hAB hC, integral_add hA hB', integral_const_mul, integral_const_mul,
        integral_const_mul]
    linarith
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at this
  linarith

end HRS.MS.S82R

end
