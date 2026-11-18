import HRS.MS.S82RM7

/-!
# S8.2 R02 (S82R), M8: the weight recursion preserves admissibility and decays in sup norm
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_Gam_meas {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) {w : E → ℝ} (hw : Measurable w) :
    Measurable (s82r_Gam μ Γ w) := by
  have hf : Measurable (fun p : E × E => w p.2 * Γ p.2 p.1) :=
    (hw.comp measurable_snd).mul (hΓ.comp (measurable_snd.prodMk measurable_fst))
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma s82r_Gam_nonneg {μ : Measure E} {Γ : E → E → ℝ} (hΓ0 : ∀ z u, 0 ≤ Γ z u) {w : E → ℝ}
    (hw0 : ∀ z, 0 ≤ w z) (u : E) : 0 ≤ s82r_Gam μ Γ w u :=
  integral_nonneg fun z => mul_nonneg (hw0 z) (hΓ0 z u)

lemma s82r_Gam_le {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {θ : ℝ}
    (hθ : ∀ u, ∫ z, Γ z u ∂μ ≤ θ) {w : E → ℝ} (hw : Measurable w) (hw0 : ∀ z, 0 ≤ w z) {B : ℝ}
    (hwB : ∀ z, w z ≤ B) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0) (u : E) :
    s82r_Gam μ Γ w u ≤ B * θ := by
  have hΓi : Integrable (fun z => Γ z u) μ :=
    Integrable.of_bound (hΓ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable G0
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hΓ0 z u)]; exact hG0 z u)
  have hwΓ : Integrable (fun z => w z * Γ z u) μ :=
    Integrable.of_bound (hw.mul (hΓ.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
      (B * G0) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 z) (hΓ0 z u))]
        exact mul_le_mul (hwB z) (hG0 z u) (hΓ0 z u) ((hw0 z).trans (hwB z)))
  unfold s82r_Gam
  calc ∫ z, w z * Γ z u ∂μ ≤ ∫ z, B * Γ z u ∂μ :=
        integral_mono hwΓ (hΓi.const_mul B) fun z => mul_le_mul_of_nonneg_right (hwB z) (hΓ0 z u)
    _ = B * ∫ z, Γ z u ∂μ := integral_const_mul _ _
    _ ≤ B * θ := mul_le_mul_of_nonneg_left (hθ u) ((hw0 u).trans (hwB u))


/-- Admissibility is preserved by the weight recursion. -/
lemma s82r_Sw_ok [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {θ : ℝ}
    (hθ : ∀ u, ∫ z, Γ z u ∂μ ≤ θ) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) : s82r_WOK (s82r_Sw μ Γ n W) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hc0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hn
  have hc1 : 0 ≤ 1 / (n : ℝ) := by positivity
  refine ⟨fun ℓ => ?_, fun ℓ u => ?_, fun ℓ => ?_⟩
  · unfold s82r_Sw
    exact ((hW.meas ℓ).const_mul _).add
      ((Finset.measurable_sum _ fun i _ => s82r_Gam_meas hΓ (hW.meas i)).const_mul _)
  · unfold s82r_Sw
    exact add_nonneg (mul_nonneg hc0 (hW.nonneg ℓ u)) (mul_nonneg hc1 (Finset.sum_nonneg fun i _ =>
      s82r_Gam_nonneg hΓ0 (hW.nonneg i) u))
  · choose B hB using hW.bdd
    refine ⟨(1 - 1 / (n : ℝ)) * B ℓ + (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.erase ℓ, B i * θ, fun u => ?_⟩
    unfold s82r_Sw
    refine add_le_add (mul_le_mul_of_nonneg_left (hB ℓ u) hc0) (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => s82r_Gam_le hΓ hΓ0 hθ (hW.meas i) (hW.nonneg i) (hB i) hG0 u) hc1)

/-- Sup-norm decay of the weight recursion (sum of the per-site bounds). -/
lemma s82r_Sw_decay [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ u, ∫ z, Γ z u ∂μ ≤ θ) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) {B : Fin n → ℝ} (hB0 : ∀ ℓ, 0 ≤ B ℓ)
    (hB : ∀ ℓ z, W ℓ z ≤ B ℓ) :
    ∃ B' : Fin n → ℝ, (∀ ℓ, 0 ≤ B' ℓ) ∧ (∀ ℓ z, s82r_Sw μ Γ n W ℓ z ≤ B' ℓ) ∧
      ∑ ℓ, B' ℓ ≤ (1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ) * ∑ ℓ, B ℓ := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hc0 : 0 ≤ 1 - 1 / (n : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hn
  have hc1 : 0 ≤ 1 / (n : ℝ) := by positivity
  refine ⟨fun ℓ => (1 - 1 / (n : ℝ)) * B ℓ + (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.erase ℓ, B i * θ,
    fun ℓ => add_nonneg (mul_nonneg hc0 (hB0 ℓ)) (mul_nonneg hc1 (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hB0 i) hθ0)), fun ℓ u => ?_, ?_⟩
  · unfold s82r_Sw
    refine add_le_add (mul_le_mul_of_nonneg_left (hB ℓ u) hc0) (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ => s82r_Gam_le hΓ hΓ0 hθ (hW.meas i) (hW.nonneg i) (hB i) hG0 u) hc1)
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hswap : ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, B i * θ =
        ∑ i : Fin n, ∑ ℓ ∈ Finset.univ.erase i, B i * θ := by
      refine Finset.sum_comm' fun i ℓ => ?_
      simp [Finset.mem_erase, eq_comm, and_comm]
    rw [hswap]
    have hcard : ((Finset.univ.erase (0 : Fin n)).card : ℝ) = (n : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      have : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
      rw [Nat.cast_sub this]; simp
    have hc : ∀ i : Fin n, ∑ ℓ ∈ Finset.univ.erase i, B i * θ = ((n : ℝ) - 1) * (B i * θ) := by
      intro i
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      have : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
      rw [Nat.cast_sub this]; simp
    simp_rw [hc]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have : (1 - 1 / (n : ℝ)) * ∑ ℓ, B ℓ + 1 / (n : ℝ) * (((n : ℝ) - 1) * ((∑ i, B i) * θ)) =
        (1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ) * ∑ ℓ, B ℓ := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [this]

end HRS.MS.S82R

end
