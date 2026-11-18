import HRS.Uniform.Q45Core1

/-!
# Q45: closeness of the Riemann-sum approximants to the node values of the convolution
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma aemeasurable_rsum {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {κ : ℕ} (hκ : 1 ≤ κ)
    (S : EvolData H E) {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (i : Fin (g + 1)) : AEMeasurable (rsum S T g κ M i) P := by
  have hfun : rsum S T g κ M i = fun ω => ∑ k ∈ Finset.range (i * κ),
      S.VE (unifPart T g i) (rr (g * κ) T k)
        (S.j (M (rr (g * κ) T (k + 1)) ω - M (rr (g * κ) T k) ω)) := rfl
  rw [hfun]
  refine Finset.aemeasurable_fun_sum (f := fun k ω => S.VE (unifPart T g i) (rr (g * κ) T k)
        (S.j (M (rr (g * κ) T (k + 1)) ω - M (rr (g * κ) T k) ω))) _ fun k hk => ?_
  have hk' : k < i * κ := Finset.mem_range.1 hk
  have hik : (i : ℕ) * κ ≤ g * κ := Nat.mul_le_mul_right κ (Nat.lt_succ_iff.1 i.2)
  have hmem : ∀ j : ℕ, j ≤ g * κ → rr (g * κ) T j ∈ Set.Icc (0 : ℝ) T := fun j hj =>
    ⟨unifPart_nonneg hT.le _ _, unifPart_le hT.le hj⟩
  have h1 : AEMeasurable (M (rr (g * κ) T (k + 1))) P :=
    (hM.sq_int _ (hmem (k + 1) (by omega))).aestronglyMeasurable.aemeasurable
  have h0 : AEMeasurable (M (rr (g * κ) T k)) P :=
    (hM.sq_int _ (hmem k (by omega))).aestronglyMeasurable.aemeasurable
  have hd : AEMeasurable (fun ω => M (rr (g * κ) T (k + 1)) ω - M (rr (g * κ) T k) ω) P := h1.sub h0
  exact (S.VE _ _).continuous.measurable.comp_aemeasurable (S.j.continuous.measurable.comp_aemeasurable hd)

lemma aemeasurable_gridPath {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {κ : ℕ} (hκ : 1 ≤ κ) {d : ℕ}
    (b : Fin d → E) (S : EvolData H E) {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (X₀ : Ω → H) (hX' : Measurable X₀) :
    AEMeasurable (fun ω => hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
      rsum S T g κ M i ω))) P := by
  have : AEMeasurable (fun ω => (fun i : Fin (g + 1) =>
      projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) + rsum S T g κ M i ω))) P :=
    aemeasurable_pi_iff.2 fun i =>
      (continuous_projB b).measurable.comp_aemeasurable
        ((((S.VE _ 0).continuous.comp S.j.continuous).measurable.comp hX').aemeasurable.add
          (aemeasurable_rsum P hT hg hκ S hM i))
  exact (continuous_hatPath hT hg).measurable.comp_aemeasurable this

/-- The pointwise difference of the two grid paths. -/
lemma grid_path_diff_le {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {d : ℕ} (b : Fin d → E)
    (hb : Orthonormal ℝ b) (u z r : Fin (g + 1) → E) :
    ‖hatPath T g (fun i => projB b (u i + z i)) - hatPath T g (fun i => projB b (u i + r i))‖ ≤
      ∑ i, ‖z i - r i‖ := by
  rw [← hatPath_sub]
  refine norm_hatPath_le hT hg _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun i => ?_
  simp only [Pi.sub_apply]
  rw [← projB_sub, add_sub_add_left_eq_sub]
  exact (norm_projB_le hb _).trans (Finset.single_le_sum (f := fun j => ‖z j - r j‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ i))

end HRS.Uniform.Q45
