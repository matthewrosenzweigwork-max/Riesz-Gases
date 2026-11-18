import HRS.Commutator.Whole.XLIAux31

/-!
# X-LI part 32: the good function of the Calderón–Zygmund decomposition
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma good_function {ι : Type*} [Countable ι] (F : 𝔼 → ℂ) (hF : Measurable F) (hFi : Integrable F)
    (E : ι → Set 𝔼) (hEm : ∀ i, MeasurableSet (E i)) (hEd : Pairwise (Function.onFun Disjoint E))
    (hE0 : ∀ i, volume (E i) ≠ 0) (hEt : ∀ i, volume (E i) ≠ ⊤) {l M : ℝ≥0∞} (hlM : l ≤ M)
    (hav : ∀ i, (volume (E i))⁻¹ * ∫⁻ y in E i, ‖F y‖ₑ ≤ M) :
    ∃ g : 𝔼 → ℂ, Measurable g ∧ (∀ x, ‖g x‖ₑ ≤ M) ∧ ∫⁻ x, ‖g x‖ₑ ≤ ∫⁻ x, ‖F x‖ₑ ∧
      (∀ i, ∫ y in E i, (F y - g y) = 0) ∧
      (∀ x, x ∉ ⋃ i, E i → ‖F x‖ₑ ≤ l → g x = F x) := by
  classical
  set a : ι → ℂ := fun i => ((volume (E i)).toReal)⁻¹ • ∫ y in E i, F y with ha
  set g₂ : 𝔼 → ℂ := fun x => if ‖F x‖ₑ ≤ l then F x else 0 with hg₂
  set Ω : Set 𝔼 := ⋃ i, E i with hΩ
  have hΩm : MeasurableSet Ω := MeasurableSet.iUnion hEm
  set g : 𝔼 → ℂ := fun x => if h : ∃ i, x ∈ E i then a (Classical.choose h) else g₂ x with hg
  have hgE : ∀ i, ∀ x ∈ E i, g x = a i := by
    intro i x hx
    have h : ∃ i, x ∈ E i := ⟨i, hx⟩
    have hspec := Classical.choose_spec h
    have : Classical.choose h = i := by
      by_contra hne
      exact Set.disjoint_left.1 (hEd hne) hspec hx
    simp only [hg, dif_pos h, this]
  have hgout : ∀ x, x ∉ Ω → g x = g₂ x := by
    intro x hx
    have h : ¬ ∃ i, x ∈ E i := by
      intro ⟨i, hi⟩; exact hx (mem_iUnion.2 ⟨i, hi⟩)
    simp only [hg, dif_neg h]
  have hg₂m : Measurable g₂ := by
    refine Measurable.ite ?_ hF measurable_const
    exact measurableSet_le hF.enorm measurable_const
  have hgm : Measurable g := by
    have : g = fun x => (∑' i, (E i).indicator (fun _ => a i) x) + Ωᶜ.indicator g₂ x := by
      funext x
      by_cases hx : x ∈ Ω
      · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
        rw [Set.indicator_of_notMem (by simpa using hx), add_zero, tsum_eq_single i, 
          Set.indicator_of_mem hi, hgE i x hi]
        intro k hk
        rw [Set.indicator_of_notMem]
        intro hxk
        exact Set.disjoint_left.1 (hEd hk) hxk hi
      · rw [hgout x hx, Set.indicator_of_mem (by simpa using hx)]
        have : ∀ i, (E i).indicator (fun _ => a i) x = 0 := fun i =>
          Set.indicator_of_notMem (fun hxi => hx (mem_iUnion.2 ⟨i, hxi⟩)) _
        simp [this]
    rw [this]
    refine Measurable.add (Measurable.tsum fun i => ?_) (hg₂m.indicator hΩm.compl)
    exact measurable_const.indicator (hEm i)
  have hav' : ∀ i, ‖a i‖ₑ * volume (E i) = ‖∫ y in E i, F y‖ₑ := by
    intro i
    rw [ha]
    simp only [enorm_smul]
    have hv0 : (volume (E i)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hE0 i, hEt i⟩
    have : ‖((volume (E i)).toReal)⁻¹‖ₑ = (volume (E i))⁻¹ := by
      rw [enorm_inv hv0, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hEt i)]
    rw [this, mul_assoc, mul_comm _ (volume (E i)), ← mul_assoc, ENNReal.inv_mul_cancel (hE0 i) (hEt i),
      one_mul]
  have haE : ∀ i, ‖a i‖ₑ ≤ M := by
    intro i
    have h1 : ‖a i‖ₑ = (volume (E i))⁻¹ * ‖∫ y in E i, F y‖ₑ := by
      have := hav' i
      rw [← this, mul_comm (‖a i‖ₑ), ← mul_assoc, ENNReal.inv_mul_cancel (hE0 i) (hEt i), one_mul]
    rw [h1]
    refine le_trans ?_ (hav i)
    exact mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
  have hbd : ∀ x, ‖g x‖ₑ ≤ M := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      rw [hgE i x hi]; exact haE i
    · rw [hgout x hx, hg₂]
      simp only
      split_ifs with h
      · exact h.trans hlM
      · simp
  have hmean : ∀ i, ∫ y in E i, (F y - g y) = 0 := by
    intro i
    have hv0 : (volume (E i)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hE0 i, hEt i⟩
    have hgint : IntegrableOn g (E i) := by
      have : IntegrableOn (fun _ : 𝔼 => a i) (E i) := integrableOn_const (hEt i)
      exact this.congr_fun (fun y hy => (hgE i y hy).symm) (hEm i)
    rw [integral_sub hFi.integrableOn hgint]
    have : ∫ y in E i, g y = ∫ y in E i, a i := setIntegral_congr_fun (hEm i) (fun y hy => hgE i y hy)
    rw [this, setIntegral_const]
    simp only [ha, Measure.real, smul_smul]
    rw [mul_inv_cancel₀ hv0, one_smul, sub_self]
  have hint : ∫⁻ x, ‖g x‖ₑ ≤ ∫⁻ x, ‖F x‖ₑ := by
    rw [← lintegral_add_compl (fun x => ‖g x‖ₑ) hΩm, ← lintegral_add_compl (fun x => ‖F x‖ₑ) hΩm]
    refine add_le_add ?_ ?_
    · rw [hΩ, lintegral_iUnion hEm hEd, lintegral_iUnion hEm hEd]
      refine ENNReal.tsum_le_tsum fun i => ?_
      rw [setLIntegral_congr_fun (hEm i) (fun y hy => by rw [hgE i y hy]), setLIntegral_const, hav' i]
      exact enorm_integral_le_lintegral_enorm _
    · refine setLIntegral_mono' hΩm.compl fun x hx => ?_
      rw [hgout x hx, hg₂]
      simp only
      split_ifs <;> simp
  refine ⟨g, hgm, hbd, hint, hmean, fun x hx hxl => ?_⟩
  rw [hgout x hx, hg₂]
  simp only [if_pos hxl]

lemma enorm_add_sq_le (v w : ℂ) : ‖v + w‖ₑ ^ 2 ≤ 2 * ‖v‖ₑ ^ 2 + 2 * ‖w‖ₑ ^ 2 := by
  have h1 : ‖v + w‖ₑ ≤ ‖v‖ₑ + ‖w‖ₑ := enorm_add_le _ _
  have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖v‖ₑ ‖w‖ₑ (p := 2) (by norm_num)
  calc ‖v + w‖ₑ ^ 2 ≤ (‖v‖ₑ + ‖w‖ₑ) ^ 2 := by gcongr
    _ = (‖v‖ₑ + ‖w‖ₑ) ^ (2 : ℝ) := by rw [ENNReal.rpow_two]
    _ ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) * (‖v‖ₑ ^ (2 : ℝ) + ‖w‖ₑ ^ (2 : ℝ)) := h2
    _ = 2 * ‖v‖ₑ ^ 2 + 2 * ‖w‖ₑ ^ 2 := by
        norm_num [ENNReal.rpow_two]
        ring

lemma sqS_add_le (a b c : ℤ → 𝔼 → ℂ) (h : ∀ j x, a j x = b j x + c j x) (x : 𝔼) :
    sqS a x ≤ 2 * sqS b x + 2 * sqS c x := by
  unfold sqS
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [h j x]
  exact enorm_add_sq_le _ _

lemma sqS_le_sq_tsum (f : ℤ → 𝔼 → ℂ) (x : 𝔼) : sqS f x ≤ (∑' j, ‖f j x‖ₑ) ^ 2 := by
  unfold sqS
  set S : ℝ≥0∞ := ∑' j, ‖f j x‖ₑ with hS
  calc ∑' j, ‖f j x‖ₑ ^ 2 ≤ ∑' j, ‖f j x‖ₑ * S := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [pow_two]
        exact mul_le_mul_right (ENNReal.le_tsum (f := fun j => ‖f j x‖ₑ) j) _
    _ = S * S := by rw [ENNReal.tsum_mul_right]
    _ = S ^ 2 := (pow_two S).symm

end HRS.Commutator.Whole.XLI
