import HRS.Commutator.Whole.XLIAux30

/-!
# X-LI part 31: the weak type `(1,1)` estimate (Calderón–Zygmund) — the bad part
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma enorm_tsum_le_of_hasSum {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasSum f a) :
    ‖a‖ₑ ≤ ∑' i, ‖f i‖ₑ := by
  have h2 : Tendsto (fun s : Finset ι => ‖∑ i ∈ s, f i‖ₑ) atTop (𝓝 ‖a‖ₑ) := h.enorm
  exact le_of_tendsto' h2 fun s => (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)

/-- the pointwise estimate for the bad part -/
lemma bad_pointwise {ι : Type*} [Countable ι] {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j))
    (hKi : ∀ j, Integrable (K j)) (E : ι → Set 𝔼) (hEm : ∀ i, MeasurableSet (E i))
    (hEd : Pairwise (Function.onFun Disjoint E)) (c : ι → 𝔼) {b : 𝔼 → ℂ} (hbm : Measurable b) (hbi : Integrable b)
    {Bb : ℝ} (hbB : ∀ y, ‖b y‖ ≤ Bb) (hb0 : ∀ᵐ y, y ∉ ⋃ i, E i → b y = 0)
    (hbint : ∀ i, ∫ y in E i, b y = 0) (x : 𝔼) :
    ∑' j, ‖cv (K j) b x‖ₑ ≤
      ∑' i, ∫⁻ y in E i, (∑' j, ‖K j (x - y) - K j (x - c i)‖ₑ) * ‖b y‖ₑ := by
  have hfi : ∀ j, Integrable (fun y => K j (x - y) * b y) := by
    intro j
    refine Integrable.mul_bdd (c := Bb) ((hKi j).comp_sub_left x) hbm.aestronglyMeasurable
      (Eventually.of_forall hbB)
  have hterm : ∀ j, ‖cv (K j) b x‖ₑ ≤ ∑' i, ∫⁻ y in E i, ‖K j (x - y) - K j (x - c i)‖ₑ * ‖b y‖ₑ := by
    intro j
    have h1 : cv (K j) b x = ∫ y, K j (x - y) * b y := by
      rw [cv_apply]
      simpa [sub_sub_cancel] using (integral_sub_left_eq_self (fun y => K j y * b (x - y)) volume x).symm
    have h2 : ∫ y, K j (x - y) * b y = ∫ y in ⋃ i, E i, K j (x - y) * b y := by
      rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
      exact hb0.mono fun y h hy => by rw [h hy, mul_zero]
    have h3 := hasSum_integral_iUnion hEm hEd (hfi j).integrableOn
    rw [h1, h2]
    refine (enorm_tsum_le_of_hasSum h3).trans (ENNReal.tsum_le_tsum fun i => ?_)
    have h4 : ∫ y in E i, K j (x - y) * b y =
        ∫ y in E i, (K j (x - y) - K j (x - c i)) * b y := by
      have h5 : ∫ y in E i, (K j (x - y) - K j (x - c i)) * b y =
          (∫ y in E i, K j (x - y) * b y) - K j (x - c i) * ∫ y in E i, b y := by
        simp only [sub_mul]
        rw [integral_sub (hfi j).integrableOn, integral_const_mul]
        exact (hbi.const_mul (K j (x - c i))).integrableOn
      rw [h5, hbint i]; simp
    rw [h4]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    simp [enorm_mul]
  calc ∑' j, ‖cv (K j) b x‖ₑ
      ≤ ∑' j, ∑' i, ∫⁻ y in E i, ‖K j (x - y) - K j (x - c i)‖ₑ * ‖b y‖ₑ :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑' i, ∑' j, ∫⁻ y in E i, ‖K j (x - y) - K j (x - c i)‖ₑ * ‖b y‖ₑ := ENNReal.tsum_comm
    _ = ∑' i, ∫⁻ y in E i, (∑' j, ‖K j (x - y) - K j (x - c i)‖ₑ) * ‖b y‖ₑ := by
        refine tsum_congr fun i => ?_
        have hm : ∀ j, AEMeasurable (fun y => ‖K j (x - y) - K j (x - c i)‖ₑ * ‖b y‖ₑ)
            (volume.restrict (E i)) := fun j =>
          ((((hKm j).comp (measurable_const.sub measurable_id)).sub measurable_const).enorm.mul
            hbm.enorm).aemeasurable
        rw [← lintegral_tsum hm]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_right]

/-- the Hörmander condition, translated to the centre `c` -/
lemma horm_translate {K : ℤ → 𝔼 → ℂ} {H : ℝ≥0∞} (hH : HormK K H) (c y : 𝔼) {s : ℝ}
    (hs : 2 * ‖y - c‖ ≤ s) :
    ∫⁻ x in {x : 𝔼 | s ≤ ‖x - c‖}, ∑' j, ‖K j (x - y) - K j (x - c)‖ₑ ≤ H := by
  set w : 𝔼 := y - c with hw
  set G : 𝔼 → ℝ≥0∞ := fun z => ∑' j, ‖K j (z - w) - K j z‖ₑ with hG
  have hmeas : MeasurableSet {x : 𝔼 | s ≤ ‖x - c‖} :=
    measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const c))
  have e1 : ∫⁻ x in {x : 𝔼 | s ≤ ‖x - c‖}, ∑' j, ‖K j (x - y) - K j (x - c)‖ₑ =
      ∫⁻ x, ({z : 𝔼 | s ≤ ‖z‖}.indicator G) (x - c) := by
    rw [← lintegral_indicator hmeas]
    refine lintegral_congr fun x => ?_
    by_cases hx : s ≤ ‖x - c‖
    · have h1 : x ∈ {x : 𝔼 | s ≤ ‖x - c‖} := hx
      have h2 : x - c ∈ {z : 𝔼 | s ≤ ‖z‖} := hx
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      simp only [hG, hw, sub_sub_sub_cancel_right]
    · have h1 : x ∉ {x : 𝔼 | s ≤ ‖x - c‖} := hx
      have h2 : x - c ∉ {z : 𝔼 | s ≤ ‖z‖} := hx
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
  rw [e1, lintegral_sub_right_eq_self (μ := volume) ({z : 𝔼 | s ≤ ‖z‖}.indicator G) c]
  have hsub : {z : 𝔼 | s ≤ ‖z‖} ⊆ {z : 𝔼 | 2 * ‖w‖ ≤ ‖z‖} := fun z hz => le_trans hs hz
  calc ∫⁻ z, ({z : 𝔼 | s ≤ ‖z‖}.indicator G) z
      = ∫⁻ z in {z : 𝔼 | s ≤ ‖z‖}, G z := by
        rw [lintegral_indicator (measurableSet_le measurable_const measurable_norm)]
    _ ≤ ∫⁻ z in {z : 𝔼 | 2 * ‖w‖ ≤ ‖z‖}, G z := lintegral_mono_set hsub
    _ ≤ H := hH w

/-- the integral of the bad part away from the enlarged balls -/
lemma bad_integral {ι : Type*} [Countable ι] {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j))
    (hKi : ∀ j, Integrable (K j)) {H : ℝ≥0∞} (hH : HormK K H) (E : ι → Set 𝔼)
    (hEm : ∀ i, MeasurableSet (E i)) (hEd : Pairwise (Function.onFun Disjoint E)) (c : ι → 𝔼)
    (ρ : ι → ℝ) (hρ : ∀ i, ∀ y ∈ E i, ‖y - c i‖ ≤ ρ i) {b : 𝔼 → ℂ} (hbm : Measurable b)
    (hbi : Integrable b) {Bb : ℝ} (hbB : ∀ y, ‖b y‖ ≤ Bb) (hb0 : ∀ᵐ y, y ∉ ⋃ i, E i → b y = 0)
    (hbint : ∀ i, ∫ y in E i, b y = 0) :
    ∫⁻ x in {x : 𝔼 | ∀ i, 2 * ρ i ≤ ‖x - c i‖}, ∑' j, ‖cv (K j) b x‖ₑ ≤
      H * ∫⁻ y in ⋃ i, E i, ‖b y‖ₑ := by
  set A : Set 𝔼 := {x : 𝔼 | ∀ i, 2 * ρ i ≤ ‖x - c i‖} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ i, {x : 𝔼 | 2 * ρ i ≤ ‖x - c i‖} := by
      ext x; simp [hA]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const _))
  have hF : ∀ i, Measurable (fun p : 𝔼 × 𝔼 =>
      (∑' j, ‖K j (p.1 - p.2) - K j (p.1 - c i)‖ₑ) * ‖b p.2‖ₑ) := by
    intro i
    refine (Measurable.tsum fun j => ?_).mul (hbm.comp measurable_snd).enorm
    exact (((hKm j).comp (measurable_fst.sub measurable_snd)).sub
      ((hKm j).comp (measurable_fst.sub measurable_const))).enorm
  calc ∫⁻ x in A, ∑' j, ‖cv (K j) b x‖ₑ
      ≤ ∫⁻ x in A, ∑' i, ∫⁻ y in E i, (∑' j, ‖K j (x - y) - K j (x - c i)‖ₑ) * ‖b y‖ₑ :=
        lintegral_mono fun x => bad_pointwise hKm hKi E hEm hEd c hbm hbi hbB hb0 hbint x
    _ = ∑' i, ∫⁻ x in A, ∫⁻ y in E i, (∑' j, ‖K j (x - y) - K j (x - c i)‖ₑ) * ‖b y‖ₑ := by
        rw [lintegral_tsum]
        intro i
        exact ((hF i).lintegral_prod_right' (ν := volume.restrict (E i))).aemeasurable
    _ = ∑' i, ∫⁻ y in E i, ∫⁻ x in A, (∑' j, ‖K j (x - y) - K j (x - c i)‖ₑ) * ‖b y‖ₑ := by
        refine tsum_congr fun i => ?_
        exact lintegral_lintegral_swap ((hF i).aemeasurable)
    _ ≤ ∑' i, ∫⁻ y in E i, H * ‖b y‖ₑ := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        refine setLIntegral_mono' (hEm i) fun y hy => ?_
        rw [lintegral_mul_const' _ _ enorm_ne_top]
        refine mul_le_mul_left ?_ _
        refine le_trans (lintegral_mono_set ?_) (horm_translate hH (c i) y (s := 2 * ρ i)
          (by linarith [hρ i y hy]))
        intro x hx
        exact hx i
    _ = H * ∫⁻ y in ⋃ i, E i, ‖b y‖ₑ := by
        rw [lintegral_iUnion hEm hEd, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun i => ?_
        rw [lintegral_const_mul _ hbm.enorm]

end HRS.Commutator.Whole.XLI
