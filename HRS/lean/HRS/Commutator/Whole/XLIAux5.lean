import HRS.Commutator.Whole.XLIAux4

/-!
# X-LI part 5: Littlewood–Paley kernel families, the tent lemma
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- A Littlewood–Paley-type kernel family: uniformly dominated by `Phi j`, with the `L²`
almost-orthogonality `∑_j ‖K_j ⋆ u‖₂² ≤ M ‖u‖₂²`. -/
structure IsLP (K : ℤ → 𝔼 → ℂ) : Prop where
  meas : ∀ j, Measurable (K j)
  dec : ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ j, DecK A j (K j)
  orth : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ u : 𝔼 → ℂ, Measurable u → Integrable u →
    ∫⁻ x, ‖u x‖ₑ ^ 2 < ⊤ → ∑' j, ∫⁻ x, ‖cv (K j) u x‖ₑ ^ 2 ≤ M * ∫⁻ x, ‖u x‖ₑ ^ 2

lemma measurable_cv {K u : 𝔼 → ℂ} (hK : Measurable K) (hu : Measurable u) :
    Measurable (cv K u) := by
  have : cv K u = fun x => ∫ y, K y * u (x - y) := funext fun x => cv_apply K u x
  rw [this]
  have hm : Measurable (fun p : 𝔼 × 𝔼 => K p.2 * u (p.1 - p.2)) :=
    (hK.comp measurable_snd).mul (hu.comp (measurable_fst.sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

lemma integrable_of_dec {A : ℝ≥0∞} (hA : A ≠ ⊤) {j : ℤ} {K : 𝔼 → ℂ} (hK : DecK A j K)
    (hKm : Measurable K) : Integrable K := by
  refine ⟨hKm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (lintegral_enorm_le_of_dec hK) (ENNReal.mul_lt_top hA.lt_top KP_ne_top.lt_top)

lemma cv_add_of_bdd {K F1 F2 : 𝔼 → ℂ} (hK : Integrable K) (h1 : Measurable F1) (h2 : Measurable F2)
    {B : ℝ} (hB1 : ∀ x, ‖F1 x‖ ≤ B) (hB2 : ∀ x, ‖F2 x‖ ≤ B) (x : 𝔼) :
    cv K (fun y => F1 y + F2 y) x = cv K F1 x + cv K F2 x := by
  simp only [cv_apply, mul_add]
  have hi : ∀ (G : 𝔼 → ℂ), Measurable G → (∀ y, ‖G y‖ ≤ B) →
      Integrable (fun y => K y * G (x - y)) := by
    intro G hG hB
    refine Integrable.mul_bdd (c := B) hK ?_ (Eventually.of_forall fun y => hB (x - y))
    exact (hG.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  exact integral_add (hi F1 h1 hB1) (hi F2 h2 hB2)

/-- pointwise tail estimate for the part of `F` outside `E` at a point of the `j`-th tent -/
lemma tail_pointwise {A : ℝ≥0∞} {j : ℤ} {K : 𝔼 → ℂ} (hK : DecK A j K) {F : 𝔼 → ℂ}
    (hF : Measurable F) (E : Set 𝔼) (hE : MeasurableSet E) (x : 𝔼) (hdd : 0 < Metric.infDist x Eᶜ) :
    ‖cv K (Eᶜ.indicator F) x‖ₑ ≤
      A * KT d * ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) *
        cmxHLS_Md (fun y => ‖F y‖ₑ) x := by
  set r := Metric.infDist x Eᶜ with hr
  have hmeas : Measurable (fun y : 𝔼 => ‖F (x - y)‖ₑ) :=
    (hF.comp (measurable_const.sub measurable_id)).enorm
  refine (enorm_cv_le K _ x).trans ?_
  calc ∫⁻ y, ‖K y‖ₑ * ‖(Eᶜ.indicator F) (x - y)‖ₑ
      ≤ ∫⁻ y, A * ((if r ≤ ‖y‖ then Phi j y else 0) * ‖F (x - y)‖ₑ) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : x - y ∈ Eᶜ
        · rw [Set.indicator_of_mem hy]
          have hry : r ≤ ‖y‖ := by
            have : Metric.infDist x Eᶜ ≤ dist x (x - y) := Metric.infDist_le_dist_of_mem hy
            simpa [dist_eq_norm] using this
          rw [if_pos hry]
          calc ‖K y‖ₑ * ‖F (x - y)‖ₑ ≤ (A * Phi j y) * ‖F (x - y)‖ₑ := mul_le_mul_left (hK y) _
            _ = _ := by ring
        · rw [Set.indicator_of_notMem hy]; simp
    _ = A * ∫⁻ y, (if r ≤ ‖y‖ then Phi j y else 0) * ‖F (x - y)‖ₑ := by
        rw [lintegral_const_mul]
        refine Measurable.mul ?_ hmeas
        refine Measurable.ite (measurableSet_le measurable_const measurable_norm) (Phi_measurable j)
          measurable_const
    _ ≤ A * (KT d * ENNReal.ofReal (((2 : ℝ) ^ j * r)⁻¹) * cmxHLS_Md (fun y => ‖F y‖ₑ) x) := by
        refine mul_le_mul_right ?_ _
        exact lintegral_Phi_tail_le j (G := fun y => ‖F y‖ₑ) hF.enorm x hdd
    _ = _ := by ring

lemma add_sq_le_two (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
  exact h

/-- **Tent lemma**: the `L²` mass of the Littlewood–Paley pieces of `F` over the tents of `E` is
controlled by the maximal function of `F` on `E`. -/
lemma tent_bound (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hK : IsLP K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (F : 𝔼 → ℂ), Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ E : Set 𝔼, MeasurableSet E →
      ∑' j, ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2 ≤
        C * ∫⁻ x in E, (cmxHLS_Md (fun y => ‖F y‖ₑ) x) ^ 2 := by
  obtain ⟨A, hA, hdec⟩ := hK.dec
  obtain ⟨M, hM, horth⟩ := hK.orth
  refine ⟨2 * M + 4 * (A * KT d) ^ 2, ?_, fun F hF hFi B hB hFB E hE => ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hM,
      ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.mul_ne_top hA KT_ne_top))⟩
  set F1 : 𝔼 → ℂ := E.indicator F with hF1
  set F2 : 𝔼 → ℂ := Eᶜ.indicator F with hF2
  have hF1m : Measurable F1 := hF.indicator hE
  have hF2m : Measurable F2 := hF.indicator hE.compl
  have hFsplit : F = fun y => F1 y + F2 y := by
    ext y; simp only [hF1, hF2]; exact (congrFun (Set.indicator_self_add_compl E F) y).symm
  have hBr : ∀ x, ‖F x‖ ≤ B.toReal := fun x => by
    have := hFB x
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 this
  have hF1b : ∀ x, ‖F1 x‖ ≤ B.toReal := fun x => by
    simp only [hF1]; by_cases h : x ∈ E
    · rw [Set.indicator_of_mem h]; exact hBr x
    · rw [Set.indicator_of_notMem h]; simp
  have hF2b : ∀ x, ‖F2 x‖ ≤ B.toReal := fun x => by
    simp only [hF2]; by_cases h : x ∈ Eᶜ
    · rw [Set.indicator_of_mem h]; exact hBr x
    · rw [Set.indicator_of_notMem h]; simp
  have hF1i : Integrable F1 := hFi.indicator hE
  have hF1fin : ∫⁻ x, ‖F1 x‖ₑ ^ 2 < ⊤ := by
    have h1 : ∀ x, ‖F1 x‖ₑ ^ 2 ≤ B * ‖F1 x‖ₑ := fun x => by
      rw [sq]
      refine mul_le_mul_left ?_ _
      by_cases h : x ∈ E
      · simp only [hF1, Set.indicator_of_mem h]; exact hFB x
      · simp [hF1, Set.indicator_of_notMem h]
    calc ∫⁻ x, ‖F1 x‖ₑ ^ 2 ≤ ∫⁻ x, B * ‖F1 x‖ₑ := lintegral_mono h1
      _ = B * ∫⁻ x, ‖F1 x‖ₑ := lintegral_const_mul' _ _ hB
      _ < ⊤ := ENNReal.mul_lt_top hB.lt_top hF1i.2
  -- the maximal function majorant
  set Md : 𝔼 → ℝ≥0∞ := cmxHLS_Md (fun y => ‖F y‖ₑ) with hMd
  have hMdm : Measurable Md := cmxHLS_Md_measurable hF.enorm
  have hF_loc : LocallyIntegrable F volume := hFi.locallyIntegrable
  have hdiff := enorm_le_Md_ae hF_loc
  set ψ : ℤ → 𝔼 → ℝ≥0∞ := fun j x =>
    (A * KT d) ^ 2 * ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 * Md x ^ 2 with hψ
  have hψm : ∀ j, Measurable (ψ j) := fun j => by
    refine (measurable_const.mul ?_).mul (hMdm.pow_const 2)
    exact ((ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Metric.continuous_infDist_pt _).measurable).inv)).pow_const 2
  -- pointwise bound on the tent
  have hpt : ∀ j, ∀ x ∈ tent E j, ‖cv (K j) F2 x‖ₑ ^ 2 ≤ ψ j x := by
    intro j x hx
    by_cases hEc : Eᶜ.Nonempty
    · have hdd : (2 : ℝ) ^ (-j) ≤ Metric.infDist x Eᶜ := by
        rw [Metric.le_infDist hEc]
        intro y hy
        by_contra hlt
        rw [not_le] at hlt
        have := hx y (by rw [dist_eq_norm] at hlt; rwa [norm_sub_rev] at hlt)
        exact hy this
      have hddpos : 0 < Metric.infDist x Eᶜ :=
        lt_of_lt_of_le (zpow_pos (by norm_num) _) hdd
      have h1 := tail_pointwise (hdec j) hF E hE x hddpos
      calc ‖cv (K j) F2 x‖ₑ ^ 2 ≤ (A * KT d * ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) *
            Md x) ^ 2 := by gcongr
        _ = ψ j x := by simp only [hψ]; ring
    · rw [Set.not_nonempty_iff_eq_empty] at hEc
      have : F2 = fun _ => 0 := by
        ext y
        simp only [hF2, hEc, Set.indicator_empty]
      have h0 : cv (K j) F2 x = 0 := by rw [cv_apply, this]; simp
      rw [h0]; simp
  -- the pointwise bound for the indicator of the tent, in terms of the geometric sum
  have hind : ∀ x j, (tent E j).indicator (ψ j) x ≤ (A * KT d) ^ 2 * Md x ^ 2 *
      (if 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ then
        ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 else 0) := by
    intro x j
    by_cases hx : x ∈ tent E j
    · rw [Set.indicator_of_mem hx]
      by_cases hEc : Eᶜ.Nonempty
      · have hdd : (2 : ℝ) ^ (-j) ≤ Metric.infDist x Eᶜ := by
          rw [Metric.le_infDist hEc]
          intro y hy
          by_contra hlt
          rw [not_le] at hlt
          have := hx y (by rw [dist_eq_norm] at hlt; rwa [norm_sub_rev] at hlt)
          exact hy this
        have h1 : 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ := by
          calc (1 : ℝ) = (2 : ℝ) ^ j * (2 : ℝ) ^ (-j) := by
                rw [← zpow_add₀ (by norm_num)]; simp
            _ ≤ _ := by gcongr
        rw [if_pos h1]
        simp only [hψ]
        refine le_of_eq ?_
        ring
      · rw [Set.not_nonempty_iff_eq_empty] at hEc
        simp only [hψ, hEc, Metric.infDist_empty, mul_zero, inv_zero, ENNReal.ofReal_zero]
        simp
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hsumψ : ∑' j, ∫⁻ x in tent E j, ψ j x ≤ 2 * (A * KT d) ^ 2 * ∫⁻ x in E, Md x ^ 2 := by
    calc ∑' j, ∫⁻ x in tent E j, ψ j x = ∑' j, ∫⁻ x, (tent E j).indicator (ψ j) x := by
          refine tsum_congr fun j => ?_
          rw [lintegral_indicator (measurableSet_tent E j)]
      _ = ∫⁻ x, ∑' j, (tent E j).indicator (ψ j) x := by
          rw [lintegral_tsum]
          intro j; exact ((hψm j).indicator (measurableSet_tent E j)).aemeasurable
      _ ≤ ∫⁻ x, E.indicator (fun x => 2 * (A * KT d) ^ 2 * Md x ^ 2) x := by
          refine lintegral_mono fun x => ?_
          by_cases hxE : x ∈ E
          · rw [Set.indicator_of_mem hxE]
            calc ∑' j, (tent E j).indicator (ψ j) x
                ≤ ∑' j, (A * KT d) ^ 2 * Md x ^ 2 *
                  (if 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ then
                    ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 else 0) :=
                  ENNReal.tsum_le_tsum fun j => hind x j
              _ = (A * KT d) ^ 2 * Md x ^ 2 * ∑' j : ℤ,
                  (if 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ then
                    ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 else 0) :=
                  ENNReal.tsum_mul_left
              _ ≤ (A * KT d) ^ 2 * Md x ^ 2 * 2 := by
                  refine mul_le_mul_right ?_ _
                  by_cases hpos : 0 < Metric.infDist x Eᶜ
                  · exact tail_geom_sum hpos
                  · have h0 : Metric.infDist x Eᶜ = 0 :=
                      le_antisymm (not_lt.1 hpos) Metric.infDist_nonneg
                    simp [h0]
              _ = 2 * (A * KT d) ^ 2 * Md x ^ 2 := by ring
          · have : ∀ j, x ∉ tent E j := fun j hx => hxE (tent_subset E j hx)
            simp [Set.indicator_of_notMem hxE, Set.indicator_of_notMem (this _)]
      _ = 2 * (A * KT d) ^ 2 * ∫⁻ x in E, Md x ^ 2 := by
          rw [lintegral_indicator hE, lintegral_const_mul _ (hMdm.pow_const 2)]
  -- split `F = F1 + F2` and sum over `j`
  have hint1 : ∀ j, ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2 ≤
      2 * ((∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2) + ∫⁻ x in tent E j, ψ j x) := by
    intro j
    have hKi := integrable_of_dec hA (hdec j) (hK.meas j)
    have hpt2 : ∀ x ∈ tent E j, ‖cv (K j) F x‖ₑ ^ 2 ≤ 2 * (‖cv (K j) F1 x‖ₑ ^ 2 + ψ j x) := by
      intro x hx
      have e : cv (K j) F x = cv (K j) F1 x + cv (K j) F2 x := by
        have := cv_add_of_bdd hKi hF1m hF2m hF1b hF2b x
        rw [← hFsplit] at this
        exact this
      rw [e]
      calc ‖cv (K j) F1 x + cv (K j) F2 x‖ₑ ^ 2
          ≤ (‖cv (K j) F1 x‖ₑ + ‖cv (K j) F2 x‖ₑ) ^ 2 := by gcongr; exact enorm_add_le _ _
        _ ≤ 2 * (‖cv (K j) F1 x‖ₑ ^ 2 + ‖cv (K j) F2 x‖ₑ ^ 2) := add_sq_le_two _ _
        _ ≤ 2 * (‖cv (K j) F1 x‖ₑ ^ 2 + ψ j x) := by gcongr; exact hpt j x hx
    have hcv1m : Measurable (fun x => ‖cv (K j) F1 x‖ₑ ^ 2) :=
      ((measurable_cv (hK.meas j) hF1m).enorm).pow_const 2
    have hsm : Measurable (fun x => ‖cv (K j) F1 x‖ₑ ^ 2 + ψ j x) := hcv1m.add (hψm j)
    calc ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2
        ≤ ∫⁻ x in tent E j, 2 * (‖cv (K j) F1 x‖ₑ ^ 2 + ψ j x) :=
          setLIntegral_mono' (measurableSet_tent E j) hpt2
      _ = 2 * ((∫⁻ x in tent E j, ‖cv (K j) F1 x‖ₑ ^ 2) + ∫⁻ x in tent E j, ψ j x) := by
          rw [lintegral_const_mul _ hsm, lintegral_add_left hcv1m]
      _ ≤ _ := mul_le_mul_right (add_le_add (setLIntegral_le_lintegral _ _) le_rfl) _
  have hF1int : ∫⁻ x, ‖F1 x‖ₑ ^ 2 ≤ ∫⁻ x in E, Md x ^ 2 := by
    have : ∫⁻ x, ‖F1 x‖ₑ ^ 2 = ∫⁻ x in E, ‖F x‖ₑ ^ 2 := by
      rw [← lintegral_indicator hE]
      refine lintegral_congr fun x => ?_
      by_cases h : x ∈ E
      · simp [hF1, Set.indicator_of_mem h]
      · simp [hF1, Set.indicator_of_notMem h]
    rw [this]
    refine lintegral_mono_ae ?_
    have : ∀ᵐ x ∂(volume.restrict E), ‖F x‖ₑ ≤ Md x := ae_restrict_of_ae hdiff
    filter_upwards [this] with x hx
    gcongr
  calc ∑' j, ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2
      ≤ ∑' j, 2 * ((∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2) + ∫⁻ x in tent E j, ψ j x) :=
        ENNReal.tsum_le_tsum hint1
    _ = 2 * ((∑' j, ∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2) + ∑' j, ∫⁻ x in tent E j, ψ j x) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ 2 * (M * (∫⁻ x, ‖F1 x‖ₑ ^ 2) + 2 * (A * KT d) ^ 2 * ∫⁻ x in E, Md x ^ 2) :=
        mul_le_mul_right (add_le_add (horth F1 hF1m hF1i hF1fin) hsumψ) _
    _ ≤ 2 * (M * (∫⁻ x in E, Md x ^ 2) + 2 * (A * KT d) ^ 2 * ∫⁻ x in E, Md x ^ 2) := by
        gcongr
    _ = _ := by ring

end HRS.Commutator.Whole.XLI
