import HRS.Prob.Metrics

/-!
# Row 5.10: measure-theoretic helpers for the glue of `ui_comparison`

* `ret_map_withDensity_fac`: pushing `P.withDensity (g ∘ π ∘ Φ)` along `Φ`;
* `ret_smoothDist_withDensity_le`: two pushforwards of densities against a common measure are `d_{C²}`-close
  in terms of the `L¹` distance of the densities;
* `ret_conv_map`, `ret_conv_withDensity`: convolution with a probability measure as an image of a product measure;
* `ret_trunc_exists`: truncation of a density at level `L`, renormalised.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS

theorem ret_map_withDensity_fac {Ω α γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace γ] (P : Measure Ω) (Φ : Ω → γ) (π : γ → α) (hΦ : Measurable Φ)
    (hπ : Measurable π) (g : α → ℝ≥0∞) (hg : Measurable g) :
    (P.withDensity fun ω => g (π (Φ ω))).map Φ = (P.map Φ).withDensity fun z => g (π z) := by
  ext A hA
  rw [Measure.map_apply hΦ hA, withDensity_apply _ (hΦ hA), withDensity_apply _ hA]
  exact (setLIntegral_map hA (hg.comp hπ) hΦ).symm

/-- Two finite measures with densities `ρ₁, ρ₂` against `Q`, and a bounded measurable test. -/
theorem ret_abs_integral_sub_le {α : Type*} [MeasurableSpace α] (Q : Measure α)
    (ρ₁ ρ₂ : α → ℝ≥0∞) (h1 : Measurable ρ₁) (h2 : Measurable ρ₂)
    [IsFiniteMeasure (Q.withDensity ρ₁)] [IsFiniteMeasure (Q.withDensity ρ₂)]
    (Ψ : α → ℝ) (hΨ : Measurable Ψ) (hb : ∀ z, |Ψ z| ≤ 1) :
    |∫ z, Ψ z ∂(Q.withDensity ρ₁) - ∫ z, Ψ z ∂(Q.withDensity ρ₂)| ≤
      (∫⁻ z, ((ρ₁ z - ρ₂ z) + (ρ₂ z - ρ₁ z)) ∂Q).toReal := by
  set m : Measure α := Q.withDensity fun z => min (ρ₁ z) (ρ₂ z) with hm
  set e₁ : Measure α := Q.withDensity fun z => ρ₁ z - ρ₂ z with he₁
  set e₂ : Measure α := Q.withDensity fun z => ρ₂ z - ρ₁ z with he₂
  have hmeas1 : Measurable fun z => ρ₁ z - ρ₂ z := h1.sub h2
  have hmeas2 : Measurable fun z => ρ₂ z - ρ₁ z := h2.sub h1
  have hmin : Measurable fun z => min (ρ₁ z) (ρ₂ z) := h1.min h2
  have d1 : Q.withDensity ρ₁ = e₁ + m := by
    rw [he₁, hm, ← withDensity_add_left hmeas1]
    congr 1
    funext z
    exact (tsub_add_min).symm
  have d2 : Q.withDensity ρ₂ = e₂ + m := by
    rw [he₂, hm, ← withDensity_add_left hmeas2]
    congr 1
    funext z
    show ρ₂ z = ρ₂ z - ρ₁ z + min (ρ₁ z) (ρ₂ z)
    rw [min_comm]
    exact (tsub_add_min).symm
  have fe₁ : IsFiniteMeasure e₁ := by
    refine isFiniteMeasure_of_le (Q.withDensity ρ₁) ?_
    rw [d1]; exact Measure.le_add_right le_rfl
  have fe₂ : IsFiniteMeasure e₂ := by
    refine isFiniteMeasure_of_le (Q.withDensity ρ₂) ?_
    rw [d2]; exact Measure.le_add_right le_rfl
  have fm : IsFiniteMeasure m := by
    refine isFiniteMeasure_of_le (Q.withDensity ρ₁) ?_
    rw [d1]; exact Measure.le_add_left le_rfl
  have hint : ∀ μ : Measure α, IsFiniteMeasure μ → Integrable Ψ μ := fun μ hμ =>
    Integrable.of_bound hΨ.aestronglyMeasurable 1 (ae_of_all _ fun z => by simpa using hb z)
  have hI1 : ∫ z, Ψ z ∂(Q.withDensity ρ₁) = ∫ z, Ψ z ∂e₁ + ∫ z, Ψ z ∂m := by
    rw [d1]; exact integral_add_measure (hint _ fe₁) (hint _ fm)
  have hI2 : ∫ z, Ψ z ∂(Q.withDensity ρ₂) = ∫ z, Ψ z ∂e₂ + ∫ z, Ψ z ∂m := by
    rw [d2]; exact integral_add_measure (hint _ fe₂) (hint _ fm)
  have hbd : ∀ (μ : Measure α) [IsFiniteMeasure μ], |∫ z, Ψ z ∂μ| ≤ (μ Set.univ).toReal := by
    intro μ _
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := 1)
      (ae_of_all _ fun z => by simpa using hb z)
    simpa [Measure.real] using this
  have hu1 : e₁ Set.univ = ∫⁻ z, (ρ₁ z - ρ₂ z) ∂Q := by
    rw [he₁, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hu2 : e₂ Set.univ = ∫⁻ z, (ρ₂ z - ρ₁ z) ∂Q := by
    rw [he₂, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hsum : ∫⁻ z, ((ρ₁ z - ρ₂ z) + (ρ₂ z - ρ₁ z)) ∂Q = e₁ Set.univ + e₂ Set.univ := by
    rw [hu1, hu2, lintegral_add_left hmeas1]
  rw [hsum]
  have ne1 : e₁ Set.univ ≠ ⊤ := measure_ne_top _ _
  have ne2 : e₂ Set.univ ≠ ⊤ := measure_ne_top _ _
  rw [ENNReal.toReal_add ne1 ne2, hI1, hI2]
  have : ∫ z, Ψ z ∂e₁ + ∫ z, Ψ z ∂m - (∫ z, Ψ z ∂e₂ + ∫ z, Ψ z ∂m) =
      ∫ z, Ψ z ∂e₁ - ∫ z, Ψ z ∂e₂ := by ring
  rw [this]
  calc _ ≤ |∫ z, Ψ z ∂e₁| + |∫ z, Ψ z ∂e₂| := abs_sub _ _
    _ ≤ _ := add_le_add (hbd e₁) (hbd e₂)

theorem ret_smoothDist_withDensity_le {α B : Type*} [MeasurableSpace α] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] (Q : Measure α) (F : α → B)
    (hF : Measurable F) (ρ₁ ρ₂ : α → ℝ≥0∞) (h1 : Measurable ρ₁) (h2 : Measurable ρ₂)
    [IsFiniteMeasure (Q.withDensity ρ₁)] [IsFiniteMeasure (Q.withDensity ρ₂)] :
    ENNReal.ofReal (smoothDist 2 ((Q.withDensity ρ₁).map F) ((Q.withDensity ρ₂).map F)) ≤
      ∫⁻ z, ((ρ₁ z - ρ₂ z) + (ρ₂ z - ρ₁ z)) ∂Q := by
  by_cases hE : ∫⁻ z, ((ρ₁ z - ρ₂ z) + (ρ₂ z - ρ₁ z)) ∂Q = ⊤
  · rw [hE]; exact le_top
  have hle : smoothDist 2 ((Q.withDensity ρ₁).map F) ((Q.withDensity ρ₂).map F) ≤
      (∫⁻ z, ((ρ₁ z - ρ₂ z) + (ρ₂ z - ρ₁ z)) ∂Q).toReal := by
    refine Real.iSup_le (fun Φ => ?_) ENNReal.toReal_nonneg
    have hΦm : Measurable Φ.1 := Φ.2.1.continuous.measurable
    rw [integral_map hF.aemeasurable hΦm.aestronglyMeasurable,
      integral_map hF.aemeasurable hΦm.aestronglyMeasurable]
    exact ret_abs_integral_sub_le Q ρ₁ ρ₂ h1 h2 (fun z => Φ.1 (F z)) (hΦm.comp hF)
      (fun z => abs_apply_le_of_mem Φ.2 _)
  calc _ ≤ ENNReal.ofReal (∫⁻ z, ((ρ₁ z - ρ₂ z) + (ρ₂ z - ρ₁ z)) ∂Q).toReal :=
        ENNReal.ofReal_le_ofReal hle
    _ = _ := ENNReal.ofReal_toReal hE

theorem ret_conv_map {α : Type*} [MeasurableSpace α] {p : ℕ} (Q : Measure α) [SFinite Q]
    (γ : Measure (EuclideanSpace ℝ (Fin p))) [SFinite γ] (f : α → EuclideanSpace ℝ (Fin p))
    (hf : Measurable f) :
    (Q.map f) ∗ γ = (Q.prod γ).map (fun z => f z.1 + z.2) := by
  have h1 : (Q.map f).prod γ = (Q.prod γ).map (Prod.map f id) := by
    conv_lhs => rw [← Measure.map_id (μ := γ)]
    exact Measure.map_prod_map Q γ hf measurable_id
  unfold Measure.conv
  rw [h1, Measure.map_map (by fun_prop) (hf.prodMap measurable_id)]
  rfl

theorem ret_conv_withDensity {α : Type*} [MeasurableSpace α] {p : ℕ} (Q : Measure α) [SFinite Q]
    (γ : Measure (EuclideanSpace ℝ (Fin p))) [SFinite γ] (f : α → EuclideanSpace ℝ (Fin p))
    (hf : Measurable f) (ρ : α → ℝ≥0∞) (hρ : Measurable ρ) :
    ((Q.withDensity ρ).map f) ∗ γ =
      ((Q.prod γ).withDensity fun z => ρ z.1).map (fun z => f z.1 + z.2) := by
  rw [ret_conv_map _ γ f hf, prod_withDensity_left hρ]

/-- Truncation of a density at level `L`, renormalised. -/
theorem ret_trunc_exists {α : Type*} [MeasurableSpace α] (G ν : Measure α) [IsProbabilityMeasure G]
    [IsProbabilityMeasure ν] (hac : ν ≪ G) (L : ℝ) (θ : ℝ≥0∞)
    (hθ : ν {x | ENNReal.ofReal L < ν.rnDeriv G x} ≤ θ) (hθ2 : θ ≤ 2⁻¹) :
    ∃ h' : α → ℝ≥0∞, Measurable h' ∧ (∃ M : ℝ≥0, ∀ x, h' x ≤ M) ∧ ∫⁻ x, h' x ∂G = 1 ∧
      ∫⁻ x, h' x ^ 2 ∂G ≤ ENNReal.ofReal (2 * L) ∧
      ∫⁻ x, ((ν.rnDeriv G x - h' x) + (h' x - ν.rnDeriv G x)) ∂G ≤ 2 * θ := by
  classical
  set h : α → ℝ≥0∞ := ν.rnDeriv G with hh
  have hhm : Measurable h := Measure.measurable_rnDeriv ν G
  set A : Set α := {x | h x ≤ ENNReal.ofReal L} with hA
  have hAm : MeasurableSet A := measurableSet_le hhm measurable_const
  have hν : G.withDensity h = ν := Measure.withDensity_rnDeriv_eq ν G hac
  have hAc : Aᶜ = {x | ENNReal.ofReal L < h x} := by ext x; simp [hA]
  set a : ℝ≥0∞ := ν A with ha
  set b : ℝ≥0∞ := ν Aᶜ with hb
  have hab : a + b = 1 := by rw [ha, hb, measure_add_measure_compl hAm]; simp
  have hbθ : b ≤ θ := by rw [hb, hAc]; exact hθ
  have h2a : 2⁻¹ ≤ a := by
    have : (2⁻¹ : ℝ≥0∞) + 2⁻¹ ≤ a + 2⁻¹ := by
      rw [ENNReal.inv_two_add_inv_two, ← hab]
      exact add_le_add le_rfl (hbθ.trans hθ2)
    exact ENNReal.le_of_add_le_add_right (by simp) this
  have ha0 : a ≠ 0 := fun h0 => by
    rw [h0] at h2a; simp at h2a
  have haT : a ≠ ⊤ := measure_ne_top _ _
  have ha1 : a ≤ 1 := by rw [← hab]; exact le_self_add
  set k : ℝ≥0∞ := a⁻¹ with hk
  have hka : k * a = 1 := ENNReal.inv_mul_cancel ha0 haT
  have hk1 : 1 ≤ k := ENNReal.one_le_inv.2 ha1
  have hk2 : k ≤ 2 := by
    rw [hk, ENNReal.inv_le_iff_inv_le]; simpa using h2a
  have hkT : k ≠ ⊤ := ne_top_of_le_ne_top (by simp) hk2
  have hAint : ∫⁻ x, A.indicator h x ∂G = a := by
    rw [ha, ← hν, withDensity_apply _ hAm, lintegral_indicator hAm]
  have hAcint : ∫⁻ x, Aᶜ.indicator h x ∂G = b := by
    rw [hb, ← hν, withDensity_apply _ hAm.compl, lintegral_indicator hAm.compl]
  have hindm : Measurable (A.indicator h) := hhm.indicator hAm
  have hind_le : ∀ x, A.indicator h x ≤ ENNReal.ofReal L := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]; exact hx
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  refine ⟨fun x => k * A.indicator h x, hindm.const_mul k, ⟨(2 * L).toNNReal, fun x => ?_⟩, ?_, ?_, ?_⟩
  · calc k * A.indicator h x ≤ 2 * ENNReal.ofReal L := mul_le_mul' hk2 (hind_le x)
      _ = ENNReal.ofReal (2 * L) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ = _ := rfl
  · rw [lintegral_const_mul _ hindm, hAint, hk, ENNReal.inv_mul_cancel ha0 haT]
  · calc ∫⁻ x, (k * A.indicator h x) ^ 2 ∂G
        ≤ ∫⁻ x, (k ^ 2 * ENNReal.ofReal L) * A.indicator h x ∂G := by
          refine lintegral_mono fun x => ?_
          calc (k * A.indicator h x) ^ 2 = k ^ 2 * (A.indicator h x * A.indicator h x) := by ring
            _ ≤ k ^ 2 * (ENNReal.ofReal L * A.indicator h x) := by
                gcongr; exact hind_le x
            _ = k ^ 2 * ENNReal.ofReal L * A.indicator h x := by ring
      _ = (k ^ 2 * ENNReal.ofReal L) * a := by rw [lintegral_const_mul _ hindm, hAint]
      _ = k * (k * a) * ENNReal.ofReal L := by ring
      _ = k * ENNReal.ofReal L := by rw [hka, mul_one]
      _ ≤ 2 * ENNReal.ofReal L := by gcongr
      _ = ENNReal.ofReal (2 * L) := by rw [ENNReal.ofReal_mul (by norm_num)]; simp
  · have hkm : (k - 1) * a = b := by
      rw [ENNReal.sub_mul (fun _ _ => haT), hka, one_mul]
      refine ENNReal.sub_eq_of_eq_add_rev haT ?_
      exact hab.symm
    calc ∫⁻ x, ((h x - k * A.indicator h x) + (k * A.indicator h x - h x)) ∂G
        ≤ ∫⁻ x, (Aᶜ.indicator h x + (k - 1) * A.indicator h x) ∂G := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ A
          · have hfin : h x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
            rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx)]
            have e1 : h x - k * h x = 0 := tsub_eq_zero_of_le (by calc h x = 1 * h x := (one_mul _).symm
                _ ≤ k * h x := by gcongr)
            have e2 : k * h x - h x = (k - 1) * h x := by
              rw [ENNReal.sub_mul (fun _ _ => hfin), one_mul]
            rw [e1, e2, zero_add]
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx)]
            simp
      _ = b + (k - 1) * a := by
          rw [lintegral_add_left (hhm.indicator hAm.compl), hAcint,
            lintegral_const_mul _ hindm, hAint]
      _ = b + b := by rw [hkm]
      _ ≤ 2 * θ := by rw [two_mul]; exact add_le_add hbθ hbθ


theorem ret_smoothDist_comm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (k : ℕ) (P Q : Measure B) : smoothDist k P Q = smoothDist k Q P := by
  unfold smoothDist
  congr 1
  funext Φ
  exact abs_sub_comm _ _

theorem ret_ofReal_triangle2 {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B]
    (P Q R : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure R] :
    ENNReal.ofReal (smoothDist 2 P R) ≤
      ENNReal.ofReal (smoothDist 2 P Q) + ENNReal.ofReal (smoothDist 2 Q R) := by
  rw [← ENNReal.ofReal_add (smoothDist_nonneg _ _ _) (smoothDist_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (smoothDist_triangle 2 P Q R)

theorem ret_ofReal_triangle3 {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B]
    (P Q R S : Measure B) [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure R]
    [IsFiniteMeasure S] :
    ENNReal.ofReal (smoothDist 2 P S) ≤ ENNReal.ofReal (smoothDist 2 P Q) +
      ENNReal.ofReal (smoothDist 2 Q R) + ENNReal.ofReal (smoothDist 2 R S) := by
  calc ENNReal.ofReal (smoothDist 2 P S) ≤
        ENNReal.ofReal (smoothDist 2 P R) + ENNReal.ofReal (smoothDist 2 R S) :=
        ret_ofReal_triangle2 P R S
    _ ≤ (ENNReal.ofReal (smoothDist 2 P Q) + ENNReal.ofReal (smoothDist 2 Q R)) +
          ENNReal.ofReal (smoothDist 2 R S) := by
        gcongr; exact ret_ofReal_triangle2 P Q R
    _ = _ := by ring

end HRS.ME.Ret

end
