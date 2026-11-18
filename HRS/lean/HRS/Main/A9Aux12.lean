import HRS.Main.A9Aux11

/-!
# Packet A9, part 12: the abstract four-term comparison in a Hilbert space

`a9_chain`: for `Z, X, Ĩ : Ω → H` measurable, a linear contraction `ι : ℝ^p → H`, a measurable `c : H → ℝ^p`
with `νG.map c = γ`, and `Φ ∈ C_b²(H)`,
`|E Φ(Z) - E ∫ Φ(Ĩ + y) dνG(y)| ≤ e₁ + e₂ + e₃ + e₄` where `e₁` bounds `E‖Z - X - ιM‖`, `e₂` is the
shift estimate, `e₃` bounds `E‖X - Ĩ‖` and `e₄` bounds `E‖y - ι c y‖` under `νG`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.Main.A8P

theorem a9_abs_integral_sub_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ENNReal.ofReal |f ω - g ω| ∂P ≤ ENNReal.ofReal c) :
    |(∫ ω, f ω ∂P) - ∫ ω, g ω ∂P| ≤ c := by
  have hi : Integrable (fun ω => |f ω - g ω|) P := (hf.sub hg).abs
  rw [← integral_sub hf hg]
  refine (abs_integral_le_integral_abs).trans ?_
  have e : ENNReal.ofReal (∫ ω, |f ω - g ω| ∂P) = ∫⁻ ω, ENNReal.ofReal |f ω - g ω| ∂P :=
    ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => abs_nonneg _)
  rw [← e] at h
  exact (ENNReal.ofReal_le_ofReal_iff hc).1 h

section Chain

variable {p : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem a9_chain (ι : (ℝ^p) →L[ℝ] H) (hι : ‖ι‖ ≤ 1) (c : H → ℝ^p) (hc : Measurable c)
    (νG : Measure H) [IsProbabilityMeasure νG] (γ : Measure (ℝ^p)) [IsProbabilityMeasure γ]
    (hνγ : νG.map c = γ)
    (Φ : H → ℝ) (hΦ : Φ ∈ CbUnitBall H 2)
    (Z X Xt : Ω → H) (hZ : Measurable Z) (hX : Measurable X) (hXt : Measurable Xt)
    (Mt : Ω → (ℝ^p)) (hM : AEMeasurable Mt P)
    {e1 e2 e3 e4 : ℝ} (he1 : 0 ≤ e1) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4)
    (h1 : ∫⁻ ω, ENNReal.ofReal ‖Z ω - X ω - ι (Mt ω)‖ ∂P ≤ ENNReal.ofReal e1)
    (h2 : |(∫ ω, Φ (X ω + ι (Mt ω)) ∂P) - ∫ ω, (∫ z, Φ (X ω + ι z) ∂γ) ∂P| ≤ e2)
    (h3 : ∫⁻ ω, ENNReal.ofReal ‖X ω - Xt ω‖ ∂P ≤ ENNReal.ofReal e3)
    (h4 : ∫⁻ y, ENNReal.ofReal ‖y - ι (c y)‖ ∂νG ≤ ENNReal.ofReal e4) :
    |(∫ ω, Φ (Z ω) ∂P) - ∫ ω, (∫ y, Φ (Xt ω + y) ∂νG) ∂P| ≤ e1 + e2 + e3 + e4 := by
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hΦb := fun x => a9_cbUnit_bdd hΦ x
  have hιc : Continuous ι := ι.continuous
  -- the smoothed functions
  set fΛ : H → ℝ := fun x => ∫ z, Φ (x + ι z) ∂γ with hfΛ
  set fG : H → ℝ := fun x => ∫ y, Φ (x + y) ∂νG with hfG
  have hiΛ : ∀ x : H, Integrable (fun z => Φ (x + ι z)) γ := fun x =>
    Integrable.of_bound (C := 1) (hΦc.comp (continuous_const.add hιc)).aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa using hΦb (x + ι z))
  have hiG : ∀ x : H, Integrable (fun y => Φ (x + y)) νG := fun x =>
    Integrable.of_bound (C := 1) (hΦc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa using hΦb (x + y))
  have hfΛlip : ∀ x y, |fΛ x - fΛ y| ≤ ‖x - y‖ := fun x y => by
    simp only [hfΛ]
    rw [← integral_sub (hiΛ x) (hiΛ y)]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ‖x - y‖) (Eventually.of_forall fun z => ?_)).trans
      (by simp)
    have := a9_cbUnit_lip hΦ (x + ι z) (y + ι z)
    simpa [Real.norm_eq_abs, add_sub_add_right_eq_sub] using this
  have hfGlip : ∀ x y, |fG x - fG y| ≤ ‖x - y‖ := fun x y => by
    simp only [hfG]
    rw [← integral_sub (hiG x) (hiG y)]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ‖x - y‖) (Eventually.of_forall fun z => ?_)).trans
      (by simp)
    have := a9_cbUnit_lip hΦ (x + z) (y + z)
    simpa [Real.norm_eq_abs, add_sub_add_right_eq_sub] using this
  have hfΛb : ∀ x, |fΛ x| ≤ 1 := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := γ) (C := 1) (f := fun z => Φ (x + ι z))
      (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hΦb (x + ι z))
    simpa [Real.norm_eq_abs, hfΛ] using this
  have hfGb : ∀ x, |fG x| ≤ 1 := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := νG) (C := 1) (f := fun y => Φ (x + y))
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hΦb (x + y))
    simpa [Real.norm_eq_abs, hfG] using this
  have hfΛc : Continuous fΛ := by
    have : LipschitzWith 1 fΛ := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [dist_eq_norm, Real.dist_eq] using hfΛlip x y
    exact this.continuous
  have hfGc : Continuous fG := by
    have : LipschitzWith 1 fG := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [dist_eq_norm, Real.dist_eq] using hfGlip x y
    exact this.continuous
  -- integrability of the compositions
  have hIΦ : ∀ F : Ω → H, AEMeasurable F P → Integrable (fun ω => Φ (F ω)) P := fun F hF =>
    Integrable.of_bound (C := 1) (hΦc.measurable.comp_aemeasurable hF).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa using hΦb (F ω))
  have hIΛ : ∀ F : Ω → H, AEMeasurable F P → Integrable (fun ω => fΛ (F ω)) P := fun F hF =>
    Integrable.of_bound (C := 1) (hfΛc.measurable.comp_aemeasurable hF).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa using hfΛb (F ω))
  have hIG : ∀ F : Ω → H, AEMeasurable F P → Integrable (fun ω => fG (F ω)) P := fun F hF =>
    Integrable.of_bound (C := 1) (hfGc.measurable.comp_aemeasurable hF).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa using hfGb (F ω))
  have hιM : AEMeasurable (fun ω => ι (Mt ω)) P := hιc.measurable.comp_aemeasurable hM
  have hXM : AEMeasurable (fun ω => X ω + ι (Mt ω)) P := hX.aemeasurable.add hιM
  -- term 1
  have t1 : |(∫ ω, Φ (Z ω) ∂P) - ∫ ω, Φ (X ω + ι (Mt ω)) ∂P| ≤ e1 := by
    refine a9_abs_integral_sub_le (hIΦ Z hZ.aemeasurable) (hIΦ _ hXM) he1 ?_
    refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) h1
    have := a9_cbUnit_lip hΦ (Z ω) (X ω + ι (Mt ω))
    calc |Φ (Z ω) - Φ (X ω + ι (Mt ω))| ≤ ‖Z ω - (X ω + ι (Mt ω))‖ := this
      _ = ‖Z ω - X ω - ι (Mt ω)‖ := by rw [sub_sub]
  -- term 3
  have t3 : |(∫ ω, fΛ (X ω) ∂P) - ∫ ω, fΛ (Xt ω) ∂P| ≤ e3 := by
    refine a9_abs_integral_sub_le (hIΛ X hX.aemeasurable) (hIΛ Xt hXt.aemeasurable) he3 ?_
    exact le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hfΛlip _ _)) h3
  -- term 4
  have hfΛ_eq : ∀ x, fΛ x = ∫ y, Φ (x + ι (c y)) ∂νG := fun x => by
    simp only [hfΛ]
    rw [← hνγ]
    have hm : Measurable fun z : (ℝ^p) => Φ (x + ι z) :=
      hΦc.measurable.comp (measurable_const.add hιc.measurable)
    rw [integral_map hc.aemeasurable hm.aestronglyMeasurable]
  have t4pt : ∀ x, |fΛ x - fG x| ≤ e4 := fun x => by
    rw [hfΛ_eq x]
    simp only [hfG]
    refine a9_abs_integral_sub_le (P := νG) ?_ (hiG x) he4 ?_
    · exact Integrable.of_bound (C := 1)
        (hΦc.measurable.comp (measurable_const.add (hιc.measurable.comp hc))).aestronglyMeasurable
        (Eventually.of_forall fun y => by simpa using hΦb (x + ι (c y)))
    · refine le_trans (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) h4
      have := a9_cbUnit_lip hΦ (x + ι (c y)) (x + y)
      calc |Φ (x + ι (c y)) - Φ (x + y)| ≤ ‖x + ι (c y) - (x + y)‖ := this
        _ = ‖y - ι (c y)‖ := by
          rw [add_sub_add_left_eq_sub, norm_sub_rev]
  have t4 : |(∫ ω, fΛ (Xt ω) ∂P) - ∫ ω, fG (Xt ω) ∂P| ≤ e4 := by
    rw [← integral_sub (hIΛ Xt hXt.aemeasurable) (hIG Xt hXt.aemeasurable), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := e4) (Eventually.of_forall fun ω => ?_)).trans
      (by simp)
    simpa [Real.norm_eq_abs] using t4pt (Xt ω)
  -- assembly
  have e : (∫ ω, Φ (Z ω) ∂P) - ∫ ω, fG (Xt ω) ∂P =
      ((∫ ω, Φ (Z ω) ∂P) - ∫ ω, Φ (X ω + ι (Mt ω)) ∂P) +
      (((∫ ω, Φ (X ω + ι (Mt ω)) ∂P) - ∫ ω, fΛ (X ω) ∂P) +
        (((∫ ω, fΛ (X ω) ∂P) - ∫ ω, fΛ (Xt ω) ∂P) +
          ((∫ ω, fΛ (Xt ω) ∂P) - ∫ ω, fG (Xt ω) ∂P))) := by ring
  show |(∫ ω, Φ (Z ω) ∂P) - ∫ ω, fG (Xt ω) ∂P| ≤ _
  rw [e]
  have h2' : |(∫ ω, Φ (X ω + ι (Mt ω)) ∂P) - ∫ ω, fΛ (X ω) ∂P| ≤ e2 := h2
  calc _ ≤ |(∫ ω, Φ (Z ω) ∂P) - ∫ ω, Φ (X ω + ι (Mt ω)) ∂P| +
        |(((∫ ω, Φ (X ω + ι (Mt ω)) ∂P) - ∫ ω, fΛ (X ω) ∂P) +
        (((∫ ω, fΛ (X ω) ∂P) - ∫ ω, fΛ (Xt ω) ∂P) +
          ((∫ ω, fΛ (Xt ω) ∂P) - ∫ ω, fG (Xt ω) ∂P)))| := abs_add_le _ _
    _ ≤ e1 + (e2 + (e3 + e4)) := by
        refine add_le_add t1 ((abs_add_le _ _).trans (add_le_add h2' ((abs_add_le _ _).trans
          (add_le_add t3 t4))))
    _ = _ := by ring

end Chain

end HRS.Main.A9
