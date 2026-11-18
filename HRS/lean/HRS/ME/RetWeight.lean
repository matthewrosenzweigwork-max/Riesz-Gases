import HRS.Uniform.Spec

/-!
# Row 5.10, packet RW1: transfer of the martingale hypotheses to a bounded `ℱ 0`-measurable change of density

If `w` is a bounded `ℱ 0`-measurable density with `∫ w dP = 1`, then `P_w = P.withDensity w` is a probability measure absolutely
continuous with respect to `P` with `P_w ≤ B • P`.  The structure `IsHilbertMartingaleWithCovariation` (martingale and covariation
fields, integrability fields, almost-sure fields) and the property `IsStochConv` (an `L²` limit) are stable under this change of
measure.  The filtration is NOT changed and no completeness of the filtration is used or claimed.  The template is
`HRS/Prob/HilbertMartingale.lean`, lemmas `martingale_cond`, `isHilbertMartingale_cond` (the same statement for `P[· | A]`, `A ∈ ℱ 0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.Uniform

section WDAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A density bounded by `B` gives `P.withDensity w ≤ B • P`. -/
lemma wd_le_smul {P : Measure Ω} [IsFiniteMeasure P] {w : Ω → ℝ≥0∞} {B : ℝ≥0} (hB : ∀ ω, w ω ≤ B) :
    P.withDensity w ≤ (B : ℝ≥0∞) • P := by
  refine Measure.le_iff'.2 fun s => ?_
  rw [withDensity_apply' , Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ a in s, w a ∂P ≤ ∫⁻ _ in s, (B : ℝ≥0∞) ∂P := lintegral_mono fun a => hB a
    _ = (B : ℝ≥0∞) * P s := setLIntegral_const s _

/-- Set integrals against `P.withDensity w` in terms of `P` for a bounded density. -/
lemma wd_setIntegral {P : Measure Ω} {w : Ω → ℝ≥0∞} (hw : Measurable w) {B : ℝ≥0} (hB : ∀ ω, w ω ≤ B)
    {s : Set Ω} (hs : MeasurableSet s) (g : Ω → ℝ) :
    ∫ x in s, g x ∂(P.withDensity w) = ∫ x in s, (w x).toReal * g x ∂P := by
  have hfin : ∀ᵐ x ∂(P.restrict s), w x < ∞ :=
    ae_of_all _ fun x => lt_of_le_of_lt (hB x) ENNReal.coe_lt_top
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hw hfin g hs]
  simp only [smul_eq_mul]

/-- Pull-out of a bounded `ℱ a`-measurable factor, for a martingale `f` (`a ≤ b`). -/
lemma wd_integral_mul {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ mΩ} {f : ℝ → Ω → ℝ}
    (hf : Martingale f ℱ P) {a b : ℝ} (hab : a ≤ b) {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ a] g)
    {C : ℝ} (hC : ∀ ω, |g ω| ≤ C) :
    ∫ x, g x * f b x ∂P = ∫ x, g x * f a x ∂P := by
  have hgm : StronglyMeasurable g := hg.mono (ℱ.le a)
  have hbd : ∀ᵐ x ∂P, ‖g x‖ ≤ C := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hC x
  have hi1 : Integrable (fun x => g x * f b x) P :=
    Integrable.bdd_mul (hf.integrable b) hgm.aestronglyMeasurable hbd
  have hce := condExp_mul_of_stronglyMeasurable_left hg hi1 (hf.integrable b)
  calc ∫ x, g x * f b x ∂P = ∫ x, (P[fun x => g x * f b x | ℱ a]) x ∂P :=
        (integral_condExp (ℱ.le a)).symm
    _ = ∫ x, g x * (P[f b | ℱ a]) x ∂P := by
        apply integral_congr_ae
        filter_upwards [hce] with x hx
        exact hx
    _ = ∫ x, g x * f a x ∂P := by
        apply integral_congr_ae
        filter_upwards [hf.condExp_ae_eq hab] with x hx
        rw [hx]

/-- Martingale property of a real process under a bounded `ℱ 0`-measurable change of density. -/
lemma wd_martingale {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ mΩ} {f : ℝ → Ω → ℝ}
    (hf : Martingale f ℱ P) (h0 : f 0 =ᵐ[P] 0) {w : Ω → ℝ≥0∞} (hw : Measurable[ℱ 0] w) {B : ℝ≥0}
    (hB : ∀ ω, w ω ≤ B) [IsFiniteMeasure (P.withDensity w)] :
    Martingale f ℱ (P.withDensity w) := by
  classical
  have hwm : Measurable w := hw.mono (ℱ.le 0) le_rfl
  have hle : P.withDensity w ≤ (B : ℝ≥0∞) • P := wd_le_smul hB
  have hint : ∀ k, Integrable (f k) (P.withDensity w) := fun k =>
    (hf.integrable k).of_measure_le_smul ENNReal.coe_ne_top hle
  have hneg : ∀ k, k ≤ 0 → f k =ᵐ[P] 0 := by
    intro k hk
    have h1 := hf.2 k 0 hk
    have h2 : P[f 0 | ℱ k] =ᵐ[P] P[(0 : Ω → ℝ) | ℱ k] := condExp_congr_ae h0
    rw [condExp_zero] at h2
    exact h1.symm.trans h2
  have hbv : ∀ ω, (w ω).toReal ≤ (B : ℝ) := fun ω => by
    have := ENNReal.toReal_mono ENNReal.coe_ne_top (hB ω)
    rwa [ENNReal.coe_toReal] at this
  have hv0 : ∀ ω, 0 ≤ (w ω).toReal := fun ω => ENNReal.toReal_nonneg
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := NNReal.coe_nonneg B
  have hind_bd : ∀ (t : Set Ω) ω, |t.indicator (fun x => (w x).toReal) ω| ≤ (B : ℝ) := by
    intro t ω
    rw [Set.indicator_apply]
    split_ifs
    · rw [abs_of_nonneg (hv0 ω)]; exact hbv ω
    · rw [abs_zero]; exact hBnn
  have hconv : ∀ (s : Set Ω), MeasurableSet s → ∀ k : ℝ,
      ∫ x in s, (w x).toReal * f k x ∂P = ∫ x, s.indicator (fun x => (w x).toReal) x * f k x ∂P := by
    intro s hs k
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  refine ⟨hf.stronglyAdapted, fun i j hij => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hint j) (fun s _ _ => (hint i).integrableOn)
    (fun s hs _ => ?_) (hf.stronglyMeasurable i).aestronglyMeasurable
  have hsm : MeasurableSet s := ℱ.le i s hs
  rw [wd_setIntegral hwm hB hsm (f i), wd_setIntegral hwm hB hsm (f j), hconv s hsm i, hconv s hsm j]
  by_cases hi : 0 ≤ i
  · have hwi : Measurable[ℱ i] (fun x => (w x).toReal) :=
      (hw.mono (ℱ.mono hi) le_rfl).ennreal_toReal
    have hgs : StronglyMeasurable[ℱ i] (s.indicator fun x => (w x).toReal) :=
      (hwi.indicator hs).stronglyMeasurable
    exact (wd_integral_mul hf hij hgs (fun ω => hind_bd s ω)).symm
  · replace hi := not_le.mp hi
    have hs0 : MeasurableSet[ℱ 0] s := ℱ.mono hi.le s hs
    have hw0 : Measurable[ℱ 0] (fun x => (w x).toReal) := hw.ennreal_toReal
    have hgs0 : StronglyMeasurable[ℱ 0] (s.indicator fun x => (w x).toReal) :=
      (hw0.indicator hs0).stronglyMeasurable
    have hzero : ∀ k, k ≤ 0 → ∫ x, s.indicator (fun x => (w x).toReal) x * f k x ∂P = 0 := by
      intro k hk
      have : (fun x => s.indicator (fun x => (w x).toReal) x * f k x) =ᵐ[P] fun _ => 0 := by
        filter_upwards [hneg k hk] with x hx
        simp [hx]
      rw [integral_congr_ae this]
      simp
    rw [hzero i hi.le]
    by_cases hj : j ≤ 0
    · rw [hzero j hj]
    · replace hj := not_le.mp hj
      rw [wd_integral_mul hf hj.le hgs0 (fun ω => hind_bd s ω), hzero 0 le_rfl]

end WDAux

/-- Hölder (Cauchy-Schwarz) in `ℝ≥0∞`: `∫ w F ≤ (∫ w²)^{1/2} (∫ F²)^{1/2}`. -/
theorem lintegral_mul_le_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {w F : Ω → ℝ≥0∞}
    (hw : AEMeasurable w P) (hF : AEMeasurable F P) :
    ∫⁻ ω, w ω * F ω ∂P ≤ (∫⁻ ω, w ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, F ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hw hF
  simpa only [ENNReal.rpow_two, Pi.mul_apply] using h

/-- `P.withDensity w` is a probability measure when `∫ w dP = 1` and `w` is measurable. -/
theorem isProbabilityMeasure_withDensity_of_lintegral_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {w : Ω → ℝ≥0∞} (hw : Measurable w) (h1 : ∫⁻ ω, w ω ∂P = 1) :
    IsProbabilityMeasure (P.withDensity w) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h1

/-- The martingale hypotheses are preserved by a bounded `ℱ 0`-measurable density of integral one. -/
theorem isHilbertMartingale_withDensity {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    {w : Ω → ℝ≥0∞} (hw : Measurable[ℱ 0] w) {B : ℝ≥0} (hB : ∀ ω, w ω ≤ B)
    (h1 : ∫⁻ ω, w ω ∂P = 1) [IsProbabilityMeasure (P.withDensity w)] :
    IsHilbertMartingaleWithCovariation (P.withDensity w) ℱ t M Sg := by
  have hac : P.withDensity w ≪ P := withDensity_absolutelyContinuous P w
  have hle : P.withDensity w ≤ (B : ℝ≥0∞) • P := wd_le_smul hB
  have hc : (B : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hzero : ∀ x : H, (fun ω => inner ℝ (M 0 ω) x) =ᵐ[P] 0 := fun x => by
    filter_upwards [hM.zero] with ω h
    simp [h]
  refine
    { martingale := fun x => wd_martingale (hM.martingale x) (hzero x) hw hB
      zero := hac.ae_le hM.zero
      cont := hac.ae_le hM.cont
      sq_int := fun τ hτ => MemLp.of_measure_le_smul hc hle (hM.sq_int τ hτ)
      sigma_meas := hM.sigma_meas
      sigma_adapted := hM.sigma_adapted
      sigma_traceClass := hac.ae_le hM.sigma_traceClass
      sigma_int := Integrable.of_measure_le_smul hc hle hM.sigma_int
      sigma_pathint := hac.ae_le hM.sigma_pathint
      sigma_entry_int := hac.ae_le hM.sigma_entry_int
      covariation := fun x y => wd_martingale (hM.covariation x y) ?_ hw hB }
  · filter_upwards [hM.zero] with ω h
    simp [h]

/-- The stochastic convolution property (an `L²`-limit of Riemann sums) is preserved by a bounded density. -/
theorem isStochConv_withDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {VE : ℝ → ℝ → E →L[ℝ] E} {j : H →L[ℝ] E} {M : ℝ → Ω → H} {a t : ℝ} {Z : Ω → E}
    (hZ : IsStochConv P VE j M a t Z) {w : Ω → ℝ≥0∞} {B : ℝ≥0} (hB : ∀ ω, w ω ≤ B)
    (hw : Measurable w) :
    IsStochConv (P.withDensity w) VE j M a t Z := by
  unfold IsStochConv at hZ ⊢
  intro ε hε
  have hbound : ∀ g : Ω → ℝ≥0∞, ∫⁻ ω, g ω ∂(P.withDensity w) ≤ (B : ℝ≥0∞) * ∫⁻ ω, g ω ∂P := by
    intro g
    calc ∫⁻ ω, g ω ∂(P.withDensity w) ≤ ∫⁻ ω, (w * g) ω ∂P :=
          lintegral_withDensity_le_lintegral_mul P hw g
      _ ≤ ∫⁻ ω, (B : ℝ≥0∞) * g ω ∂P := lintegral_mono fun ω => by
          simp only [Pi.mul_apply]; exact mul_le_mul_of_nonneg_right (hB ω) zero_le
      _ = (B : ℝ≥0∞) * ∫⁻ ω, g ω ∂P := lintegral_const_mul' _ _ ENNReal.coe_ne_top
  obtain ⟨δ, hδ, hZ'⟩ := hZ (ε / ((B : ℝ) + 1)) (div_pos hε (by positivity))
  refine ⟨δ, hδ, fun n r h0 hl hmono hgap => ?_⟩
  have hX := hZ' n r h0 hl hmono hgap
  refine lt_of_le_of_lt (hbound _) ?_
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  have hreal : (B : ℝ) * (ε / ((B : ℝ) + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ hB1]
    nlinarith
  calc (B : ℝ≥0∞) * ∫⁻ ω, ‖Z ω - riemannSum VE j M t r ω‖ₑ ^ 2 ∂P
      ≤ (B : ℝ≥0∞) * ENNReal.ofReal (ε / ((B : ℝ) + 1)) := mul_le_mul_of_nonneg_left hX.le zero_le
    _ = ENNReal.ofReal ((B : ℝ) * (ε / ((B : ℝ) + 1))) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg B), ENNReal.ofReal_coe_nnreal]
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 hreal

end HRS.ME.Ret

end
