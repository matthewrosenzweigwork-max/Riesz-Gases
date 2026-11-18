import HRS.External.WeakSpec
import HRS.Equilibrium.ReferenceMarginal

/-!
# S8.2 R02 (S82R), N7: the removed-particle mixture at measure level (abstract part)
The mixing weight `pinWeight` is the density of the removed coordinate; averaging a pointwise
(position-weighted) comparison over it.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {B : Type*} [Fintype B]

/-- `pinWeight` is the section integral of the `(n+1)`-particle density. -/
theorem s82r_pinWeight_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) (x : E) :
    pinWeight V lam a n x = ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y)
      ∂(Measure.pi fun _ : Fin n => μ) := by
  have hψ := isField_pinField V hlam a
  have h1 : ∀ y : Fin n → E, fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y)
      = (ENNReal.ofReal (Real.exp (pinField V lam a x))
          * (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹)
          * fieldWeight V (pinField V lam (pinsWith a x)) lam y := by
    intro y
    unfold fieldDensity
    rw [fieldWeight_insertAt]; ring
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ (by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (fieldNorm_pos hψ.measurable V lam (n + 1)).ne'))]
  unfold pinWeight
  change _ = _ * fieldNorm V (pinField V lam (pinsWith a x)) lam n
  ring

theorem s82r_pinWeight_meas (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) : Measurable (pinWeight V lam a n) := by
  have hψ := isField_pinField V hlam a
  have hF := measurable_fieldDensity hψ.measurable V lam (n + 1)
  have hm : Measurable fun p : E × (Fin n → E) => fieldDensity V (pinField V lam a) lam (n + 1)
      (insertAt i p.1 p.2) :=
    hF.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i).symm.measurable
  have := hm.lintegral_prod_right' (ν := Measure.pi fun _ : Fin n => μ)
  have e : pinWeight V lam a n = fun x => ∫⁻ y, fieldDensity V (pinField V lam a) lam (n + 1)
      (insertAt i x y) ∂(Measure.pi fun _ : Fin n => μ) :=
    funext fun x => s82r_pinWeight_eq V hlam a i x
  rw [e]; exact this

/-- The law of the removed coordinate `i` is `pinWeight • μ`. -/
theorem s82r_pinWeight_marg (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) {A : Set E} (hA : MeasurableSet A) :
    ((pinnedLaw V lam (n + 1) a).map (fun y => y i)) A = ∫⁻ x in A, pinWeight V lam a n x ∂μ := by
  have hψ := isField_pinField V hlam a
  have hS : MeasurableSet ((fun y : Fin (n + 1) → E => y i) ⁻¹' A) := measurable_pi_apply _ hA
  rw [Measure.map_apply (measurable_pi_apply _) hA]
  change (fieldLaw V (pinField V lam a) lam (n + 1)) _ = _
  unfold fieldLaw
  rw [withDensity_apply _ hS, ← lintegral_indicator hS, ← lintegral_indicator hA]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  set h : (Fin (n + 1) → E) → ℝ≥0∞ := fun y =>
    ((fun y : Fin (n + 1) → E => y i) ⁻¹' A).indicator
      (fieldDensity V (pinField V lam a) lam (n + 1)) y with hh
  have hhm : Measurable h :=
    (measurable_fieldDensity hψ.measurable V lam (n + 1)).indicator hS
  have step1 : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, h (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => h (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  rw [step1, lintegral_prod (fun p => h (e.symm p)) (hhm.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [hsymm]
  by_cases hx : x ∈ A
  · have h1 : ∀ y : Fin n → E, h (insertAt i x y)
        = fieldDensity V (pinField V lam a) lam (n + 1) (insertAt i x y) := by
      intro y
      have hm : insertAt i x y ∈ (fun y : Fin (n + 1) → E => y i) ⁻¹' A := by simp [hx]
      simp only [hh]
      rw [Set.indicator_of_mem hm]
    simp_rw [h1]
    rw [Set.indicator_of_mem hx, s82r_pinWeight_eq V hlam a i x]
  · have h1 : ∀ y : Fin n → E, h (insertAt i x y) = 0 := by
      intro y
      have hm : insertAt i x y ∉ (fun y : Fin (n + 1) → E => y i) ⁻¹' A := by simp [hx]
      simp only [hh]
      rw [Set.indicator_of_notMem hm]
    simp_rw [h1]
    simp [Set.indicator_of_notMem hx]

/-- Weighted integrals against `pinWeight` are controlled by a marginal domination. -/
theorem s82r_pinWeight_lintegral_le (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E)
    {n : ℕ} (i : Fin (n + 1)) {K : ℝ≥0∞}
    (hmarg : (pinnedLaw V lam (n + 1) a).map (fun y => y i) ≤ K • μ)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, pinWeight V lam a n x * g x ∂μ ≤ K * ∫⁻ x, g x ∂μ := by
  have hν : μ.withDensity (pinWeight V lam a n) = (pinnedLaw V lam (n + 1) a).map (fun y => y i) := by
    refine Measure.ext fun A hA => ?_
    rw [withDensity_apply _ hA, s82r_pinWeight_marg V hlam a i hA]
  have hpm := s82r_pinWeight_meas V hlam a i
  calc ∫⁻ x, pinWeight V lam a n x * g x ∂μ = ∫⁻ x, g x ∂(μ.withDensity (pinWeight V lam a n)) :=
        (lintegral_withDensity_eq_lintegral_mul _ hpm hg).symm
    _ ≤ ∫⁻ x, g x ∂(K • μ) := lintegral_mono' (hν ▸ hmarg) le_rfl
    _ = K * ∫⁻ x, g x ∂μ := by rw [lintegral_smul_measure]; rfl

/-- **Averaging a pointwise comparison over the removed coordinate.**  If, for every value `x` of the
removed coordinate, the marginal mass `r x` of the ensemble with the extra pin `x` is within the
(extended) defect `d x` of `r0`, then the mixture is within `D` whenever `∫ pinWeight * d ≤ D`. -/
theorem s82r_mix_compare (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) {A : Set E} (hA : MeasurableSet A) {r0 : ℝ} (hr0 : 0 ≤ r0)
    (d : E → ℝ≥0∞) (hdm : Measurable d) {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hd1 : ∀ x, ENNReal.ofReal (((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)).real A)
      ≤ ENNReal.ofReal r0 + d x)
    (hd2 : ∀ x, ENNReal.ofReal r0
      ≤ ENNReal.ofReal (((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)).real A) + d x)
    (hint : ∫⁻ x, pinWeight V lam a n x * d x ∂μ ≤ D) :
    |((pinnedLaw V lam (n + 1) a).map (fun y => y (i.succAbove j))).real A - r0| ≤ D.toReal := by
  have := isProb_pinnedLaw V hlam (n + 1) a
  have : ∀ x, IsProbabilityMeasure (pinnedLaw V lam n (pinsWith a x)) :=
    fun x => isProb_pinnedLaw V hlam n _
  have hmix := pinned_marginal_succ V hlam a i j hA
  have hw := lintegral_pinWeight V hlam a i j
  have hpm := s82r_pinWeight_meas V hlam a i
  set X := ((pinnedLaw V lam (n + 1) a).map (fun y => y (i.succAbove j))) A with hX
  have hXt : X ≠ ∞ := by
    rw [hX, Measure.map_apply (measurable_pi_apply _) hA]
    exact measure_ne_top _ _
  have hp : ∀ x, ((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)) A
      = ENNReal.ofReal (((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)).real A) :=
    fun x => by
      simp only [Measure.real]
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hup : X ≤ ENNReal.ofReal r0 + D := by
    rw [hmix]
    calc ∫⁻ x, pinWeight V lam a n x * ((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)) A ∂μ
        ≤ ∫⁻ x, (pinWeight V lam a n x * ENNReal.ofReal r0 + pinWeight V lam a n x * d x) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← mul_add, hp]
          exact mul_le_mul' le_rfl (hd1 x)
      _ = ENNReal.ofReal r0 + ∫⁻ x, pinWeight V lam a n x * d x ∂μ := by
          rw [lintegral_add_left (hpm.mul_const _), lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
            hw, one_mul]
      _ ≤ _ := add_le_add le_rfl hint
  have hlo : ENNReal.ofReal r0 ≤ X + D := by
    calc ENNReal.ofReal r0 = ∫⁻ x, pinWeight V lam a n x * ENNReal.ofReal r0 ∂μ := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hw, one_mul]
      _ ≤ ∫⁻ x, (pinWeight V lam a n x * ((pinnedLaw V lam n (pinsWith a x)).map (fun y => y j)) A
            + pinWeight V lam a n x * d x) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← mul_add, hp]
          exact mul_le_mul' le_rfl (hd2 x)
      _ = X + ∫⁻ x, pinWeight V lam a n x * d x ∂μ := by
          rw [lintegral_add_right _ (show Measurable fun x => pinWeight V lam a n x * d x from hpm.mul hdm), hmix]
      _ ≤ X + D := add_le_add le_rfl hint
  have h1 : X.toReal ≤ r0 + D.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hD⟩) hup
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top hD, ENNReal.toReal_ofReal hr0] at this
  have h2 : r0 ≤ X.toReal + D.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hXt, hD⟩) hlo
    rwa [ENNReal.toReal_add hXt hD, ENNReal.toReal_ofReal hr0] at this
  simp only [Measure.real]
  rw [abs_le]; constructor <;> linarith

end HRS.MS.S82R
