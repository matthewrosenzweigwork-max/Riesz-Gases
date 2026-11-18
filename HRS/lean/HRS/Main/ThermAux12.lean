import HRS.Main.ThermAux11

/-!
# THERM helper 12: translation estimates for `d_2` and `W_p`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

section Translate

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

/-- `W_p(P(· - a), Q) ≤ W_p(P, Q) + ‖a‖`. -/
theorem therm_wE_translate_le [SecondCountableTopology B] (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (a : B) (p : ℝ) (hp : 1 ≤ p) :
    wassersteinE p (P.map (fun x => x + a)) Q ≤ wassersteinE p P Q + ENNReal.ofReal ‖a‖ := by
  have hp0 : 0 < p := by linarith
  unfold wassersteinE
  rw [ENNReal.iInf_add]
  refine le_iInf fun π => ?_
  obtain ⟨h1, h2⟩ := π.2
  set g : B × B → B × B := fun z => (z.1 + a, z.2) with hg
  have hgm : Measurable g := by fun_prop
  have hπ : IsCoupling (π.1.map g) (P.map (fun x => x + a)) Q := by
    constructor
    · have e : (π.1.map g).map Prod.fst = (π.1.map Prod.fst).map (fun x => x + a) := by
        rw [Measure.map_map measurable_fst hgm, Measure.map_map (by fun_prop) measurable_fst]
        rfl
      rw [e, h1]
    · have e : (π.1.map g).map Prod.snd = π.1.map Prod.snd := by
        rw [Measure.map_map measurable_snd hgm]
        rfl
      rw [e, h2]
  refine (iInf_le (fun π : couplings (P.map (fun x => x + a)) Q =>
    (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p)) ⟨π.1.map g, hπ⟩).trans ?_
  show (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂(π.1.map g)) ^ (1 / p) ≤ _
  set u : B × B → ℝ≥0∞ := fun z => ENNReal.ofReal ‖z.1 - z.2‖ with hu
  set v : B × B → ℝ≥0∞ := fun _ => ENNReal.ofReal ‖a‖ with hv
  have hum : Measurable u := by
    rw [hu]; exact ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm)
  have hvm : Measurable v := measurable_const
  haveI : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  calc (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂(π.1.map g)) ^ (1 / p)
      ≤ (∫⁻ z, ENNReal.ofReal (‖(g z).1 - (g z).2‖ ^ p) ∂π.1) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_map_le _ hgm.aemeasurable) (by positivity)
    _ ≤ (∫⁻ z, (u + v) z ^ p ∂π.1) ^ (1 / p) := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun z => ?_) (by positivity)
        rw [ofReal_norm_rpow (p := p) hp0.le]
        refine ENNReal.rpow_le_rpow ?_ hp0.le
        simp only [Pi.add_apply, hu, hv, hg]
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖z.1 + a - z.2‖ = ‖(z.1 - z.2) + a‖ := by congr 1; abel
          _ ≤ ‖z.1 - z.2‖ + ‖a‖ := norm_add_le _ _
    _ ≤ (∫⁻ z, u z ^ p ∂π.1) ^ (1 / p) + (∫⁻ z, v z ^ p ∂π.1) ^ (1 / p) :=
        ENNReal.lintegral_Lp_add_le hum.aemeasurable hvm.aemeasurable hp
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p) + ENNReal.ofReal ‖a‖ := by
        congr 1
        · simp only [hu, ofReal_norm_rpow (p := p) hp0.le]
        · simp only [hv, lintegral_const, measure_univ, mul_one]
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- `d_2(P(· - a), Q) ≤ d_2(P, Q) + ‖a‖`. -/
theorem therm_smoothDist_translate_le (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (a : B) :
    smoothDist 2 (P.map (fun x => x + a)) Q ≤ smoothDist 2 P Q + ‖a‖ := by
  refine Real.iSup_le (fun Φ => ?_) (add_nonneg (smoothDist_nonneg _ _ _) (norm_nonneg _))
  have hΦ := Φ.2
  have hc : Continuous Φ.1 := hΦ.1.continuous
  have hΦ1 : Φ.1 ∈ CbUnitBall B 1 := cbUnitBall_anti (by norm_num) hΦ
  have hb : ∀ z, |Φ.1 z| ≤ 1 := abs_apply_le_of_mem hΦ
  have hint : ∫ z, Φ.1 z ∂(P.map (fun x => x + a)) = ∫ z, Φ.1 (z + a) ∂P :=
    integral_map (by fun_prop) hc.aestronglyMeasurable
  have h1 : |∫ z, Φ.1 (z + a) ∂P - ∫ z, Φ.1 z ∂P| ≤ ‖a‖ := by
    have hi1 : Integrable (fun z => Φ.1 (z + a)) P :=
      Integrable.of_bound (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable 1
        (Eventually.of_forall fun z => by simpa using hb (z + a))
    have hi2 : Integrable Φ.1 P :=
      Integrable.of_bound hc.aestronglyMeasurable 1 (Eventually.of_forall fun z => by simpa using hb z)
    rw [← integral_sub hi1 hi2]
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun z => Φ.1 (z + a) - Φ.1 z)
      (C := ‖a‖) (Eventually.of_forall fun z => by
        simpa using norm_sub_le_of_mem_one hΦ1 (z + a) z)
    simpa [Measure.real] using this
  have h2 := abs_integral_sub_le_smoothDist hΦ P Q
  rw [hint]
  have e : ∫ z, Φ.1 (z + a) ∂P - ∫ z, Φ.1 z ∂Q =
      (∫ z, Φ.1 (z + a) ∂P - ∫ z, Φ.1 z ∂P) + (∫ z, Φ.1 z ∂P - ∫ z, Φ.1 z ∂Q) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (by linarith)

end Translate

variable {d : ℕ}

instance therm_pathSpace_sc {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

end Main

end HRS
