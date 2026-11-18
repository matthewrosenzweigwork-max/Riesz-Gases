import Mathlib
import HRS.Prob.Metrics

/-!
# Mean-particle packet: Wasserstein-1 helper lemmas

Internal helpers for Corollary 5.17 (`mean_particles`):

* `mp_ofReal_abs_integral_sub_le_wE1`, `mp_abs_integral_sub_le_wE1` : Lipschitz test functions are
  controlled by `W_1`;
* `mp_wE_translate2` : `W_p` of two translates;
* `mp_wE_map_clm` : `W_p` contracts under a bounded linear map;
* `mp_tendstoInDistribution_of_wE1` : `W_1 → 0` implies convergence in distribution;
* `mp_lowerTail` : a lower-tail estimate for `ξ_n + δ_n` with `δ_n → +∞`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

section MPMetric

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

/-- The product measure is a coupling. -/
theorem mp_isCoupling_prod (μ ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν := by
  constructor
  · simp [Measure.map_fst_prod]
  · simp [Measure.map_snd_prod]

/-- **Lipschitz test functions are controlled by `W_1`** (extended-real form, no finiteness
hypothesis): for a bounded `L`-Lipschitz `f`,
`ofReal |∫ f dμ - ∫ f dν| ≤ L * W_1(μ, ν)` in `ℝ≥0∞`. -/
theorem mp_ofReal_abs_integral_sub_le_wE1 {f : B → ℝ} {L : ℝ≥0} (hL : LipschitzWith L f)
    (hb : ∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C)
    (μ ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (L : ℝ≥0∞) * wassersteinE 1 μ ν := by
  obtain ⟨C, hC⟩ := hb
  have hc : Continuous f := hL.continuous
  have hbd : ∀ x, |f x| ≤ |f 0| + C := fun x => by
    have := hC x 0
    rw [Real.dist_eq] at this
    calc |f x| = |(f x - f 0) + f 0| := by ring_nf
      _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
      _ ≤ |f 0| + C := by linarith
  haveI : Nonempty (couplings μ ν) := ⟨⟨μ.prod ν, mp_isCoupling_prod μ ν⟩⟩
  unfold wassersteinE
  rw [ENNReal.mul_iInf (fun h => absurd h ENNReal.coe_ne_top)]
  refine le_iInf fun π => ?_
  obtain ⟨h1, h2⟩ := π.2
  haveI : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  have hi1 : Integrable (fun z : B × B => f z.1) π.1 :=
    Integrable.of_bound (hc.measurable.comp measurable_fst).aestronglyMeasurable (|f 0| + C)
      (Eventually.of_forall fun z => by simpa using hbd z.1)
  have hi2 : Integrable (fun z : B × B => f z.2) π.1 :=
    Integrable.of_bound (hc.measurable.comp measurable_snd).aestronglyMeasurable (|f 0| + C)
      (Eventually.of_forall fun z => by simpa using hbd z.2)
  have e1 : ∫ x, f x ∂μ = ∫ z, f z.1 ∂π.1 := by
    have := integral_map (μ := π.1) measurable_fst.aemeasurable (f := f) hc.aestronglyMeasurable
    rwa [h1] at this
  have e2 : ∫ x, f x ∂ν = ∫ z, f z.2 ∂π.1 := by
    have := integral_map (μ := π.1) measurable_snd.aemeasurable (f := f) hc.aestronglyMeasurable
    rwa [h2] at this
  rw [e1, e2, ← integral_sub hi1 hi2, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun z => ?_
  have := hL.edist_le_mul z.1 z.2
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub, ← ofReal_norm (x := z.1 - z.2)] at this
  exact this

/-- **Lipschitz test functions are controlled by `W_1`** (real form): for a bounded `L`-Lipschitz `f`
and `W_1(μ, ν) < ∞`, `|∫ f dμ - ∫ f dν| ≤ L * W_1(μ, ν)`. -/
theorem mp_abs_integral_sub_le_wE1 {f : B → ℝ} {L : ℝ≥0} (hL : LipschitzWith L f)
    (hb : ∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C)
    (μ ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hW : wassersteinE 1 μ ν ≠ ⊤) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (L : ℝ) * (wassersteinE 1 μ ν).toReal := by
  have h := mp_ofReal_abs_integral_sub_le_wE1 hL hb μ ν
  have h2 : ENNReal.ofReal |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤
      ENNReal.ofReal ((L : ℝ) * (wassersteinE 1 μ ν).toReal) := by
    rwa [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hW]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **`W_p` of two translates**: `W_p(P(· + a), Q(· + b)) ≤ W_p(P, Q) + ‖a - b‖`. -/
theorem mp_wE_translate2 [SecondCountableTopology B] (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (a b : B) (p : ℝ) (hp : 1 ≤ p) :
    wassersteinE p (P.map (fun x => x + a)) (Q.map (fun x => x + b)) ≤
      wassersteinE p P Q + ENNReal.ofReal ‖a - b‖ := by
  have hp0 : 0 < p := by linarith
  unfold wassersteinE
  rw [ENNReal.iInf_add]
  refine le_iInf fun π => ?_
  obtain ⟨h1, h2⟩ := π.2
  set g : B × B → B × B := fun z => (z.1 + a, z.2 + b) with hg
  have hgm : Measurable g := by fun_prop
  have hπ : IsCoupling (π.1.map g) (P.map (fun x => x + a)) (Q.map (fun x => x + b)) := by
    constructor
    · have e : (π.1.map g).map Prod.fst = (π.1.map Prod.fst).map (fun x => x + a) := by
        rw [Measure.map_map measurable_fst hgm, Measure.map_map (by fun_prop) measurable_fst]
        rfl
      rw [e, h1]
    · have e : (π.1.map g).map Prod.snd = (π.1.map Prod.snd).map (fun x => x + b) := by
        rw [Measure.map_map measurable_snd hgm, Measure.map_map (by fun_prop) measurable_snd]
        rfl
      rw [e, h2]
  refine (iInf_le (fun π : couplings (P.map (fun x => x + a)) (Q.map (fun x => x + b)) =>
    (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p)) ⟨π.1.map g, hπ⟩).trans ?_
  show (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂(π.1.map g)) ^ (1 / p) ≤ _
  set u : B × B → ℝ≥0∞ := fun z => ENNReal.ofReal ‖z.1 - z.2‖ with hu
  set v : B × B → ℝ≥0∞ := fun _ => ENNReal.ofReal ‖a - b‖ with hv
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
        calc ‖z.1 + a - (z.2 + b)‖ = ‖(z.1 - z.2) + (a - b)‖ := by congr 1; abel
          _ ≤ ‖z.1 - z.2‖ + ‖a - b‖ := norm_add_le _ _
    _ ≤ (∫⁻ z, u z ^ p ∂π.1) ^ (1 / p) + (∫⁻ z, v z ^ p ∂π.1) ^ (1 / p) :=
        ENNReal.lintegral_Lp_add_le hum.aemeasurable hvm.aemeasurable hp
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p) + ENNReal.ofReal ‖a - b‖ := by
        congr 1
        · simp only [hu, ofReal_norm_rpow (p := p) hp0.le]
        · simp only [hv, lintegral_const, measure_univ, mul_one]
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end MPMetric

section MPMapClm

variable {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup B'] [NormedSpace ℝ B'] [MeasurableSpace B'] [BorelSpace B']

/-- **`W_p` contracts under a bounded linear map**:
`W_p(ℓ_* μ, ℓ_* ν) ≤ ‖ℓ‖ W_p(μ, ν)` (pushforward of a coupling). -/
theorem mp_wE_map_clm (ℓ : B →L[ℝ] B') (μ ν : Measure B) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (p : ℝ) (hp : 0 < p) :
    wassersteinE p (μ.map ℓ) (ν.map ℓ) ≤ ENNReal.ofReal ‖ℓ‖ * wassersteinE p μ ν := by
  haveI : Nonempty (couplings μ ν) := ⟨⟨μ.prod ν, mp_isCoupling_prod μ ν⟩⟩
  unfold wassersteinE
  rw [ENNReal.mul_iInf (fun h => absurd h ENNReal.ofReal_ne_top)]
  refine le_iInf fun π => ?_
  obtain ⟨h1, h2⟩ := π.2
  have hℓ : Measurable ℓ := ℓ.continuous.measurable
  set g : B × B → B' × B' := fun z => (ℓ z.1, ℓ z.2) with hg
  have hgm : Measurable g := (hℓ.comp measurable_fst).prodMk (hℓ.comp measurable_snd)
  have hπ : IsCoupling (π.1.map g) (μ.map ℓ) (ν.map ℓ) := by
    constructor
    · have e : (π.1.map g).map Prod.fst = (π.1.map Prod.fst).map ℓ := by
        rw [Measure.map_map measurable_fst hgm, Measure.map_map hℓ measurable_fst]
        rfl
      rw [e, h1]
    · have e : (π.1.map g).map Prod.snd = (π.1.map Prod.snd).map ℓ := by
        rw [Measure.map_map measurable_snd hgm, Measure.map_map hℓ measurable_snd]
        rfl
      rw [e, h2]
  refine (iInf_le (fun π : couplings (μ.map ℓ) (ν.map ℓ) =>
    (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p)) ⟨π.1.map g, hπ⟩).trans ?_
  show (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂(π.1.map g)) ^ (1 / p) ≤ _
  have hpt : ∀ z : B × B, ENNReal.ofReal (‖(g z).1 - (g z).2‖ ^ p) ≤
      ENNReal.ofReal (‖ℓ‖ ^ p) * ENNReal.ofReal (‖z.1 - z.2‖ ^ p) := by
    intro z
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
    have : (g z).1 - (g z).2 = ℓ (z.1 - z.2) := by simp [hg]
    rw [this]
    exact ℓ.le_opNorm _
  calc (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂(π.1.map g)) ^ (1 / p)
      ≤ (∫⁻ z, ENNReal.ofReal (‖(g z).1 - (g z).2‖ ^ p) ∂π.1) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_map_le _ hgm.aemeasurable) (by positivity)
    _ ≤ (∫⁻ z, ENNReal.ofReal (‖ℓ‖ ^ p) * ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by positivity)
    _ = ENNReal.ofReal ‖ℓ‖ * (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π.1) ^ (1 / p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          Real.rpow_rpow_inv (norm_nonneg _) hp.ne']

end MPMapClm

end HRS
