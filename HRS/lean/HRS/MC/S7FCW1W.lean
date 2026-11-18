import HRS.Prob.Metrics

/-!
# Weak convergence and lower semicontinuity from `W_1 → 0` (FC-D7a, FC-D7b)

Proof files for `s7_FC_D7a_weak` and `s7_FC_D7b_fatou` of `HRS/MC/S7FCPlan.lean`.  Neither statement
uses the `field_chaos` definitions; the proofs use only `HRS/Prob/Metrics.lean` (sorry-free).
Helpers carry the prefix `S7FCW1_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

open HRS

namespace HRS.MC.Sec7.S7FCW1

/-- Coupling bound: for a bounded `L`-Lipschitz `f`, `|∫ f dP - ∫ f dQ| ≤ L · W_1(P,Q)`. -/
theorem S7FCW1_lip_coupling {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : B → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (L : NNReal)
    (hL : LipschitzWith L f) :
    ENNReal.ofReal |∫ z, f z ∂P - ∫ z, f z ∂Q| ≤ (L : ℝ≥0∞) * wassersteinE 1 P Q := by
  have hW : wassersteinE 1 P Q =
      ⨅ π : couplings P Q, ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1 := by
    unfold wassersteinE
    simp only [div_one, ENNReal.rpow_one]
  have hpt : ∀ a b : B, ‖f a - f b‖ₑ ≤ (L : ℝ≥0∞) * ENNReal.ofReal (‖a - b‖ ^ (1 : ℝ)) := by
    intro a b
    rw [Real.rpow_one, ← ofReal_norm]
    calc ENNReal.ofReal ‖f a - f b‖ = ENNReal.ofReal (dist (f a) (f b)) := by rw [dist_eq_norm]
      _ ≤ ENNReal.ofReal ((L : ℝ) * dist a b) := ENNReal.ofReal_le_ofReal (hL.dist_le_mul a b)
      _ = (L : ℝ≥0∞) * ENNReal.ofReal ‖a - b‖ := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal, dist_eq_norm]
  have key : ∀ π : couplings P Q, ENNReal.ofReal |∫ z, f z ∂P - ∫ z, f z ∂Q| ≤
      (L : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1 := by
    rintro ⟨π, hπ⟩
    have := hπ.isProbabilityMeasure
    have hfst : Integrable (fun z : B × B => f z.1) π :=
      Integrable.of_bound (hf.measurable.comp measurable_fst).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM z.1)
    have hsnd : Integrable (fun z : B × B => f z.2) π :=
      Integrable.of_bound (hf.measurable.comp measurable_snd).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM z.2)
    have e1 : ∫ z, f z ∂P = ∫ z, f z.1 ∂π := by
      rw [← hπ.1, integral_map measurable_fst.aemeasurable hf.measurable.aestronglyMeasurable]
    have e2 : ∫ z, f z ∂Q = ∫ z, f z.2 ∂π := by
      rw [← hπ.2, integral_map measurable_snd.aemeasurable hf.measurable.aestronglyMeasurable]
    have hg : Integrable (fun z : B × B => f z.1 - f z.2) π := hfst.sub hsnd
    rw [e1, e2, ← integral_sub hfst hsnd]
    calc ENNReal.ofReal |∫ z, (f z.1 - f z.2) ∂π|
        = ENNReal.ofReal ‖∫ z, (f z.1 - f z.2) ∂π‖ := by rw [Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal (∫ z, ‖f z.1 - f z.2‖ ∂π) :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
      _ = ∫⁻ z, ‖f z.1 - f z.2‖ₑ ∂π := ofReal_integral_norm_eq_lintegral_enorm hg
      _ ≤ ∫⁻ z, (L : ℝ≥0∞) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π :=
          lintegral_mono fun z => hpt z.1 z.2
      _ = (L : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
  rw [hW]
  by_cases hL0 : (L : ℝ≥0∞) = 0
  · have hπ0 : P.prod Q ∈ couplings P Q := by constructor <;> simp
    have := key ⟨P.prod Q, hπ0⟩
    rw [hL0, zero_mul] at this
    rw [hL0, zero_mul]
    exact this
  · rw [ENNReal.mul_iInf_of_ne hL0 ENNReal.coe_ne_top]
    exact le_iInf fun π => key π

/-- Convergence of `∫ f dμ_n` for a bounded Lipschitz `f` under `W_1(μ_n, ν) → 0`. -/
theorem S7FCW1_tendsto_lip {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (μ : ℕ → Measure B) [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure B)
    [IsProbabilityMeasure ν] (h : Tendsto (fun n => wassersteinE 1 (μ n) ν) atTop (𝓝 0))
    (f : B → ℝ) (hf : Continuous f) (M : ℝ) (hM : ∀ z, |f z| ≤ M) (L : NNReal)
    (hL : LipschitzWith L f) :
    Tendsto (fun n => ∫ z, f z ∂(μ n)) atTop (𝓝 (∫ z, f z ∂ν)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hA : Tendsto (fun n => ENNReal.ofReal ‖(∫ z, f z ∂(μ n)) - ∫ z, f z ∂ν‖) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => (L : ℝ≥0∞) * wassersteinE 1 (μ n) ν) atTop
        (𝓝 ((L : ℝ≥0∞) * 0)) :=
      ENNReal.Tendsto.const_mul h (Or.inr ENNReal.coe_ne_top)
    rw [mul_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun n => _root_.zero_le) (fun n => ?_)
    rw [Real.norm_eq_abs]
    exact S7FCW1_lip_coupling (μ n) ν f hf M hM L hL
  have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hA
  simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h3

/-- **D7a (`W_1 → 0` implies weak convergence)**, proof of `s7_FC_D7a_weak`. -/
theorem s7_FC_D7a_weak_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (μ : ℕ → Measure B) [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure B)
    [IsProbabilityMeasure ν] (h : Tendsto (fun n => wassersteinE 1 (μ n) ν) atTop (𝓝 0)) :
    ∀ G : B → ℝ, Continuous G → (∃ M, ∀ z, |G z| ≤ M) →
      Tendsto (fun n => ∫ z, G z ∂(μ n)) atTop (𝓝 (∫ z, G z ∂ν)) := by
  intro G hG hGb
  obtain ⟨M, hM⟩ := hGb
  have hlip : ∀ f : B → ℝ, (∃ C, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ L : NNReal, LipschitzWith L f) →
      Tendsto (fun n => ∫ z, f z ∂(μ n)) atTop (𝓝 (∫ z, f z ∂ν)) := by
    rintro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfc : Continuous f := hL.continuous
    have hb : ∀ z, |f z| ≤ |f 0| + C := by
      intro z
      have h1 := hC z 0
      rw [Real.dist_eq] at h1
      have h2 := abs_add_le (f z - f 0) (f 0)
      simp only [sub_add_cancel] at h2
      linarith
    exact S7FCW1_tendsto_lip μ ν h f hfc (|f 0| + C) hb L hL
  let μs : ℕ → ProbabilityMeasure B := fun n => ⟨μ n, inferInstance⟩
  let νs : ProbabilityMeasure B := ⟨ν, inferInstance⟩
  have hconv : Tendsto μs atTop (𝓝 νs) :=
    tendsto_iff_forall_lipschitz_integral_tendsto.mpr hlip
  have hGd : ∀ x y : B, dist ((⟨G, hG⟩ : C(B, ℝ)) x) ((⟨G, hG⟩ : C(B, ℝ)) y) ≤ 2 * M := by
    intro x y
    show dist (G x) (G y) ≤ 2 * M
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [(abs_le.mp (hM x)).1, (abs_le.mp (hM x)).2,
      (abs_le.mp (hM y)).1, (abs_le.mp (hM y)).2]
  let F : BoundedContinuousFunction B ℝ := BoundedContinuousFunction.mkOfBound ⟨G, hG⟩ (2 * M) hGd
  have hF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv F
  exact hF

/-- Truncated moments: `∫⁻ min(‖x‖ₑ^q, N) dν ≤ liminf ∫⁻ ‖x‖ₑ^q dμ_n`. -/
theorem S7FCW1_trunc_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (μ : ℕ → Measure B) [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure B)
    [IsProbabilityMeasure ν] (h : Tendsto (fun n => wassersteinE 1 (μ n) ν) atTop (𝓝 0))
    (q : ℝ) (hq : 0 ≤ q) (N : ℕ) :
    ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂ν ≤
      liminf (fun n => ∫⁻ x, ‖x‖ₑ ^ q ∂(μ n)) atTop := by
  let g : B → ℝ := fun x => min (‖x‖ ^ q) (N : ℝ)
  have hgc : Continuous g :=
    ((Real.continuous_rpow_const hq).comp continuous_norm).min continuous_const
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min (Real.rpow_nonneg (norm_nonneg _) q) (Nat.cast_nonneg N)
  have hgb : ∀ x, |g x| ≤ (N : ℝ) := by
    intro x
    rw [abs_of_nonneg (hg0 x)]
    exact min_le_right _ _
  have hconv := s7_FC_D7a_weak_proof μ ν h g hgc ⟨N, hgb⟩
  have hint : ∀ ρ : Measure B, IsProbabilityMeasure ρ →
      ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂ρ = ENNReal.ofReal (∫ x, g x ∂ρ) := by
    intro ρ hρ
    have hgi : Integrable g ρ :=
      Integrable.of_bound hgc.measurable.aestronglyMeasurable (N : ℝ)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact min_le_right _ _)
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)]
    refine Eq.symm (lintegral_congr fun x => ?_)
    simp only [g]
    rw [Monotone.map_min (f := ENNReal.ofReal) (fun a b hab => ENNReal.ofReal_le_ofReal hab),
      ofReal_norm_rpow hq, ofReal_norm, ENNReal.ofReal_natCast]
  have hlim : Tendsto (fun n => ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂(μ n)) atTop
      (𝓝 (∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂ν)) := by
    have e : (fun n => ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂(μ n)) =
        fun n => ENNReal.ofReal (∫ x, g x ∂(μ n)) :=
      funext fun n => hint (μ n) inferInstance
    rw [e, hint ν inferInstance]
    exact ENNReal.tendsto_ofReal hconv
  calc ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂ν
      = liminf (fun n => ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂(μ n)) atTop := hlim.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ‖x‖ₑ ^ q ∂(μ n)) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall fun n => lintegral_mono fun x => min_le_left _ _)

/-- **D7b (Fatou for moments)**, proof of `s7_FC_D7b_fatou`. -/
theorem s7_FC_D7b_fatou_proof {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] (μ : ℕ → Measure B) [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure B)
    [IsProbabilityMeasure ν] (h : Tendsto (fun n => wassersteinE 1 (μ n) ν) atTop (𝓝 0)) (q : ℝ)
    (hq : 0 ≤ q) :
    ∫⁻ x, ‖x‖ₑ ^ q ∂ν ≤ liminf (fun n => ∫⁻ x, ‖x‖ₑ ^ q ∂(μ n)) atTop := by
  have hsup : ∀ x : B, ⨆ N : ℕ, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) = ‖x‖ₑ ^ q := by
    intro x
    refine le_antisymm (iSup_le fun N => min_le_left _ _) (le_of_forall_lt fun c hc => ?_)
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    exact lt_of_lt_of_le (lt_min hc hN) (le_iSup (fun N : ℕ => min (‖x‖ₑ ^ q) (N : ℝ≥0∞)) N)
  have hmeas : ∀ N : ℕ, Measurable (fun x : B => min (‖x‖ₑ ^ q) (N : ℝ≥0∞)) := fun N =>
    (((ENNReal.continuous_rpow_const).comp continuous_enorm).min continuous_const).measurable
  have hmono : Monotone (fun (N : ℕ) (x : B) => min (‖x‖ₑ ^ q) (N : ℝ≥0∞)) := fun N M hNM x =>
    min_le_min_left _ (by exact_mod_cast hNM)
  calc ∫⁻ x, ‖x‖ₑ ^ q ∂ν = ∫⁻ x, ⨆ N : ℕ, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂ν :=
        lintegral_congr fun x => (hsup x).symm
    _ = ⨆ N : ℕ, ∫⁻ x, min (‖x‖ₑ ^ q) (N : ℝ≥0∞) ∂ν := lintegral_iSup hmeas hmono
    _ ≤ liminf (fun n => ∫⁻ x, ‖x‖ₑ ^ q ∂(μ n)) atTop :=
        iSup_le fun N => S7FCW1_trunc_le μ ν h q hq N

end HRS.MC.Sec7.S7FCW1

end
