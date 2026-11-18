import HRS.Appendix.B15CAux3

/-!
# Packet B15-DV: proof of the Donsker-Varadhan variational formula `b15b_klDiv_eq_iSup`

Relocated proof (the frozen spec in `HRS/Appendix/B15BAux1.lean` keeps its `sorry`).
* (`≥`, Gibbs) `b15dv_gibbs`: `∫ φ dP - log ∫ e^φ dQ ≤ klDiv P Q`, from Mathlib's `integral_llr_tilted_right`.
* (`≤`, `P ≪ Q`) `b15dv_klDiv_le_iSup_of_ac`: bounded measurable truncations `log (clamp_{[e^-k,e^k]} (dP/dQ))`
  (`b15dv_le_iSup_bdd`: approximation by continuous functions in `L¹(P+Q)`), monotone/dominated limit in `k`;
  if `llr` is not `P`-integrable then `(llr)⁻` is (`b15dv_llr_negPart_integrable`, `t (log t)⁻ ≤ 1`) and the
  truncated integrals are unbounded.
* (`≤`, `P ≪̸ Q`) `b15dv_iSup_eq_top_of_not_ac`: `φ_k = k (1 - min 1 (dist(·,A)/r))` for a closed `A` with
  `Q A = 0 < P A` and `r` with `e^k Q(thickening r A) ≤ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory Metric
open scoped ENNReal NNReal

namespace HRS


/-- Gibbs variational inequality, continuous (or just integrable) test functions. -/
theorem b15dv_gibbs {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (φ : α → ℝ)
    (hφP : Integrable φ P) (hexp : Integrable (fun x => Real.exp (φ x)) Q) :
    ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)) ≤ klDiv P Q := by
  by_cases hac : P ≪ Q
  swap
  · rw [klDiv_of_not_ac hac]; exact le_top
  by_cases hint : Integrable (llr P Q) P
  swap
  · rw [klDiv_of_not_integrable hint]; exact le_top
  have := isProbabilityMeasure_tilted hexp
  have hPQ : P ≪ Q.tilted φ := hac.trans (absolutelyContinuous_tilted hexp)
  have hint2 := integrable_llr_tilted_right hac hφP hint hexp
  have h1 := integral_llr_add_sub_measure_univ_nonneg hPQ hint2
  have h2 := integral_llr_tilted_right hac hφP hexp hint
  simp only [probReal_univ] at h1
  rw [klDiv_of_ac_of_integrable hac hint]
  apply ENNReal.ofReal_le_ofReal
  simp only [probReal_univ]
  linarith

lemma b15dv_exp_sub_le (a b : ℝ) : |Real.exp a - Real.exp b| ≤ max (Real.exp a) (Real.exp b) * |a - b| := by
  have h1 := Real.add_one_le_exp (b - a)
  have h2 := Real.add_one_le_exp (a - b)
  have ha := Real.exp_pos a
  have hb := Real.exp_pos b
  have e1 : Real.exp b = Real.exp a * Real.exp (b - a) := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp a = Real.exp b * Real.exp (a - b) := by rw [← Real.exp_add]; ring_nf
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith [Real.exp_le_exp.2 h]), abs_of_nonpos (by linarith),
      max_eq_right (Real.exp_le_exp.2 h)]
    nlinarith
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h]), abs_of_nonneg (by linarith),
      max_eq_left (Real.exp_le_exp.2 h)]
    nlinarith

lemma b15dv_tendsto_integral {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (F : ℕ → α → ℝ) (f : α → ℝ) (hF : ∀ n, Integrable (F n) ν) (hf : Integrable f ν)
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0)) (h : ∀ n, ∫ x, |F n x - f x| ∂ν ≤ B n) :
    Tendsto (fun n => ∫ x, F n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hB
  rw [Real.dist_eq, ← integral_sub (hF n) hf]
  exact (abs_integral_le_integral_abs).trans (h n)

lemma b15dv_clamp_dist (k b c : ℝ) (hc : |c| ≤ k) :
    |c - max (-k) (min k b)| ≤ |c - b| := by
  rw [abs_le] at hc
  have : c = max (-k) (min k c) := by
    rw [min_eq_right hc.2, max_eq_right hc.1]
  conv_lhs => rw [this]
  rw [max_comm (-k), max_comm (-k) (min k b)]
  refine (abs_max_sub_max_le_abs (min k c) (min k b) (-k)).trans ?_
  have := abs_min_sub_min_le_max k c k b
  simpa using this

/-- Bounded measurable test functions are dominated by the continuous supremum. -/
theorem b15dv_le_iSup_bdd {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ψ : α → ℝ) (hψ : Measurable ψ) (k : ℝ) (hk : 0 ≤ k) (hb : ∀ x, |ψ x| ≤ k) :
    ENNReal.ofReal (∫ x, ψ x ∂P - Real.log (∫ x, Real.exp (ψ x) ∂Q)) ≤
      ⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)) := by
  set μ : Measure α := P + Q with hμ
  have hψμ : Integrable ψ μ :=
    Integrable.of_bound hψ.aestronglyMeasurable k (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hb x)
  have hex : ∀ n : ℕ, ∃ g : BoundedContinuousFunction α ℝ, (∫ x, ‖ψ x - g x‖ ∂μ) ≤ 1 / ((n : ℝ) + 1) ∧ Integrable g μ :=
    fun n => hψμ.exists_boundedContinuous_integral_sub_le (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1))
  choose g hg hgi using hex
  let c : ℕ → C(α, ℝ) := fun n =>
    ⟨fun x => max (-k) (min k (g n x)), by fun_prop⟩
  have hcb : ∀ n x, |c n x| ≤ k := by
    intro n x
    simp only [c, ContinuousMap.coe_mk, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hcd : ∀ n x, |ψ x - c n x| ≤ ‖ψ x - g n x‖ := fun n x => by
    simpa [c, Real.norm_eq_abs] using b15dv_clamp_dist k (g n x) (ψ x) (hb x)
  have hcint : ∀ (ν : Measure α) [IsFiniteMeasure ν] n, Integrable (c n) ν := fun ν _ n =>
    (c n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hexpint : ∀ (ν : Measure α) [IsFiniteMeasure ν] n,
      Integrable (fun x => Real.exp (c n x)) ν := fun ν _ n =>
    (Real.continuous_exp.comp (c n).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hψint : ∀ (ν : Measure α) [IsFiniteMeasure ν], Integrable ψ ν := fun ν _ =>
    Integrable.of_bound hψ.aestronglyMeasurable k (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hb x)
  have hexpψint : ∀ (ν : Measure α) [IsFiniteMeasure ν], Integrable (fun x => Real.exp (ψ x)) ν :=
    fun ν _ => Integrable.of_bound (Real.measurable_exp.comp hψ).aestronglyMeasurable (Real.exp k)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_of_abs_le (hb x)))
  -- L¹ bounds, in terms of `μ = P + Q`
  have hL1 : ∀ n, (∫ x, |ψ x - c n x| ∂P) ≤ 1 / ((n : ℝ) + 1) ∧
      (∫ x, |ψ x - c n x| ∂Q) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hI : Integrable (fun x => |ψ x - c n x|) μ :=
      ((hψint μ).sub (hcint μ n)).abs
    have hIP : Integrable (fun x => |ψ x - c n x|) P := hI.mono_measure (Measure.le_add_right le_rfl)
    have hIQ : Integrable (fun x => |ψ x - c n x|) Q := hI.mono_measure (Measure.le_add_left le_rfl)
    have hsplit : (∫ x, |ψ x - c n x| ∂μ) = (∫ x, |ψ x - c n x| ∂P) + ∫ x, |ψ x - c n x| ∂Q :=
      integral_add_measure hIP hIQ
    have hle : (∫ x, |ψ x - c n x| ∂μ) ≤ 1 / ((n : ℝ) + 1) :=
      (integral_mono hI ((hψμ.sub (hgi n)).norm) (fun x => hcd n x)).trans (hg n)
    have h1 : 0 ≤ ∫ x, |ψ x - c n x| ∂P := integral_nonneg fun x => abs_nonneg _
    have h2 : 0 ≤ ∫ x, |ψ x - c n x| ∂Q := integral_nonneg fun x => abs_nonneg _
    constructor <;> linarith
  have hB0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hT1 : Tendsto (fun n => ∫ x, c n x ∂P) atTop (𝓝 (∫ x, ψ x ∂P)) := by
    refine b15dv_tendsto_integral P (fun n x => c n x) ψ (hcint P) (hψint P) _ hB0 (fun n => ?_)
    have := (hL1 n).1
    calc (∫ x, |c n x - ψ x| ∂P) = ∫ x, |ψ x - c n x| ∂P := by
          congr 1; ext x; exact abs_sub_comm _ _
      _ ≤ _ := this
  have hT2 : Tendsto (fun n => ∫ x, Real.exp (c n x) ∂Q) atTop (𝓝 (∫ x, Real.exp (ψ x) ∂Q)) := by
    refine b15dv_tendsto_integral Q (fun n x => Real.exp (c n x)) (fun x => Real.exp (ψ x))
      (hexpint Q) (hexpψint Q) (fun n : ℕ => Real.exp k * (1 / ((n : ℝ) + 1)))
      (by have := hB0.const_mul (Real.exp k); rwa [mul_zero] at this) (fun n => ?_)
    have hpt : ∀ x, |Real.exp (c n x) - Real.exp (ψ x)| ≤ Real.exp k * |ψ x - c n x| := by
      intro x
      refine (b15dv_exp_sub_le _ _).trans ?_
      rw [abs_sub_comm (c n x) (ψ x)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact max_le (Real.exp_le_exp.2 (le_of_abs_le (hcb n x)))
        (Real.exp_le_exp.2 (le_of_abs_le (hb x)))
    calc (∫ x, |Real.exp (c n x) - Real.exp (ψ x)| ∂Q)
        ≤ ∫ x, Real.exp k * |ψ x - c n x| ∂Q :=
          integral_mono (((hexpint Q n).sub (hexpψint Q)).abs)
            (((hψint Q).sub (hcint Q n)).abs.const_mul _) hpt
      _ = Real.exp k * ∫ x, |ψ x - c n x| ∂Q := integral_const_mul _ _
      _ ≤ Real.exp k * (1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hL1 n).2 (Real.exp_pos _).le
  have hpos : 0 < ∫ x, Real.exp (ψ x) ∂Q := integral_exp_pos (hexpψint Q)
  have hT3 := (hT1.sub (hT2.log hpos.ne'))
  have hT4 := ENNReal.tendsto_ofReal hT3
  refine le_of_tendsto' hT4 fun n => ?_
  exact le_iSup (fun φ : C(α, ℝ) => ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q))) (c n)



/-- Step function used when `P ≪̸ Q`: for a closed `A` with `Q A = 0 < P A` and `k ≥ 0`, there is a
continuous `φ` with `∫ φ dP ≥ k · P A` and `∫ e^φ dQ ≤ 2`. -/
lemma b15dv_indicator_like {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set α) (hA : IsClosed A) (hPA : 0 < P A) (hQA : Q A = 0) (k : ℝ) (hk : 0 ≤ k) :
    ∃ φ : C(α, ℝ), k * P.real A ≤ ∫ x, φ x ∂P ∧ ∫ x, Real.exp (φ x) ∂Q ≤ 2 := by
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [h] at hPA
  have hlim : Tendsto (fun r => Q (thickening r A)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_measure_thickening_of_isClosed (μ := Q) (s := A)
      ⟨1, one_pos, measure_ne_top _ _⟩ hA
    rwa [hQA] at this
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), Q (thickening r A) < ENNReal.ofReal (Real.exp (-k)) :=
    (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 (Real.exp_pos _))
  obtain ⟨r, hr, hrpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hrpos' : (0 : ℝ) < r := hrpos
  let φ : C(α, ℝ) := ⟨fun x => k * (1 - min 1 (infDist x A / r)), by
    have := continuous_infDist_pt A
    fun_prop⟩
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => by
    have : min 1 (infDist x A / r) ≤ 1 := min_le_left _ _
    simp only [φ, ContinuousMap.coe_mk]
    exact mul_nonneg hk (by linarith)
  have hφk : ∀ x, φ x ≤ k := fun x => by
    have : 0 ≤ min 1 (infDist x A / r) :=
      le_min zero_le_one (div_nonneg infDist_nonneg hrpos'.le)
    simp only [φ, ContinuousMap.coe_mk]
    nlinarith
  have hφA : ∀ x ∈ A, φ x = k := fun x hx => by
    simp [φ, infDist_zero_of_mem hx]
  have hφout : ∀ x, x ∉ thickening r A → φ x = 0 := fun x hx => by
    rw [mem_thickening_iff_infDist_lt hne, not_lt] at hx
    have : 1 ≤ infDist x A / r := (one_le_div hrpos').2 hx
    simp [φ, min_eq_left this]
  have hφint : ∀ (ν : Measure α) [IsFiniteMeasure ν], Integrable φ ν := fun ν _ =>
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨φ, ?_, ?_⟩
  · calc k * P.real A = ∫ x in A, k ∂P := by
          simp [Measure.real, mul_comm]
      _ = ∫ x in A, φ x ∂P := setIntegral_congr_fun hA.measurableSet (fun x hx => (hφA x hx).symm)
      _ ≤ ∫ x, φ x ∂P := setIntegral_le_integral (hφint P) (Eventually.of_forall hφ0)
  · have hexpint : Integrable (fun x => Real.exp (φ x)) Q :=
      (Real.continuous_exp.comp φ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hpt : ∀ x, Real.exp (φ x) ≤ 1 + (thickening r A).indicator (fun _ => Real.exp k) x := by
      intro x
      by_cases hx : x ∈ thickening r A
      · rw [indicator_of_mem hx]
        have := Real.exp_le_exp.2 (hφk x)
        linarith [Real.exp_pos (φ x)]
      · rw [indicator_of_notMem hx, hφout x hx]; simp
    have hind : Integrable ((thickening r A).indicator (fun _ => Real.exp k)) Q :=
      (integrable_const _).indicator isOpen_thickening.measurableSet
    calc ∫ x, Real.exp (φ x) ∂Q
        ≤ ∫ x, (1 + (thickening r A).indicator (fun _ => Real.exp k) x) ∂Q :=
          integral_mono hexpint ((integrable_const _).add hind) hpt
      _ = 1 + Real.exp k * Q.real (thickening r A) := by
          rw [integral_add (integrable_const _) hind, integral_indicator_const _
            isOpen_thickening.measurableSet]
          simp [Measure.real, mul_comm]
      _ ≤ 1 + 1 := by
          have h1 : Q.real (thickening r A) ≤ Real.exp (-k) :=
            ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hr.le
          have : Real.exp k * Real.exp (-k) = 1 := by rw [← Real.exp_add]; simp
          have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos k).le
          linarith
      _ = 2 := by norm_num

/-- If `P ≪̸ Q` the Donsker-Varadhan supremum is `⊤`. -/
theorem b15dv_iSup_eq_top_of_not_ac {α : Type*} [MetricSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hac : ¬ P ≪ Q) :
    (⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q))) = ⊤ := by
  obtain ⟨S, hQS, hPS⟩ : ∃ S, Q S = 0 ∧ P S ≠ 0 := by
    by_contra h
    exact hac fun s hs => by
      by_contra h'
      exact h ⟨s, hs, h'⟩
  obtain ⟨T, hST, hTm, hQT⟩ := exists_measurable_superset_of_null hQS
  have hPT : P T ≠ 0 := fun h => hPS (measure_mono_null hST h)
  obtain ⟨A, hAT, hAc, hA⟩ := hTm.exists_isClosed_lt_add (μ := P) (measure_ne_top _ _)
    (ε := P T / 2) (by simp [hPT])
  have hPA : 0 < P A := by
    by_contra h
    rw [not_lt, nonpos_iff_eq_zero] at h
    rw [h, zero_add] at hA
    exact absurd hA (not_lt.2 (ENNReal.half_le_self))
  have hQA : Q A = 0 := measure_mono_null hAT hQT
  have hp : 0 < P.real A := ENNReal.toReal_pos hPA.ne' (measure_ne_top _ _)
  by_contra hne
  set R := (⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)))
    with hR
  obtain ⟨k, hk⟩ := exists_nat_gt ((R.toReal + Real.log 2) / P.real A)
  have hk0 : (0 : ℝ) ≤ k := by
    have : 0 ≤ (R.toReal + Real.log 2) / P.real A :=
      div_nonneg (add_nonneg ENNReal.toReal_nonneg (Real.log_nonneg (by norm_num))) hp.le
    linarith
  obtain ⟨φ, h1, h2⟩ := b15dv_indicator_like P Q A hAc hPA hQA k hk0
  have hexpint : Integrable (fun x => Real.exp (φ x)) Q :=
    (Real.continuous_exp.comp φ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpos := integral_exp_pos hexpint
  have h3 : Real.log (∫ x, Real.exp (φ x) ∂Q) ≤ Real.log 2 := Real.log_le_log hpos h2
  have h4 : ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)) ≤ R :=
    le_iSup (fun φ : C(α, ℝ) => ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q))) φ
  rw [ENNReal.ofReal_le_iff_le_toReal hne] at h4
  rw [div_lt_iff₀ hp] at hk
  linarith



/-- Truncation of the (positive) density `t` to `[e^{-k}, e^k]`, followed by `log`. -/
def b15dv_trunc (k : ℕ) (t : ℝ) : ℝ :=
  Real.log (max (Real.exp (-(k : ℝ))) (min (Real.exp (k : ℝ)) t))

lemma b15dv_trunc_eq (k : ℕ) (t : ℝ) (ht : 0 < t) :
    b15dv_trunc k t = max (-(k : ℝ)) (min (k : ℝ) (Real.log t)) := by
  have hmono : MonotoneOn Real.log (Ioi (0 : ℝ)) := Real.strictMonoOn_log.monotoneOn
  have h1 : min (Real.exp (k : ℝ)) t ∈ Ioi (0 : ℝ) := lt_min (Real.exp_pos _) ht
  have h2 : Real.exp (-(k : ℝ)) ∈ Ioi (0 : ℝ) := Real.exp_pos _
  have h3 : Real.exp (k : ℝ) ∈ Ioi (0 : ℝ) := Real.exp_pos _
  unfold b15dv_trunc
  rw [hmono.map_max h2 h1, hmono.map_min h3 ht, Real.log_exp, Real.log_exp]

lemma b15dv_trunc_abs_le (k : ℕ) (t : ℝ) : |b15dv_trunc k t| ≤ k := by
  unfold b15dv_trunc
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hpos : 0 < max (Real.exp (-(k : ℝ))) (min (Real.exp (k : ℝ)) t) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  have hle : max (Real.exp (-(k : ℝ))) (min (Real.exp (k : ℝ)) t) ≤ Real.exp k :=
    max_le (Real.exp_le_exp.2 (by linarith)) (min_le_left _ _)
  rw [abs_le]
  constructor
  · calc -(k : ℝ) = Real.log (Real.exp (-(k : ℝ))) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (le_max_left _ _)
  · calc _ ≤ Real.log (Real.exp (k : ℝ)) := Real.log_le_log hpos hle
      _ = k := Real.log_exp _

lemma b15dv_exp_trunc_le (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (b15dv_trunc k t) ≤ t + Real.exp (-(k : ℝ)) := by
  unfold b15dv_trunc
  have hpos : 0 < max (Real.exp (-(k : ℝ))) (min (Real.exp (k : ℝ)) t) :=
    lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)
  rw [Real.exp_log hpos]
  refine max_le ?_ ?_
  · linarith
  · have := min_le_right (Real.exp (k : ℝ)) t
    linarith [Real.exp_pos (-(k : ℝ))]

lemma b15dv_trunc_abs_le_log (k : ℕ) (t : ℝ) (ht : 0 < t) :
    |b15dv_trunc k t| ≤ |Real.log t| := by
  rw [b15dv_trunc_eq k t ht]
  simp only [abs_le, max_def, min_def]
  have := le_abs_self (Real.log t)
  have := neg_abs_le (Real.log t)
  split_ifs <;> constructor <;> linarith [abs_nonneg (Real.log t)]

lemma b15dv_trunc_eq_log (k : ℕ) (t : ℝ) (ht : 0 < t) (hk : |Real.log t| ≤ k) :
    b15dv_trunc k t = Real.log t := by
  rw [b15dv_trunc_eq k t ht]
  rw [abs_le] at hk
  rw [min_eq_right hk.2, max_eq_right hk.1]

lemma b15dv_trunc_ge (k : ℕ) (t : ℝ) (ht : 0 < t) :
    min (max (Real.log t) 0) (k : ℝ) - max (-Real.log t) 0 ≤ b15dv_trunc k t := by
  rw [b15dv_trunc_eq k t ht]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma b15dv_mul_negPart_log_le (t : ℝ) (ht : 0 ≤ t) : t * max (-Real.log t) 0 ≤ 1 := by
  rcases ht.eq_or_lt with h | h
  · simp [← h]
  · rcases le_total (-Real.log t) 0 with h1 | h1
    · rw [max_eq_right h1]; simp
    · rw [max_eq_left h1]
      have h2 : -Real.log t ≤ t⁻¹ - 1 := by
        have := Real.log_le_sub_one_of_pos (inv_pos.2 h)
        rwa [Real.log_inv] at this
      calc t * (-Real.log t) ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 ht
        _ = 1 - t := by field_simp
        _ ≤ 1 := by linarith

lemma b15dv_llr_negPart_integrable {α : Type*} [MeasurableSpace α] (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hac : P ≪ Q) :
    Integrable (fun x => max (-llr P Q x) 0) P := by
  have hm : Measurable fun x => max (-llr P Q x) 0 := (measurable_llr P Q).neg.max measurable_const
  have hmeas : Measurable fun x => ENNReal.ofReal (max (-llr P Q x) 0) := hm.ennreal_ofReal
  have hfin : ∫⁻ x, ENNReal.ofReal (max (-llr P Q x) 0) ∂P ≠ ⊤ := by
    rw [← lintegral_rnDeriv_mul hac hmeas.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _, 1 ∂Q) (by simp) ?_
    refine lintegral_mono_ae ?_
    filter_upwards [Measure.rnDeriv_ne_top P Q] with x hx
    have : P.rnDeriv Q x = ENNReal.ofReal (P.rnDeriv Q x).toReal := (ENNReal.ofReal_toReal hx).symm
    rw [this, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (b15dv_mul_negPart_log_le _ ENNReal.toReal_nonneg)
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall fun x => le_max_right _ _)).1 hfin

/-- A nonnegative measurable function whose truncations have bounded integrals is integrable. -/
lemma b15dv_integrable_of_trunc_bound {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] (h : α → ℝ) (hm : Measurable h) (hnn : ∀ x, 0 ≤ h x) (B : ℝ)
    (hB : ∀ k : ℕ, ∫ x, min (h x) (k : ℝ) ∂ν ≤ B) : Integrable h ν := by
  have hint : ∀ k : ℕ, Integrable (fun x => min (h x) (k : ℝ)) ν := fun k =>
    Integrable.of_bound (hm.min measurable_const).aestronglyMeasurable k
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn x) (Nat.cast_nonneg _))]
        exact min_le_right _ _)
  have h1 : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (min (h x) (k : ℝ)) ∂ν ≤ ENNReal.ofReal B := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
      (Eventually.of_forall fun x => le_min (hnn x) (Nat.cast_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have h2 : ∫⁻ x, ENNReal.ofReal (h x) ∂ν ≤ ENNReal.ofReal B := by
    have : ∀ x, ENNReal.ofReal (h x) = ⨆ k : ℕ, ENNReal.ofReal (min (h x) (k : ℝ)) := by
      intro x
      refine le_antisymm ?_ (iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      obtain ⟨k, hk⟩ := exists_nat_ge (h x)
      refine le_iSup_of_le k ?_
      rw [min_eq_left hk]
    simp_rw [this]
    rw [lintegral_iSup (fun k => (hm.min measurable_const).ennreal_ofReal)]
    · exact iSup_le h1
    · intro k l hkl x
      exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hkl))
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall hnn)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2)


/-- The approximation direction when `P ≪ Q`. -/
theorem b15dv_klDiv_le_iSup_of_ac {α : Type*} [MetricSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (P Q : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hac : P ≪ Q) :
    klDiv P Q ≤
      ⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)) := by
  set R := (⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)))
    with hR
  set f : α → ℝ := fun x => (P.rnDeriv Q x).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv P Q).ennreal_toReal
  have hfint : Integrable f Q := Measure.integrable_toReal_rnDeriv
  have hfone : ∫ x, f x ∂Q = 1 := by
    rw [hf]; simp only; rw [Measure.integral_toReal_rnDeriv hac]; simp
  have hψm : ∀ k : ℕ, Measurable fun x => b15dv_trunc k (f x) := fun k =>
    Measurable.log (measurable_const.max (measurable_const.min hfm))
  have hψint : ∀ (ν : Measure α) [IsFiniteMeasure ν] (k : ℕ),
      Integrable (fun x => b15dv_trunc k (f x)) ν := fun ν _ k =>
    Integrable.of_bound (hψm k).aestronglyMeasurable k
      (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using b15dv_trunc_abs_le k (f x))
  have hexpψ : ∀ k : ℕ, Integrable (fun x => Real.exp (b15dv_trunc k (f x))) Q := fun k =>
    Integrable.of_bound (Real.measurable_exp.comp (hψm k)).aestronglyMeasurable (Real.exp k)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_of_abs_le (b15dv_trunc_abs_le k (f x))))
  have hbound : ∀ k : ℕ,
      ENNReal.ofReal (∫ x, b15dv_trunc k (f x) ∂P - Real.exp (-(k : ℝ))) ≤ R := by
    intro k
    have h1 := b15dv_le_iSup_bdd P Q (fun x => b15dv_trunc k (f x)) (hψm k) k (Nat.cast_nonneg _)
      (fun x => b15dv_trunc_abs_le k (f x))
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h1
    have hI : ∫ x, Real.exp (b15dv_trunc k (f x)) ∂Q ≤ 1 + Real.exp (-(k : ℝ)) := by
      calc ∫ x, Real.exp (b15dv_trunc k (f x)) ∂Q ≤ ∫ x, (f x + Real.exp (-(k : ℝ))) ∂Q :=
            integral_mono (hexpψ k) (hfint.add (integrable_const _))
              (fun x => b15dv_exp_trunc_le k (f x) ENNReal.toReal_nonneg)
        _ = 1 + Real.exp (-(k : ℝ)) := by
            rw [integral_add hfint (integrable_const _), hfone]; simp
    have hpos := integral_exp_pos (hexpψ k)
    have h2 : Real.log (∫ x, Real.exp (b15dv_trunc k (f x)) ∂Q) ≤ Real.exp (-(k : ℝ)) := by
      calc _ ≤ Real.log (1 + Real.exp (-(k : ℝ))) := Real.log_le_log hpos hI
        _ ≤ 1 + Real.exp (-(k : ℝ)) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
        _ = _ := by ring
    linarith
  have hposae : ∀ᵐ x ∂P, 0 < f x := by
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_ne_top P Q)] with x h1 h2
    exact ENNReal.toReal_pos h1.ne' h2
  have hexpt : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  by_cases hint : Integrable (llr P Q) P
  · rw [klDiv_of_ac_of_integrable hac hint]
    have hlim : Tendsto (fun k : ℕ => ∫ x, b15dv_trunc k (f x) ∂P) atTop
        (𝓝 (∫ x, llr P Q x ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => |llr P Q x|)
        (fun k => (hψm k).aestronglyMeasurable) hint.abs ?_ ?_
      · intro k
        filter_upwards [hposae] with x hx
        have hl : llr P Q x = Real.log (f x) := rfl
        rw [hl]
        simpa [Real.norm_eq_abs] using b15dv_trunc_abs_le_log k (f x) hx
      · filter_upwards [hposae] with x hx
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨K, hK⟩ := exists_nat_ge |Real.log (f x)|
        filter_upwards [eventually_ge_atTop K] with k hk
        exact (b15dv_trunc_eq_log k (f x) hx (hK.trans (by exact_mod_cast hk))).symm
    have hT := ENNReal.tendsto_ofReal (hlim.sub hexpt)
    refine le_of_tendsto' hT hbound |> fun h => ?_
    simpa [probReal_univ] using h
  · -- `llr` not integrable: the supremum is `⊤`
    refine le_trans (le_of_eq (klDiv_of_not_integrable hint)) ?_
    by_contra hne
    have hne' : R ≠ ⊤ := by
      intro h; exact hne (by rw [h])
    have hC := b15dv_llr_negPart_integrable P Q hac
    set C := ∫ x, max (-llr P Q x) 0 ∂P with hCdef
    have hposInt : Integrable (fun x => max (llr P Q x) 0) P := by
      refine b15dv_integrable_of_trunc_bound P _ ((measurable_llr P Q).max measurable_const)
        (fun x => le_max_right _ _) (R.toReal + 1 + C) fun k => ?_
      have h1 : ∫ x, min (max (llr P Q x) 0) (k : ℝ) - max (-llr P Q x) 0 ∂P ≤
          ∫ x, b15dv_trunc k (f x) ∂P := by
        refine integral_mono_ae ?_ (hψint P k) ?_
        · refine Integrable.sub ?_ hC
          exact Integrable.of_bound
            ((measurable_llr P Q).max measurable_const |>.min measurable_const).aestronglyMeasurable k
            (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (Nat.cast_nonneg _))]
              exact min_le_right _ _)
        · filter_upwards [hposae] with x hx
          exact b15dv_trunc_ge k (f x) hx
      have h2 : ∫ x, b15dv_trunc k (f x) ∂P - Real.exp (-(k : ℝ)) ≤ R.toReal := by
        have := hbound k
        rwa [ENNReal.ofReal_le_iff_le_toReal hne'] at this
      have h3 : Real.exp (-(k : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; simp
      have h4 : ∫ x, min (max (llr P Q x) 0) (k : ℝ) - max (-llr P Q x) 0 ∂P =
          ∫ x, min (max (llr P Q x) 0) (k : ℝ) ∂P - C := by
        rw [integral_sub ?_ hC]
        exact Integrable.of_bound
            ((measurable_llr P Q).max measurable_const |>.min measurable_const).aestronglyMeasurable k
            (Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (Nat.cast_nonneg _))]
              exact min_le_right _ _)
      linarith
    apply hint
    have := hposInt.sub hC
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rcases le_total (llr P Q x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- **Donsker-Varadhan variational formula** (relocated proof of `b15b_klDiv_eq_iSup`). -/
theorem b15b_klDiv_eq_iSup_proof {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    InformationTheory.klDiv P Q =
      ⨆ φ : C(α, ℝ), ENNReal.ofReal (∫ x, φ x ∂P - Real.log (∫ x, Real.exp (φ x) ∂Q)) := by
  by_cases hac : P ≪ Q
  · refine le_antisymm (b15dv_klDiv_le_iSup_of_ac P Q hac) (iSup_le fun φ => ?_)
    have hφ : Continuous φ := φ.continuous
    exact b15dv_gibbs P Q φ
      (hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((Real.continuous_exp.comp hφ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  · rw [klDiv_of_not_ac hac, b15dv_iSup_eq_top_of_not_ac P Q hac]

end HRS
