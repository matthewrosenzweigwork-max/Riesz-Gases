import HRS.MC.S7WQAux2

/-!
# Packet `s7_WQ_weak_ui_wasserstein`, helper 3: moment and tail estimates
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.WQ

open HRS

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- Splitting a `q`-th moment against a `(q+δ)`-th moment. -/
lemma wq_split {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ}
    (hR : 0 < R) (x : B) :
    t * ‖x‖ ^ q ≤ R ^ q * t + R ^ (-δ) * ‖x‖ ^ (q + δ) := by
  have hxn : 0 ≤ ‖x‖ ^ (q + δ) := Real.rpow_nonneg (norm_nonneg _) _
  have hRn : 0 ≤ R ^ (-δ) := Real.rpow_nonneg hR.le _
  have hRq : 0 ≤ R ^ q := Real.rpow_nonneg hR.le _
  by_cases hx : ‖x‖ ≤ R
  · have h1 : ‖x‖ ^ q ≤ R ^ q := Real.rpow_le_rpow (norm_nonneg _) hx hq.le
    calc t * ‖x‖ ^ q ≤ t * R ^ q := mul_le_mul_of_nonneg_left h1 ht0
      _ = R ^ q * t := mul_comm _ _
      _ ≤ _ := by have := mul_nonneg hRn hxn; linarith
  · rw [not_le] at hx
    have hx0 : 0 < ‖x‖ := hR.trans hx
    have h2 : ‖x‖ ^ q = ‖x‖ ^ (q + δ) * ‖x‖ ^ (-δ) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h3 : ‖x‖ ^ (-δ) ≤ R ^ (-δ) := Real.rpow_le_rpow_of_nonpos hR hx.le (by linarith)
    have hxq : 0 ≤ ‖x‖ ^ q := Real.rpow_nonneg (norm_nonneg _) _
    calc t * ‖x‖ ^ q ≤ 1 * ‖x‖ ^ q := mul_le_mul_of_nonneg_right ht1 hxq
      _ = ‖x‖ ^ (q + δ) * ‖x‖ ^ (-δ) := by rw [one_mul, h2]
      _ ≤ ‖x‖ ^ (q + δ) * R ^ (-δ) := mul_le_mul_of_nonneg_left h3 hxn
      _ = R ^ (-δ) * ‖x‖ ^ (q + δ) := mul_comm _ _
      _ ≤ _ := by have := mul_nonneg hRq ht0; linarith

lemma wq_integrable_q {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) (ρ : Measure B) [IsProbabilityMeasure ρ]
    (h : Integrable (fun x : B => ‖x‖ ^ (q + δ)) ρ) : Integrable (fun x : B => ‖x‖ ^ q) ρ := by
  refine (h.add (integrable_const (1 : ℝ))).mono'
    (continuous_norm.rpow_const fun _ => Or.inr hq.le).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hx : ‖x‖ ≤ 1
  · have : ‖x‖ ^ q ≤ 1 := Real.rpow_le_one (norm_nonneg _) hx hq.le
    have h0 : 0 ≤ ‖x‖ ^ (q + δ) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [Pi.add_apply]; linarith
  · rw [not_le] at hx
    have : ‖x‖ ^ q ≤ ‖x‖ ^ (q + δ) := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    simp only [Pi.add_apply]; linarith

/-- The tail integral against a `(q+δ)`-bounded measure is small once the tail mass is. -/
lemma wq_tail_moment_le {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) (ρ : Measure B) [IsProbabilityMeasure ρ]
    {C : ℝ} (hint : Integrable (fun x : B => ‖x‖ ^ (q + δ)) ρ)
    (hC : ∫ x, ‖x‖ ^ (q + δ) ∂ρ ≤ C) {R : ℝ} (hR : 0 < R) {s : ℝ} (c : ℕ → B) (N : ℕ) :
    ∫ x, tailF s c N x * ‖x‖ ^ q ∂ρ ≤ R ^ q * ∫ x, tailF s c N x ∂ρ + R ^ (-δ) * C := by
  have hiq := wq_integrable_q hq hδ ρ hint
  have ht : Integrable (fun x : B => tailF s c N x) ρ :=
    Integrable.of_bound (continuous_tailF s c N).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tailF_nonneg s c N x)]; exact tailF_le_one s c N x)
  have hrhs : Integrable (fun x : B => R ^ q * tailF s c N x + R ^ (-δ) * ‖x‖ ^ (q + δ)) ρ :=
    (ht.const_mul _).add (hint.const_mul _)
  calc ∫ x, tailF s c N x * ‖x‖ ^ q ∂ρ
      ≤ ∫ x, (R ^ q * tailF s c N x + R ^ (-δ) * ‖x‖ ^ (q + δ)) ∂ρ :=
        integral_mono (integrable_tail_rpow hq c N ρ hiq) hrhs fun x =>
          wq_split hq hδ (tailF_nonneg s c N x) (tailF_le_one s c N x) hR x
    _ = R ^ q * ∫ x, tailF s c N x ∂ρ + R ^ (-δ) * ∫ x, ‖x‖ ^ (q + δ) ∂ρ := by
        rw [integral_add (ht.const_mul _) (hint.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have : 0 ≤ R ^ (-δ) := Real.rpow_nonneg hR.le _
        have := mul_le_mul_of_nonneg_left hC this
        linarith

/-- Lower semicontinuity of the `(q+δ)`-moment under weak convergence. -/
lemma wq_limit_moment {r : ℝ} (hr : 0 < r) (μ : ℕ → Measure B) [∀ N, IsProbabilityMeasure (μ N)]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (hweak : ∀ F : B → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun N => ∫ x, F x ∂(μ N)) atTop (𝓝 (∫ x, F x ∂ν)))
    {C : ℝ} (hmom : ∀ N, Integrable (fun x : B => ‖x‖ ^ r) (μ N) ∧ ∫ x, ‖x‖ ^ r ∂(μ N) ≤ C) :
    Integrable (fun x : B => ‖x‖ ^ r) ν ∧ ∫ x, ‖x‖ ^ r ∂ν ≤ C := by
  set g : B → ℝ := fun x => ‖x‖ ^ r with hg
  have hgc : Continuous g := continuous_norm.rpow_const fun _ => Or.inr hr.le
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  set F : ℕ → B → ℝ := fun M x => min (g x) M with hF
  have hFc : ∀ M, Continuous (F M) := fun M => hgc.min continuous_const
  have hFb : ∀ M : ℕ, ∃ K, ∀ x, |F M x| ≤ K := fun M => ⟨M, fun x => by
    rw [abs_of_nonneg (le_min (hg0 x) (Nat.cast_nonneg M))]; exact min_le_right _ _⟩
  have hFint : ∀ M (ρ : Measure B) [IsProbabilityMeasure ρ], Integrable (F M) ρ := fun M ρ _ =>
    Integrable.of_bound (hFc M).aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg0 x) (Nat.cast_nonneg M))]; exact min_le_right _ _)
  have hFC : ∀ M, ∫ x, F M x ∂ν ≤ C := fun M => by
    refine le_of_tendsto (hweak (F M) (hFc M) (hFb M)) (Filter.Eventually.of_forall fun N => ?_)
    exact (integral_mono (hFint M (μ N)) (hmom N).1 fun x => min_le_left _ _).trans (hmom N).2
  -- monotone convergence
  have hlint : ∀ M, ∫⁻ x, ENNReal.ofReal (F M x) ∂ν ≤ ENNReal.ofReal C := fun M => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint M ν)
      (Filter.Eventually.of_forall fun x => le_min (hg0 x) (Nat.cast_nonneg M))]
    exact ENNReal.ofReal_le_ofReal (hFC M)
  have hmono : ∀ x, Monotone fun M : ℕ => ENNReal.ofReal (F M x) := fun x M M' h =>
    ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast h))
  have htend : ∀ x, Tendsto (fun M : ℕ => ENNReal.ofReal (F M x)) atTop (𝓝 (ENNReal.ofReal (g x))) := by
    intro x
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈g x⌉₊) fun M hM => ?_
    have : g x ≤ M := (Nat.le_ceil _).trans (by exact_mod_cast hM)
    simp only [hF, min_eq_left this]
  have hT := lintegral_tendsto_of_tendsto_of_monotone
    (fun M => (ENNReal.measurable_ofReal.comp (hFc M).measurable).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall htend) (μ := ν)
  have hle : ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≤ ENNReal.ofReal C := le_of_tendsto' hT hlint
  have hI : Integrable g ν := by
    refine (lintegral_ofReal_ne_top_iff_integrable hgc.aestronglyMeasurable
      (Filter.Eventually.of_forall hg0)).1 ((hle.trans_lt ENNReal.ofReal_lt_top).ne)
  refine ⟨hI, ?_⟩
  have hC0 : 0 ≤ C := (integral_nonneg hg0).trans (hmom 0).2
  rw [← ENNReal.ofReal_le_ofReal_iff hC0, ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall hg0)]
  exact hle

lemma wq_tail_nu {s : ℝ} (hs : 0 < s) {c : ℕ → B} (hc : DenseRange c) (ν : Measure B)
    [IsProbabilityMeasure ν] :
    Tendsto (fun N => ∫ x, tailF s c N x ∂ν) atTop (𝓝 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun N x => tailF s c N x) (f := fun _ => (0:ℝ)) (bound := fun _ => 1)
    (fun N => (continuous_tailF s c N).aestronglyMeasurable) (integrable_const _)
    (fun N => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailF_nonneg s c N x)]; exact tailF_le_one s c N x)
    (Filter.Eventually.of_forall fun x => by
      obtain ⟨N₀, hN₀⟩ := tailF_eventually_zero hs hc x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
      rw [hN₀ N hN])
  simpa using this

end HRS.MC.Sec7.WQ
