import Mathlib

/-!
# MOVSPEC auxiliary lemmas (Mathlib only)

Pure real-analysis / measure-theory lemmas used by the glue of `HRS/PDE/MovSpec1.lean`-`MovSpec3.lean`:

* `movspec_gronwall`: integral Gronwall for an integrable source `G` and a (not necessarily measurable)
  function `u` with `u t ≤ H0 + ∫_0^t G`, `G ≤ A u + B`;
* `movspec_ent_assembly`: passage to the limit `n → ∞` in `H_n(t) ≤ H_n(0) + I_n(t)` with a lower
  semicontinuity input;
* `movspec_int_le`: the entropy inequality `∫ |S| dν ≤ (H(ν|Q) + C)/l` from an exponential moment of `S` under `Q`.
-/

noncomputable section

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal

namespace HRS

/-! ### Integral Gronwall -/

/-- Integral Gronwall inequality.  `G` is integrable on `[0,T]`, `u t ≤ H0 + ∫_{[0,t]} G` for `t ∈ [0,T]` and
`G r ≤ A u r + B` on `[0,T]` (`A ≥ 0`).  Then `u t ≤ H0 + gronwallBound 0 A (A H0 + B) t`.  No measurability
of `u` is used (it enters only through the pointwise inequality `G ≤ A u + B`). -/
theorem movspec_gronwall {T A B H0 : ℝ} (hA : 0 ≤ A) {G u : ℝ → ℝ}
    (hG : IntegrableOn G (Set.Icc 0 T))
    (hu : ∀ t ∈ Set.Icc 0 T, u t ≤ H0 + ∫ r in Set.Icc 0 t, G r)
    (hGu : ∀ r ∈ Set.Icc 0 T, G r ≤ A * u r + B) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ H0 + gronwallBound 0 A (A * H0 + B) t := by
  classical
  set G' : ℝ → ℝ := Set.indicator (Set.Icc 0 T) G with hG'
  have hG'int : Integrable G' := (integrable_indicator_iff measurableSet_Icc).2 hG
  have hG'ii : ∀ a b : ℝ, IntervalIntegrable G' volume a b := fun a b => hG'int.intervalIntegrable
  set Φ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, G' s with hΦ
  have hΦc : Continuous Φ := intervalIntegral.continuous_primitive hG'ii 0
  have hΦeq : ∀ t ∈ Set.Icc 0 T, Φ t = ∫ r in Set.Icc 0 t, G r := by
    intro t ht
    simp only [hΦ]
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    simp only [hG']
    rw [Set.indicator_of_mem (Set.Icc_subset_Icc le_rfl ht.2 hx)]
  set ψ : ℝ → ℝ := fun s => A * (H0 + Φ s) + B with hψ
  have hψc : Continuous ψ := by simp only [hψ]; fun_prop
  have hψii : ∀ a b : ℝ, IntervalIntegrable ψ volume a b := fun a b => hψc.intervalIntegrable a b
  set Θ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ψ s with hΘ
  have hΘc : Continuous Θ := intervalIntegral.continuous_primitive hψii 0
  have hΘd : ∀ x, HasDerivAt Θ (ψ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hψii 0 x)
      (hψc.stronglyMeasurableAtFilter volume (𝓝 x)) hψc.continuousAt
  -- pointwise bound of the integrand
  have hGψ : ∀ s ∈ Set.Icc 0 T, G' s ≤ ψ s := by
    intro s hs
    simp only [hG', hψ]
    rw [Set.indicator_of_mem hs]
    have h1 := hGu s hs
    have h2 := hu s hs
    rw [← hΦeq s hs] at h2
    nlinarith
  have hΦΘ : ∀ t ∈ Set.Icc 0 T, Φ t ≤ Θ t := by
    intro t ht
    simp only [hΦ, hΘ]
    refine intervalIntegral.integral_mono_on ht.1 (hG'ii _ _) (hψii _ _) fun s hs => ?_
    exact hGψ s ⟨hs.1, hs.2.trans ht.2⟩
  have hΘ0 : Θ 0 = 0 := by simp [hΘ]
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) T, ψ x ≤ A * Θ x + (A * H0 + B) := by
    intro x hx
    have := hΦΘ x ⟨hx.1, hx.2.le⟩
    simp only [hψ]
    nlinarith
  have hlim : ∀ x ∈ Set.Ico (0 : ℝ) T, ∀ r : ℝ, ψ x < r →
      ∃ᶠ z in nhdsWithin x (Set.Ioi x), (z - x)⁻¹ * (Θ z - Θ x) < r := by
    intro x _ r hr
    exact ((hΘd x).hasDerivWithinAt.liminf_right_slope_le hr).mono fun z hz => by
      simpa [slope] using hz
  have hG := le_gronwallBound_of_liminf_deriv_right_le (f := Θ) (f' := ψ) (δ := 0) (K := A)
    (ε := A * H0 + B) (a := 0) (b := T) hΘc.continuousOn hlim (by simp [hΘ0]) hbound
  intro t ht
  have h1 := hu t ht
  rw [← hΦeq t ht] at h1
  have h2 := hG t ht
  rw [sub_zero] at h2
  linarith [hΦΘ t ht]


/-- Clean form of `movspec_gronwall`: for `B ≥ 0`, `u t ≤ (H0 + B t) e^{A t}`. -/
theorem movspec_gronwall_exp {T A B H0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {G u : ℝ → ℝ}
    (hG : IntegrableOn G (Set.Icc 0 T))
    (hu : ∀ t ∈ Set.Icc 0 T, u t ≤ H0 + ∫ r in Set.Icc 0 t, G r)
    (hGu : ∀ r ∈ Set.Icc 0 T, G r ≤ A * u r + B) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ (H0 + B * t) * Real.exp (A * t) := by
  intro t ht
  have h := movspec_gronwall hA hG hu hGu t ht
  refine h.trans ?_
  have ht0 : 0 ≤ t := ht.1
  rcases hA.eq_or_lt with hA0 | hApos
  · subst hA0
    rw [gronwallBound_K0]
    simp
  · rw [gronwallBound_of_K_ne_0 hApos.ne']
    simp only [zero_mul, zero_add]
    have hx : 1 - A * t ≤ Real.exp (-(A * t)) := by
      have := Real.add_one_le_exp (-(A * t)); linarith
    have he : Real.exp (A * t) * Real.exp (-(A * t)) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (A * t)
    have h1 : Real.exp (A * t) - 1 ≤ A * t * Real.exp (A * t) := by
      have := mul_le_mul_of_nonneg_left hx hpos.le
      nlinarith
    have h2 : (A * H0 + B) / A * (Real.exp (A * t) - 1) =
        H0 * (Real.exp (A * t) - 1) + B / A * (Real.exp (A * t) - 1) := by
      field_simp
    rw [h2]
    have h3 : B / A * (Real.exp (A * t) - 1) ≤ B * t * Real.exp (A * t) := by
      have : B / A * (Real.exp (A * t) - 1) ≤ B / A * (A * t * Real.exp (A * t)) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hB hA)
      calc _ ≤ _ := this
        _ = B * t * Real.exp (A * t) := by field_simp
    nlinarith

/-! ### Passage to the limit in the regularised inequality -/

/-- Assembly of the `ε → 0` limit: `H_n ≤ H_n^0 + I_n` (with `H_n < ∞`), `H_n^0 → a`, `I_n → b` (reals) and a
lower semicontinuity input `Hlim ≤ liminf H_n` give `Hlim < ∞` and `Hlim ≤ a + b`. -/
theorem movspec_ent_assembly {H H0 : ℕ → ℝ≥0∞} {I : ℕ → ℝ} {Hlim : ℝ≥0∞} {a b : ℝ}
    (hlsc : Hlim ≤ liminf H atTop)
    (hreg : ∀ n, H n ≠ ⊤ ∧ (H n).toReal ≤ (H0 n).toReal + I n)
    (h0 : Tendsto (fun n => (H0 n).toReal) atTop (𝓝 a))
    (hI : Tendsto I atTop (𝓝 b)) :
    Hlim ≠ ⊤ ∧ Hlim.toReal ≤ a + b := by
  have hy : Tendsto (fun n => (H0 n).toReal + I n) atTop (𝓝 (a + b)) := h0.add hI
  have hab : 0 ≤ a + b :=
    ge_of_tendsto' hy fun n => (ENNReal.toReal_nonneg).trans (hreg n).2
  have hHn : ∀ n, H n = ENNReal.ofReal (H n).toReal := fun n =>
    (ENNReal.ofReal_toReal (hreg n).1).symm
  have hle : ∀ n, H n ≤ ENNReal.ofReal ((H0 n).toReal + I n) := fun n => by
    rw [hHn n]; exact ENNReal.ofReal_le_ofReal (hreg n).2
  have hlim : Tendsto (fun n => ENNReal.ofReal ((H0 n).toReal + I n)) atTop
      (𝓝 (ENNReal.ofReal (a + b))) := ENNReal.tendsto_ofReal hy
  have h1 : liminf H atTop ≤ ENNReal.ofReal (a + b) := by
    calc liminf H atTop ≤ liminf (fun n => ENNReal.ofReal ((H0 n).toReal + I n)) atTop :=
          liminf_le_liminf (Eventually.of_forall hle)
      _ = ENNReal.ofReal (a + b) := hlim.liminf_eq
  have h2 : Hlim ≤ ENNReal.ofReal (a + b) := hlsc.trans h1
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2, ?_⟩
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rwa [ENNReal.toReal_ofReal hab] at this


/-! ### The entropy inequality for an exponentially integrable observable -/

open ProbabilityTheory in
/-- Gibbs variational inequality (the proof of `HRS.b15dv_gibbs`, `HRS/Appendix/B15BDV.lean`, copied here so that this
file depends on Mathlib only; replace by `b15dv_gibbs` if the file is ever moved behind `B15BDV`). -/
theorem movspec_gibbs {α : Type*} [MeasurableSpace α] (P Q : Measure α)
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

/-- **Entropy inequality.**  If `∫ e^{l|S|} dQ ≤ e^C` (`l > 0`) and `H(ν|Q) < ∞` (both probability measures, `S`
almost everywhere measurable for both) then `S` is `ν`-integrable and `∫ |S| dν ≤ (H(ν|Q) + C)/l`.  This is the step
"the exponential moment `N:eq:source-exp` and the entropy inequality control the source" of the TeX (M L8575-8576). -/
theorem movspec_int_le {α : Type*} [MeasurableSpace α] (ν Q : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure Q] {S : α → ℝ} (hSν : AEMeasurable S ν)
    (hSQ : AEMeasurable S Q) {l C : ℝ} (hl : 0 < l)
    (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (l * |S x|)) ∂Q ≤ ENNReal.ofReal (Real.exp C))
    (hH : klDiv ν Q ≠ ⊤) :
    Integrable S ν ∧ ∫ x, |S x| ∂ν ≤ ((klDiv ν Q).toReal + C) / l := by
  set H : ℝ := (klDiv ν Q).toReal with hHdef
  have hφm : ∀ (k : ℕ) (m : Measure α), AEMeasurable S m →
      AEMeasurable (fun x => min (l * |S x|) (k : ℝ)) m := fun k m hm =>
    (aemeasurable_const.mul hm.abs).min aemeasurable_const
  have hφb : ∀ k : ℕ, ∀ x, |min (l * |S x|) (k : ℝ)| ≤ k := fun k x => by
    have h0 : 0 ≤ min (l * |S x|) (k : ℝ) :=
      le_min (mul_nonneg hl.le (abs_nonneg _)) (Nat.cast_nonneg k)
    rw [abs_of_nonneg h0]; exact min_le_right _ _
  have hφi : ∀ (k : ℕ) (m : Measure α) [IsProbabilityMeasure m], AEMeasurable S m →
      Integrable (fun x => min (l * |S x|) (k : ℝ)) m := fun k m _ hm =>
    Integrable.of_bound (hφm k m hm).aestronglyMeasurable k (Eventually.of_forall fun x => by
      simpa using hφb k x)
  have hei : ∀ (k : ℕ), Integrable (fun x => Real.exp (min (l * |S x|) (k : ℝ))) Q := fun k =>
    Integrable.of_bound ((Real.measurable_exp.comp_aemeasurable (hφm k Q hSQ))).aestronglyMeasurable
      (Real.exp k)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (min_le_right _ _))
  -- each truncation satisfies the bound
  have hk : ∀ k : ℕ, ∫ x, min (l * |S x|) (k : ℝ) ∂ν ≤ H + C := by
    intro k
    have h1 := movspec_gibbs ν Q _ (hφi k ν hSν) (hei k)
    have h2 : ∫ x, Real.exp (min (l * |S x|) (k : ℝ)) ∂Q ≤ Real.exp C := by
      have hle : ∫⁻ x, ENNReal.ofReal (Real.exp (min (l * |S x|) (k : ℝ))) ∂Q ≤
          ENNReal.ofReal (Real.exp C) :=
        (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (min_le_left _ _))).trans hexp
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
        (hei k).aestronglyMeasurable]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
        (by rw [ENNReal.toReal_ofReal (Real.exp_pos _).le])
    have h3 : Real.log (∫ x, Real.exp (min (l * |S x|) (k : ℝ)) ∂Q) ≤ C := by
      have hpos : 0 < ∫ x, Real.exp (min (l * |S x|) (k : ℝ)) ∂Q :=
        integral_exp_pos (hei k)
      calc _ ≤ Real.log (Real.exp C) := Real.log_le_log hpos h2
        _ = C := Real.log_exp C
    have h4 := (ENNReal.ofReal_le_iff_le_toReal hH).1 h1
    linarith
  -- monotone limit
  have hmono : ∀ x, Monotone fun k : ℕ => ENNReal.ofReal (min (l * |S x|) (k : ℝ)) := fun x a b hab =>
    ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hab))
  have hsup : ∀ x, ⨆ k : ℕ, ENNReal.ofReal (min (l * |S x|) (k : ℝ)) = ENNReal.ofReal (l * |S x|) := by
    intro x
    apply le_antisymm
    · exact iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨k, hk'⟩ := exists_nat_ge (l * |S x|)
      exact le_iSup_of_le k (by rw [min_eq_left hk'])
  have hlint : ∫⁻ x, ENNReal.ofReal (l * |S x|) ∂ν ≤ ENNReal.ofReal (H + C) := by
    have : ∫⁻ x, ENNReal.ofReal (l * |S x|) ∂ν =
        ⨆ k : ℕ, ∫⁻ x, ENNReal.ofReal (min (l * |S x|) (k : ℝ)) ∂ν := by
      rw [← lintegral_iSup' (fun k => (hφm k ν hSν).ennreal_ofReal)
        (Eventually.of_forall fun x => hmono x)]
      exact lintegral_congr fun x => (hsup x).symm
    rw [this]
    refine iSup_le fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hφi k ν hSν)
      (Eventually.of_forall fun x => le_min (mul_nonneg hl.le (abs_nonneg _)) (Nat.cast_nonneg k))]
    exact ENNReal.ofReal_le_ofReal (hk k)
  have hlint' : ∫⁻ x, ENNReal.ofReal (l * |S x|) ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint
  have hint : Integrable (fun x => l * |S x|) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (aemeasurable_const.mul hSν.abs).aestronglyMeasurable
      (Eventually.of_forall fun x => mul_nonneg hl.le (abs_nonneg _))).1 hlint'
  have hSint : Integrable S ν := by
    have : Integrable (fun x => |S x|) ν := by
      have := hint.const_mul l⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hl.ne'] using this
    exact this.mono' hSν.aestronglyMeasurable (Eventually.of_forall fun x => by simp)
  refine ⟨hSint, ?_⟩
  have h5 : ∫ x, l * |S x| ∂ν ≤ H + C := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
      mul_nonneg hl.le (abs_nonneg _)) hint.aestronglyMeasurable]
    have h0 : 0 ≤ H + C := by
      have := hk 0
      have h00 : ∀ x, min (l * |S x|) ((0 : ℕ) : ℝ) = 0 := fun x => by
        rw [Nat.cast_zero]; exact min_eq_right (mul_nonneg hl.le (abs_nonneg (S x)))
      simp only [h00, integral_zero] at this
      exact this
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    rwa [ENNReal.toReal_ofReal h0] at this
  rw [integral_const_mul] at h5
  rw [le_div_iff₀ hl]
  linarith


/-! ### `L^p` norms of densities -/

/-- `‖dν/dQ‖_{L^p(Q)} ≥ 1` for probability measures `ν ≪ Q` and `p ≥ 1` (Jensen / monotonicity of `L^p`-norms on a
probability space and `∫ dν/dQ dQ = 1`). -/
theorem movspec_one_le_eLpNorm_rnDeriv {α : Type*} [MeasurableSpace α] (ν Q : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure Q] (hac : ν ≪ Q) {p : ℝ} (hp : 1 ≤ p) :
    1 ≤ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hm : AEStronglyMeasurable (ν.rnDeriv Q) Q := (Measure.measurable_rnDeriv ν Q).aestronglyMeasurable
  have h2 : eLpNorm (ν.rnDeriv Q) 1 Q ≤ eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q :=
    eLpNorm_le_eLpNorm_of_exponent_le h1
  refine le_trans (le_of_eq ?_) h2
  rw [eLpNorm_one_eq_lintegral_enorm]
  simp only [enorm_eq_self]
  rw [Measure.lintegral_rnDeriv hac]
  simp
  exact hm


/-- Variable-coefficient integral Gronwall: `a ≥ 0` integrable, `u ≤ u₀ + ∫_0^t G`, `G ≤ a u` on `[0,T]` give
`u(t) ≤ u₀ exp(∫_0^t a)` (absolutely continuous functions: `Φ e^{-A}` has a.e. nonpositive derivative). -/
theorem movspec_gronwall_var {T u0 : ℝ} {a G u : ℝ → ℝ}
    (ha0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ a r) (ha : IntegrableOn a (Set.Icc 0 T))
    (hG : IntegrableOn G (Set.Icc 0 T))
    (hu : ∀ t ∈ Set.Icc 0 T, u t ≤ u0 + ∫ r in Set.Icc 0 t, G r)
    (hGu : ∀ r ∈ Set.Icc 0 T, G r ≤ a r * u r) :
    ∀ t ∈ Set.Icc 0 T, u t ≤ u0 * Real.exp (∫ r in Set.Icc 0 t, a r) := by
  classical
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set G' : ℝ → ℝ := Set.indicator (Set.Icc 0 T) G with hG'
  set a' : ℝ → ℝ := Set.indicator (Set.Icc 0 T) a with ha'
  have hG'i : Integrable G' := (integrable_indicator_iff measurableSet_Icc).2 hG
  have ha'i : Integrable a' := (integrable_indicator_iff measurableSet_Icc).2 ha
  have hGii : ∀ x y : ℝ, IntervalIntegrable G' volume x y := fun x y => hG'i.intervalIntegrable
  have haii : ∀ x y : ℝ, IntervalIntegrable a' volume x y := fun x y => ha'i.intervalIntegrable
  set Φ : ℝ → ℝ := fun t => u0 + ∫ s in (0 : ℝ)..t, G' s with hΦ
  set A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a' s with hA
  have hset : ∀ (f : ℝ → ℝ) t, t ∈ Set.Icc 0 T → ∫ s in (0 : ℝ)..t, Set.indicator (Set.Icc 0 T) f s
      = ∫ r in Set.Icc 0 t, f r := by
    intro f t ht
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    rw [Set.indicator_of_mem (Set.Icc_subset_Icc le_rfl ht.2 hx)]
  have hΦeq : ∀ t ∈ Set.Icc 0 T, Φ t = u0 + ∫ r in Set.Icc 0 t, G r := fun t ht => by
    simp only [hΦ, hG']; rw [hset G t ht]
  have hAeq : ∀ t ∈ Set.Icc 0 T, A t = ∫ r in Set.Icc 0 t, a r := fun t ht => by
    simp only [hA, ha']; rw [hset a t ht]
  have hA0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ A t := by
    intro t ht
    rw [hAeq t ht]
    exact setIntegral_nonneg measurableSet_Icc fun r hr => ha0 r ⟨hr.1, hr.2.trans ht.2⟩
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => u0) 0 T :=
    (contDiff_const (c := u0) (n := 1)).contDiffOn.absolutelyContinuousOnInterval
  have hΦac : AbsolutelyContinuousOnInterval Φ 0 T :=
    hconst.add ((hGii 0 T).absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hAac : AbsolutelyContinuousOnInterval A 0 T :=
    (haii 0 T).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hexpL : LipschitzOnWith 1 Real.exp (Set.Iic 0) := by
    refine (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => Real.differentiableAt_exp) ?_
    intro x hx
    rw [Real.deriv_exp]
    have : Real.exp x ≤ 1 := Real.exp_le_one_iff.2 hx
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using this
  have hEac : AbsolutelyContinuousOnInterval (fun t => Real.exp (-A t)) 0 T := by
    have := hexpL.comp_absolutelyContinuousOnInterval (g := fun t => -A t) (a := 0) (b := T)
      (t := Set.Iic 0) (fun x hx => by
        rw [Set.uIcc_of_le hT] at hx
        simp only [Set.mem_Iic, Left.neg_nonpos_iff]; exact hA0 x hx) hAac.neg
    exact this
  set W : ℝ → ℝ := fun x => Φ x * Real.exp (-A x) with hW
  have hWac : AbsolutelyContinuousOnInterval W 0 t :=
    (hΦac.mono (by rw [Set.uIcc_of_le hT, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2)).mul
      (hEac.mono (by rw [Set.uIcc_of_le hT, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2))
  have hint := hWac.integral_deriv_eq_sub
  have hnp : ∫ x in (0 : ℝ)..t, deriv W x ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    refine integral_nonpos_of_ae ?_
    have h1 := LocallyIntegrable.ae_hasDerivAt_integral hG'i.locallyIntegrable
    have h2 := LocallyIntegrable.ae_hasDerivAt_integral ha'i.locallyIntegrable
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1, h2] with x hx1 hx2 hxm
    have hxT : x ∈ Set.Icc 0 T := ⟨hxm.1.le, hxm.2.trans ht.2⟩
    have d1 : HasDerivAt Φ (G' x) x := (hx1 0).const_add u0
    have d2 : HasDerivAt A (a' x) x := hx2 0
    have d3 : HasDerivAt (fun t => Real.exp (-A t)) (Real.exp (-A x) * -(a' x)) x := d2.neg.exp
    have d4 := d1.mul d3
    rw [show deriv W x = _ from d4.deriv]
    have hGx : G' x ≤ a' x * Φ x := by
      simp only [hG', ha']
      rw [Set.indicator_of_mem hxT, Set.indicator_of_mem hxT]
      have := hGu x hxT
      have hux : u x ≤ Φ x := by rw [hΦeq x hxT]; exact hu x hxT
      nlinarith [ha0 x hxT]
    have hE := Real.exp_pos (-A x)
    have := mul_nonneg hE.le (sub_nonneg.2 hGx)
    show G' x * Real.exp (-A x) + Φ x * (Real.exp (-A x) * -a' x) ≤ 0
    nlinarith [this]
  have hW0 : W 0 = u0 := by simp [hW, hΦ, hA]
  have hWt : W t ≤ u0 := by rw [hW0.symm]; linarith [hint]
  have h1 := hu t ht
  rw [← hΦeq t ht] at h1
  have hAt := hAeq t ht
  have hEt := Real.exp_pos (-A t)
  have : Φ t * Real.exp (-A t) ≤ u0 := hWt
  have hmul : Φ t ≤ u0 * Real.exp (A t) := by
    have := mul_le_mul_of_nonneg_right this (Real.exp_pos (A t)).le
    have e : Real.exp (-A t) * Real.exp (A t) = 1 := by rw [← Real.exp_add]; simp
    calc Φ t = Φ t * (Real.exp (-A t) * Real.exp (A t)) := by rw [e, mul_one]
      _ = Φ t * Real.exp (-A t) * Real.exp (A t) := by ring
      _ ≤ _ := this
  rw [hAt] at hmul
  exact h1.trans hmul

end HRS

end
