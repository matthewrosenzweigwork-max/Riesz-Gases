import HRS.Uniform.Comp28W9
import HRS.Main.GFB4Aux13

/-!
# COMP-28, Wasserstein part, W10: the single-space estimate

`wass_core`: on one probability space, if the stochastic convolution of the difference `Zd = Z - Zb` is a convolution against a
Hilbert martingale `Dd` with covariation `Sd ≤ cost`, then `W_p(windowPath a T X, windowPath a T Xb)` is bounded by the three
terms of Proposition 3.28 (history bound plus the window maximal estimate).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c HRS.GF HRS.Uniform.Q07c

universe u

section WinA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma windowPath_shift (a T : ℝ) (Y : ℝ → Ω → E) :
    windowPath a T Y = windowPath 0 T (fun t ω => Y (a + t) ω) := by
  funext ω
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y (a + (t : ℝ)) ω
  · have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => Y (a + (0 + (t : ℝ))) ω := by
      simpa only [zero_add] using hc
    have e1 : windowPath a T Y ω = (⟨fun t => Y (a + (t : ℝ)) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
      unfold windowPath; exact dif_pos hc
    have e2 : windowPath 0 T (fun t ω => Y (a + t) ω) ω =
        (⟨fun t => Y (a + (0 + (t : ℝ))) ω, hc'⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
      unfold windowPath; exact dif_pos hc'
    rw [e1, e2]
    exact ContinuousMap.ext fun t => by simp
  · have hc' : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => Y (a + (0 + (t : ℝ))) ω := by
      simpa only [zero_add] using hc
    have e1 : windowPath a T Y ω = 0 := by unfold windowPath; exact dif_neg hc
    have e2 : windowPath 0 T (fun t ω => Y (a + t) ω) ω = 0 := by unfold windowPath; exact dif_neg hc'
    rw [e1, e2]

lemma wp_enorm_le_a (a T : ℝ) (Y : ℝ → Ω → E) (ω : Ω) (B : ℝ≥0∞)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Y (a + t) ω‖ₑ ≤ B) : ‖windowPath a T Y ω‖ₑ ≤ B := by
  rw [windowPath_shift]
  exact gfb4_windowPath_enorm_le T (fun t ω => Y (a + t) ω) ω B h

lemma contOn_shift {a T : ℝ} (ha : 0 ≤ a) {Y : ℝ → Ω → E} {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    ContinuousOn (fun t => Y (a + t) ω) (Set.Icc 0 T) :=
  hω.comp (by fun_prop) (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)

lemma wp_section_le_a {a T : ℝ} (ha : 0 ≤ a) (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖Y (a + t) ω‖ₑ ≤ ‖windowPath a T Y ω‖ₑ := by
  rw [windowPath_shift]
  exact gfb4_enorm_section_le (fun t ω => Y (a + t) ω) (contOn_shift ha hω) ht

lemma wp_sub_a {a T : ℝ} (ha : 0 ≤ a) (X Y : ℝ → Ω → E) {ω : Ω}
    (hX : ContinuousOn (fun t => X t ω) (Set.Icc 0 (a + T)))
    (hY : ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    windowPath a T (fun t ω => X t ω - Y t ω) ω = windowPath a T X ω - windowPath a T Y ω := by
  rw [windowPath_shift a T (fun t ω => X t ω - Y t ω), windowPath_shift a T X, windowPath_shift a T Y]
  exact gfb4_windowPath_sub (fun t ω => X (a + t) ω) (fun t ω => Y (a + t) ω)
    (contOn_shift ha hX) (contOn_shift ha hY)

lemma aem_wp_a (P : Measure Ω) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (Y : ℝ → Ω → E)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 (a + T))) :
    AEMeasurable (windowPath a T Y) P := by
  rw [windowPath_shift]
  refine gfb4_aemeasurable_windowPath P hT _ (fun t ht => hY (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩) ?_
  filter_upwards [hc] with ω hω
  exact contOn_shift ha hω

end WinA

section Core

open HRS.Uniform.Q48d

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma enorm_clm_le {K : ℝ} (hK : 0 ≤ K) {A : H →L[ℝ] H} (h : ‖A‖ ≤ K) (z : H) :
    ‖A z‖ₑ ≤ ENNReal.ofReal K * ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal ((A.le_opNorm z).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))

/-- The single-space estimate. -/
theorem wass_core {K c T Cmax a : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (hT : 0 ≤ T) (ha : 0 ≤ a) {p : ℝ}
    (hp : p = 1 ∨ p = 2)
    (V : ℝ → ℝ → H →L[ℝ] H) (hV : IsPlainEvolution V (a + T))
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    (hmax : MaxWindows.{u, _} V T Cmax)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (x₀ x₀' : Ω → H) (hx₀ : Measurable x₀) (hx₀' : Measurable x₀')
    (Dd : ℝ → Ω → H) (Sd : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hDd : IsHilbertMartingaleWithCovariation P ℱ (a + T) Dd Sd)
    (cost : ℝ → Ω → ℝ)
    (hcost : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ a + T → traceNormForm (Sd r ω) ≤ cost r ω)
    (Z Zb R : ℝ → Ω → H)
    (hZd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv P V (ContinuousLinearMap.id ℝ H) Dd 0 t (fun ω => Z t ω - Zb t ω))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
    (hZm : ∀ t, Measurable (Z t)) (hZbm : ∀ t, Measurable (Zb t)) (hRm : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → H)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (x₀ ω) + Z t ω + R t ω)
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (x₀' ω) + Zb t ω) :
    wassersteinE p (law P (windowPath a T X)) (law P (windowPath a T Xb)) ≤
      ENNReal.ofReal ((2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) * Real.exp (-c * a)) *
          (∫⁻ ω, ‖x₀ ω - x₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
        (∫⁻ ω, ‖windowPath a T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
        ENNReal.ofReal (2 * (K ^ 2 + Real.sqrt Cmax) + K + 1) *
          (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 * cost r ω)) ∂P) ^ (1 / 2 : ℝ) := by
  classical
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hS0 : 0 ≤ a + T := by linarith
  have haS : a ≤ a + T := by linarith
  have hsq0 := Real.sqrt_nonneg Cmax
  set C : ℝ := 2 * (K ^ 2 + Real.sqrt Cmax) + K + 1 with hC
  have hCK : K ≤ C := by nlinarith [sq_nonneg K]
  have hC0 : 0 ≤ C := hK.trans hCK
  set Cm : ℝ := max Cmax 0 with hCm
  have hCmE : ENNReal.ofReal Cmax = ENNReal.ofReal Cm := by
    rcases le_total 0 Cmax with h | h
    · rw [hCm, max_eq_left h]
    · rw [hCm, max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have hsqCm : Real.sqrt Cmax ^ 2 = Cm := by
    rcases le_total 0 Cmax with h | h
    · rw [Real.sq_sqrt h, hCm, max_eq_left h]
    · rw [Real.sqrt_eq_zero_of_nonpos h, hCm, max_eq_right h]; norm_num
  set Zd : ℝ → Ω → H := fun t ω => Z t ω - Zb t ω with hZd_def
  have hZdm : ∀ t, Measurable (Zd t) := fun t => (hZm t).sub (hZbm t)
  have hZdc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zd t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZc, hZbc] with ω h1 h2
    exact h1.sub h2
  have hDm : ∀ τ, Measurable (Dd τ) := fun τ => measurable_of_isHM hDd τ
  -- the history
  have hhist := hist_bound hDd ha haS hK hc V (fun r hr0 hra => hVb r a hr0 hra haS)
    (hZdm a).aestronglyMeasurable (hZd a ⟨ha, haS⟩)
  -- the restarted convolution
  set Y : ℝ → Ω → H := fun t ω => Zd t ω - V t a (Zd a ω) with hY_def
  have hYm : ∀ t, Measurable (Y t) := fun t =>
    (hZdm t).sub ((V t a).continuous.measurable.comp (hZdm a))
  have hYS : ∀ t ∈ Set.Icc a (a + T),
      IsStochConv P V (ContinuousLinearMap.id ℝ H) Dd a t (Y t) := by
    intro t ht
    have ht0 : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans ht.1, ht.2⟩
    have hDt : ∀ τ ∈ Set.Icc 0 t, AEStronglyMeasurable (Dd τ) P := fun τ _ =>
      (hDm τ).aestronglyMeasurable
    have hDa : ∀ τ ∈ Set.Icc 0 a, AEStronglyMeasurable (Dd τ) P := fun τ _ =>
      (hDm τ).aestronglyMeasurable
    have hDt' : ∀ τ ∈ Set.Icc a t, AEStronglyMeasurable (Dd τ) P := fun τ _ =>
      (hDm τ).aestronglyMeasurable
    have h1 := (isStochConv_iff (hZdm t).aestronglyMeasurable hDt).1 (hZd t ht0)
    have h2 := (isStochConv_iff (hZdm a).aestronglyMeasurable hDa).1 (hZd a ⟨ha, haS⟩)
    have h3 := sc_split ha ht.1 hDt (fun r hr0 hra => hV.2.1 r a t hr0 hra ht.1 ht.2)
      (hZdm t).aestronglyMeasurable (hZdm a).aestronglyMeasurable h1 h2
    exact (isStochConv_iff (hYm t).aestronglyMeasurable hDt').2 h3
  have hYc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc a (a + T)) := by
    filter_upwards [hZdc] with ω hω
    refine (hω.mono (fun t ht => ⟨ha.trans ht.1, ht.2⟩)).sub ?_
    exact (hV.2.2 (Zd a ω)).comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ha, ht.1, ht.2⟩)
  have hwin := hmax Ω P ℱ a ha Dd Sd hDd Y (fun t _ => (hYm t).aemeasurable) hYS hYc
  -- the three integrals
  set I1 : ℝ≥0∞ := ∫⁻ ω, (∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sd r ω))) ∂P with hI1
  set I2 : ℝ≥0∞ := ∫⁻ ω, (∫⁻ σ in Set.Icc 0 a, ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sd σ ω))) ∂P
    with hI2
  set J : ℝ≥0∞ := ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal
    (Real.exp (-c * max (a - r) 0) ^ 2 * cost r ω)) ∂P with hJ
  have hI1J : I1 ≤ J := by
    refine lintegral_mono_ae ?_
    filter_upwards [hcost] with ω hω
    calc ∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sd r ω))
        ≤ ∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 * cost r ω) := by
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          have h1 : Real.exp (-c * max (a - r) 0) = 1 := by
            have : max (a - r) 0 = 0 := max_eq_right (by linarith [hr.1])
            rw [this]; simp
          rw [h1]
          simpa using ENNReal.ofReal_le_ofReal (hω r (ha.trans hr.1) hr.2)
      _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc ha le_rfl)
  have hI2J : I2 ≤ J := by
    refine lintegral_mono_ae ?_
    filter_upwards [hcost] with ω hω
    calc ∫⁻ σ in Set.Icc 0 a, ENNReal.ofReal (wt c a σ ^ 2 * traceNormForm (Sd σ ω))
        ≤ ∫⁻ r in Set.Icc 0 a, ENNReal.ofReal
            (Real.exp (-c * max (a - r) 0) ^ 2 * cost r ω) := by
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (hω r hr.1 (hr.2.trans haS)) (sq_nonneg _))
      _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Icc le_rfl haS)
  -- the history bound on `Zd a`
  have hh : ∫⁻ ω, ‖Zd a ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (K ^ 2) * J :=
    hhist.trans (mul_le_mul' le_rfl hI2J)
  -- the window sup bound
  have hs : ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Y t ω‖ₑ) ^ 2 ∂P ≤ ENNReal.ofReal Cm * J := by
    rw [← hCmE]
    exact hwin.trans (mul_le_mul' le_rfl hI1J)
  -- pointwise bound for the window of `Zd`
  have hpt : ∀ ω, ‖windowPath a T Zd ω‖ₑ ≤
      (⨆ t ∈ Set.Icc a (a + T), ‖Y t ω‖ₑ) + ENNReal.ofReal K * ‖Zd a ω‖ₑ := by
    intro ω
    refine wp_enorm_le_a a T Zd ω _ fun t ht => ?_
    have e : Zd (a + t) ω = Y (a + t) ω + V (a + t) a (Zd a ω) := by simp [hY_def]
    rw [e]
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc a (a + T)) => ‖Y t ω‖ₑ) (a + t)
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · refine enorm_clm_le hK ?_ _
      have h1 := hVb a (a + t) ha (by linarith [ht.1]) (by linarith [ht.2])
      have h2 : Real.exp (-c * (a + t - a)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [ht.1]
      calc ‖V (a + t) a‖ ≤ K * Real.exp (-c * (a + t - a)) := h1
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left h2 hK
        _ = K := mul_one K
  -- `L²` bound on the window of `Zd`
  have hwZd : AEMeasurable (windowPath a T Zd) P := aem_wp_a P ha hT Zd (fun t _ => hZdm t) hZdc
  have hc2 : ∫⁻ ω, ‖windowPath a T Zd ω‖ₑ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal (2 * (Cm + K ^ 4)) * J := by
    have hhm : Measurable fun ω => ENNReal.ofReal (K ^ 2) * ‖Zd a ω‖ₑ ^ 2 :=
      (((hZdm a).enorm).pow_const 2).const_mul _
    calc ∫⁻ ω, ‖windowPath a T Zd ω‖ₑ ^ (2 : ℝ) ∂P
        ≤ ∫⁻ ω, 2 * ((⨆ t ∈ Set.Icc a (a + T), ‖Y t ω‖ₑ) ^ 2 +
            ENNReal.ofReal (K ^ 2) * ‖Zd a ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [ENNReal.rpow_two]
          refine ((pow_le_pow_left' (hpt ω) 2)).trans ?_
          refine (gfb4_sq_add_le _ _).trans ?_
          gcongr
          rw [mul_pow, ENNReal.ofReal_pow hK]
      _ = 2 * (∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Y t ω‖ₑ) ^ 2 ∂P +
            ENNReal.ofReal (K ^ 2) * ∫⁻ ω, ‖Zd a ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ hhm,
            lintegral_const_mul _ (((hZdm a).enorm).pow_const 2)]
      _ ≤ 2 * (ENNReal.ofReal Cm * J + ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal (K ^ 2) * J)) := by
          gcongr
      _ = ENNReal.ofReal (2 * (Cm + K ^ 4)) * J := by
          have hCm0 : 0 ≤ Cm := le_max_right _ _
          rw [← mul_assoc (ENNReal.ofReal (K ^ 2)), ← ENNReal.ofReal_mul (by positivity),
            ← add_mul, ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_add hCm0 (by positivity),
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  -- measurability and continuity of `X`, `Xb`
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (X t) := fun t ht => by
    have : X t = fun ω => V t 0 (x₀ ω) + Z t ω + R t ω := funext (hXd t ht)
    rw [this]
    exact (((V t 0).continuous.measurable.comp hx₀).add (hZm t)).add (hRm t)
  have hXbm : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), Measurable (Xb t) := fun t ht => by
    have : Xb t = fun ω => V t 0 (x₀' ω) + Zb t ω := funext (hXbd t ht)
    rw [this]
    exact ((V t 0).continuous.measurable.comp hx₀').add (hZbm t)
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => V t 0 x) (Set.Icc 0 (a + T)) := fun x =>
    continuousOn_V_zero V hV.2.2 x
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (x₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hXbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Xb t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hZbc] with ω h1
    exact ((hVc (x₀' ω)).add h1).congr fun t ht => hXbd t ht ω
  have hwX := aem_wp_a P ha hT X hXm hXc
  have hwXb := aem_wp_a P ha hT Xb hXbm hXbc
  have hwR := aem_wp_a P ha hT R (fun t _ => hRm t) hRc
  have hpair : AEMeasurable (fun ω => (windowPath a T X ω, windowPath a T Xb ω)) P := hwX.prodMk hwXb
  have hcoup : IsCoupling (P.map fun ω => (windowPath a T X ω, windowPath a T Xb ω))
      (law P (windowPath a T X)) (law P (windowPath a T Xb)) := by
    constructor
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hpair]
      rfl
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hpair]
      rfl
  refine (wassersteinE_le_cost hcoup).trans ?_
  have : SecondCountableTopology (PathSp T H) :=
    inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, H))
  have hint : Measurable fun z : PathSp T H × PathSp T H => ENNReal.ofReal (‖z.1 - z.2‖ ^ p) :=
    (((continuous_fst.sub continuous_snd).norm.measurable).pow_const p).ennreal_ofReal
  rw [lintegral_map' hint.aemeasurable hpair]
  set A : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (C * Real.exp (-c * a)) * ‖x₀ ω - x₀' ω‖ₑ with hA
  set Cc : Ω → ℝ≥0∞ := fun ω => ‖windowPath a T Zd ω‖ₑ with hCc
  set B : Ω → ℝ≥0∞ := fun ω => ‖windowPath a T R ω‖ₑ with hB
  have hA_m : AEMeasurable A P := ((hx₀.sub hx₀').enorm.const_mul _).aemeasurable
  have hC_m : AEMeasurable Cc P := hwZd.enorm
  have hB_m : AEMeasurable B P := hwR.enorm
  have hpt0 : ∀ᵐ ω ∂P, ‖windowPath a T X ω - windowPath a T Xb ω‖ₑ ≤ A ω + Cc ω + B ω := by
    filter_upwards [hXc, hXbc, hRc, hZdc] with ω hX' hXb' hR' hZd'
    rw [← wp_sub_a ha X Xb hX' hXb']
    refine wp_enorm_le_a a T (fun t ω => X t ω - Xb t ω) ω _ fun t ht => ?_
    have ht' : a + t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have e : X (a + t) ω - Xb (a + t) ω =
        V (a + t) 0 (x₀ ω - x₀' ω) + Zd (a + t) ω + R (a + t) ω := by
      rw [hXd _ ht', hXbd _ ht']
      simp only [map_sub, hZd_def]
      abel
    have hV' : ‖V (a + t) 0 (x₀ ω - x₀' ω)‖ₑ ≤ A ω := by
      have h1 := hVb 0 (a + t) le_rfl (by linarith [ht.1]) ht'.2
      have h2 : ‖V (a + t) 0‖ ≤ C * Real.exp (-c * a) := by
        refine h1.trans ?_
        have : Real.exp (-c * (a + t - 0)) ≤ Real.exp (-c * a) := by
          rw [Real.exp_le_exp]; nlinarith [ht.1]
        calc K * Real.exp (-c * (a + t - 0)) ≤ K * Real.exp (-c * a) :=
              mul_le_mul_of_nonneg_left this hK
          _ ≤ C * Real.exp (-c * a) := mul_le_mul_of_nonneg_right hCK (Real.exp_pos _).le
      refine (enorm_clm_le (mul_nonneg hC0 (Real.exp_pos _).le) h2 _).trans ?_
      exact le_rfl
    show ‖X (a + t) ω - Xb (a + t) ω‖ₑ ≤ A ω + Cc ω + B ω
    rw [e]
    calc ‖V (a + t) 0 (x₀ ω - x₀' ω) + Zd (a + t) ω + R (a + t) ω‖ₑ
        ≤ ‖V (a + t) 0 (x₀ ω - x₀' ω) + Zd (a + t) ω‖ₑ + ‖R (a + t) ω‖ₑ := enorm_add_le _ _
      _ ≤ (‖V (a + t) 0 (x₀ ω - x₀' ω)‖ₑ + ‖Zd (a + t) ω‖ₑ) + ‖R (a + t) ω‖ₑ := by
          gcongr; exact enorm_add_le _ _
      _ ≤ A ω + Cc ω + B ω := by
          gcongr
          · exact wp_section_le_a ha Zd hZd' ht
          · exact wp_section_le_a ha R hR' ht
  have hptp : ∀ᵐ ω ∂P, ENNReal.ofReal (‖windowPath a T X ω - windowPath a T Xb ω‖ ^ p) ≤
      (A ω + Cc ω + B ω) ^ p := by
    filter_upwards [hpt0] with ω hω
    rw [ofReal_norm_rpow hp0.le, ofReal_norm]
    exact ENNReal.rpow_le_rpow hω hp0.le
  have hMink : (∫⁻ ω, (A ω + Cc ω + B ω) ^ p ∂P) ^ (1 / p) ≤
      (∫⁻ ω, A ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, Cc ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, B ω ^ p ∂P) ^ (1 / p) := by
    have h1 := ENNReal.lintegral_Lp_add_le (μ := P) (f := fun ω => A ω + Cc ω) (g := B)
      (hA_m.add hC_m) hB_m hp1
    have h2 := ENNReal.lintegral_Lp_add_le (μ := P) (f := A) (g := Cc) hA_m hC_m hp1
    calc (∫⁻ ω, (A ω + Cc ω + B ω) ^ p ∂P) ^ (1 / p)
        ≤ (∫⁻ ω, (A ω + Cc ω) ^ p ∂P) ^ (1 / p) + (∫⁻ ω, B ω ^ p ∂P) ^ (1 / p) := h1
      _ ≤ ((∫⁻ ω, A ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, Cc ω ^ p ∂P) ^ (1 / p)) +
            (∫⁻ ω, B ω ^ p ∂P) ^ (1 / p) := add_le_add h2 le_rfl
  have hApart : (∫⁻ ω, A ω ^ p ∂P) ^ (1 / p) =
      ENNReal.ofReal (C * Real.exp (-c * a)) * (∫⁻ ω, ‖x₀ ω - x₀' ω‖ₑ ^ p ∂P) ^ (1 / p) :=
    gfb4_lp_const_mul P hp0 (ENNReal.ofReal (C * Real.exp (-c * a))) ENNReal.ofReal_ne_top
      (fun ω => ‖x₀ ω - x₀' ω‖ₑ)
  have hCpart : (∫⁻ ω, Cc ω ^ p ∂P) ^ (1 / p) ≤ ENNReal.ofReal C * J ^ (1 / 2 : ℝ) := by
    refine (gfb4_lp_le_two P hC_m hp).trans ?_
    calc (∫⁻ ω, Cc ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal (2 * (Cm + K ^ 4)) * J) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hc2 (by norm_num)
      _ = ENNReal.ofReal (2 * (Cm + K ^ 4)) ^ (1 / (2 : ℝ)) * J ^ (1 / (2 : ℝ)) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ ENNReal.ofReal C * J ^ (1 / (2 : ℝ)) := by
          gcongr
          have hCm0 : 0 ≤ Cm := le_max_right _ _
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.sqrt_eq_rpow]
          refine Real.sqrt_le_iff.2 ⟨hC0, ?_⟩
          have hs2 := hsqCm
          have hkey : 2 * (Cm + K ^ 4) ≤ (2 * (K ^ 2 + Real.sqrt Cmax)) ^ 2 := by
            nlinarith [mul_nonneg (sq_nonneg K) hsq0, sq_nonneg K, sq_nonneg (K ^ 2)]
          refine hkey.trans ?_
          exact pow_le_pow_left₀ (by positivity) (by linarith [hK]) 2
  calc (∫⁻ ω, ENNReal.ofReal (‖windowPath a T X ω - windowPath a T Xb ω‖ ^ p) ∂P) ^ (1 / p)
      ≤ (∫⁻ ω, (A ω + Cc ω + B ω) ^ p ∂P) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hptp) (by positivity)
    _ ≤ (∫⁻ ω, A ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, Cc ω ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, B ω ^ p ∂P) ^ (1 / p) := hMink
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * a)) * (∫⁻ ω, ‖x₀ ω - x₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath a T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal C * J ^ (1 / 2 : ℝ) := by
        rw [hApart, add_right_comm]
        gcongr

end Core


end HRS.Uniform.Comp28
