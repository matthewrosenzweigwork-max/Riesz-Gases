import HRS.Main.GFB4Aux12
import HRS.Uniform.Q45Max
import HRS.Uniform.Q45Ten1

/-!
# GFB4, part 13: `gf_wasserstein_comparison` with the measurability of `M`, `G`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c

section Aux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem gfb4_aemeasurable_windowPath (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T) (Y : ℝ → Ω → E)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (windowPath 0 T Y) P := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    exact aemeasurable_windowPath_zero P Y (hY 0 ⟨le_rfl, le_rfl⟩)
  · exact aemeasurable_windowPath P hpos Y hY hc

theorem gfb4_windowPath_sub {T : ℝ} (X Y : ℝ → Ω → E) {ω : Ω}
    (hX : ContinuousOn (fun t => X t ω) (Set.Icc 0 T)) (hY : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    windowPath 0 T (fun t ω => X t ω - Y t ω) ω = windowPath 0 T X ω - windowPath 0 T Y ω := by
  have hXY : ContinuousOn (fun t => X t ω - Y t ω) (Set.Icc 0 T) := hX.sub hY
  refine pcm_ext fun t => ?_
  rw [pcm_sub, pcm_windowPath (fun t ω => X t ω - Y t ω) hXY, pcm_windowPath X hX, pcm_windowPath Y hY]

theorem gfb4_windowPath_eq_of_continuous (T : ℝ) (R : ℝ → Ω → E) (ω : Ω)
    (hc : Continuous fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω) :
    windowPath 0 T R ω = (⟨fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
  unfold windowPath
  exact (dite_continuousMap_congr _ _ (funext fun t => by simp)).trans (dif_pos hc)

theorem gfb4_windowPath_eq_zero (T : ℝ) (R : ℝ → Ω → E) (ω : Ω)
    (hc : ¬ Continuous fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω) :
    windowPath 0 T R ω = (0 : C(Set.Icc (0 : ℝ) T, E)) := by
  unfold windowPath
  exact (dite_continuousMap_congr _ _ (funext fun t => by simp)).trans (dif_neg hc)

/-- The sup-norm of a window path is bounded by a bound on the sections. -/
theorem gfb4_windowPath_enorm_le (T : ℝ) (R : ℝ → Ω → E) (ω : Ω) (B : ℝ≥0∞)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖R t ω‖ₑ ≤ B) : ‖windowPath 0 T R ω‖ₑ ≤ B := by
  by_cases hB : B = ⊤
  · rw [hB]; exact le_top
  have hb : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω
  · have key : ‖(⟨fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E))‖ₑ ≤ B := by
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal hB]
      refine ENNReal.ofReal_le_ofReal ((ContinuousMap.norm_le _ hb).2 fun t => ?_)
      have := h t.1 t.2
      rw [← ofReal_norm, ← ENNReal.ofReal_toReal hB, ENNReal.ofReal_le_ofReal_iff hb] at this
      exact this
    calc ‖windowPath 0 T R ω‖ₑ
        = ‖(⟨fun t : Set.Icc (0 : ℝ) T => R (t : ℝ) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, E))‖ₑ := by
          rw [gfb4_windowPath_eq_of_continuous T R ω hc]; rfl
      _ ≤ B := key
  · calc ‖windowPath 0 T R ω‖ₑ = ‖(0 : C(Set.Icc (0 : ℝ) T, E))‖ₑ := by
          rw [gfb4_windowPath_eq_zero T R ω hc]; rfl
      _ ≤ B := by
          have : ‖(0 : C(Set.Icc (0 : ℝ) T, E))‖ₑ = 0 := by
            rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
          rw [this]; exact bot_le

theorem gfb4_enorm_section_le {T : ℝ} (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖Y t ω‖ₑ ≤ ‖windowPath 0 T Y ω‖ₑ := by
  have h := norm_pcm_apply_le (windowPath 0 T Y ω) ⟨t, ht⟩
  rw [pcm_windowPath Y hω ⟨t, ht⟩] at h
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h

end Aux

theorem gfb4_wasserstein_comparison_meas (T K : ℝ) (hT : 0 ≤ T) (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K)
        (X₀ X₀' : Ω → H) (_ : Measurable X₀) (_ : Measurable X₀') (M G : ℝ → Ω → H)
        (_ : ∀ t, Measurable (M t)) (_ : ∀ t, Measurable (G t))
        (Sd : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ)
        (_ : IsHilbertMartingaleWithCovariation P ℱ T (fun τ ω => M (min τ T) ω - G (min τ T) ω)
          (fun r ω => if r ≤ T then Sd r ω else 0))
        (_ : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ T → traceNormForm (Sd r ω) ≤ cost r ω)
        (Z Zb R : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
        (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
        (X Xb : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω),
        wassersteinE p (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) ≤
          ENNReal.ofReal C * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
            (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^ (1 / 2 : ℝ) := by
  obtain ⟨Cm, hCm0, hmax⟩ := maximal_estimate_meas T K hT
  refine ⟨max (detConst T K) (Real.sqrt Cm), le_max_of_le_left (detConst_pos T K).le, ?_⟩
  intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS X₀ X₀' hX₀ hX₀' M G hMm hGm Sd cost hMG hcost Z Zb R hZ hZb
    hZc hZbc hRc hZm hZbm hRm X Xb hXd hXbd
  have hev := hS.1
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  set C : ℝ := max (detConst T K) (Real.sqrt Cm) with hC
  have hCD : detConst T K ≤ C := le_max_left _ _
  have hCs : Real.sqrt Cm ≤ C := le_max_right _ _
  set M' : ℝ → Ω → H := fun τ ω => M (min τ T) ω - G (min τ T) ω with hM'
  have hM'm : ∀ t, Measurable (M' t) := fun t => (hMm _).sub (hGm _)
  set Zd : ℝ → Ω → E := fun t ω => Z t ω - Zb t ω with hZd
  have hZdm : ∀ t, Measurable (Zd t) := fun t => (hZm t).sub (hZbm t)
  have hZdS : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M' 0 t (Zd t) := fun t ht =>
    gfb4_isStochConv_sub P S.VE S.j hMm hGm ht.1 ht.2 (hZm t) (hZbm t) (hZ t ht) (hZb t ht)
  obtain ⟨Z', hZ'S, hZ'c, hZ'm, hZ'bd⟩ := hmax Ω P ℱ H E S hS M'
    (fun r ω => if r ≤ T then Sd r ω else 0) hMG
  have huniq : ∀ t ∈ Set.Icc (0 : ℝ) T, Zd t =ᵐ[P] Z' t := fun t ht =>
    gfb4_isStochConv_unique P S.VE S.j hM'm hT ht.1 ht.2 (hZdm t).aemeasurable (hZ'm t ht)
      (hZdS t ht) (hZ'S t ht)
  have hZdc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zd t ω) (Set.Icc 0 T) := by
    filter_upwards [hZc, hZbc] with ω h1 h2
    exact h1.sub h2
  have hall := gfb4_ae_forall_Icc P hT Zd Z' hZdc hZ'c huniq
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zd t ω‖ₑ) ^ 2 ∂P ≤
      ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P := by
    calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zd t ω‖ₑ) ^ 2 ∂P
        ≤ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ) ^ 2 ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hall] with ω hω
          have : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zd t ω‖ₑ) = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ :=
            iSup_congr fun t => iSup_congr fun ht => by rw [hω t ht]
          rw [this]
      _ ≤ ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal
            (traceNormForm ((fun r ω => if r ≤ T then Sd r ω else 0) r ω))) ∂P := hZ'bd
      _ ≤ ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P := by
          refine mul_le_mul' (le_refl _) ?_
          refine lintegral_mono_ae ?_
          filter_upwards [hcost] with ω hω
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          simp only [if_pos hr.2]
          exact ENNReal.ofReal_le_ofReal (hω r hr.1 hr.2)
  have hXm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (X t) := fun t ht => by
    have : X t = fun ω => S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω := funext (hXd t ht)
    rw [this]
    exact ((((S.VE t 0).continuous.comp S.j.continuous).measurable.comp hX₀).add (hZm t)).add (hRm t)
  have hXbm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Xb t) := fun t ht => by
    have : Xb t = fun ω => S.VE t 0 (S.j (X₀' ω)) + Zb t ω := funext (hXbd t ht)
    rw [this]
    exact (((S.VE t 0).continuous.comp S.j.continuous).measurable.comp hX₀').add (hZbm t)
  have hVc : ∀ x : H, ContinuousOn (fun t : ℝ => S.VE t 0 (S.j x)) (Set.Icc 0 T) := fun x =>
    continuousOn_VE_zero S hev x
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc 0 T) := by
    filter_upwards [hZc, hRc] with ω h1 h2
    exact (((hVc (X₀ ω)).add h1).add h2).congr fun t ht => hXd t ht ω
  have hXbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Xb t ω) (Set.Icc 0 T) := by
    filter_upwards [hZbc] with ω h1
    exact ((hVc (X₀' ω)).add h1).congr fun t ht => hXbd t ht ω
  have hwX := gfb4_aemeasurable_windowPath P hT X hXm hXc
  have hwXb := gfb4_aemeasurable_windowPath P hT Xb hXbm hXbc
  have hwR := gfb4_aemeasurable_windowPath P hT R (fun t _ => hRm t) hRc
  have hwZd := gfb4_aemeasurable_windowPath P hT Zd (fun t _ => hZdm t) hZdc
  have hpair : AEMeasurable (fun ω => (windowPath 0 T X ω, windowPath 0 T Xb ω)) P := hwX.prodMk hwXb
  have hcoup : IsCoupling (P.map fun ω => (windowPath 0 T X ω, windowPath 0 T Xb ω))
      (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb)) := by
    constructor
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hpair]
      rfl
    · rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hpair]
      rfl
  refine (wassersteinE_le_cost hcoup).trans ?_
  have : SecondCountableTopology (PathSp T E) :=
    inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, E))
  have hint : Measurable fun z : PathSp T E × PathSp T E => ENNReal.ofReal (‖z.1 - z.2‖ ^ p) :=
    (((continuous_fst.sub continuous_snd).norm.measurable).pow_const p).ennreal_ofReal
  rw [lintegral_map' hint.aemeasurable hpair]
  set a : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal C * ‖X₀ ω - X₀' ω‖ₑ with ha
  set c : Ω → ℝ≥0∞ := fun ω => ‖windowPath 0 T Zd ω‖ₑ with hcdef
  set b : Ω → ℝ≥0∞ := fun ω => ‖windowPath 0 T R ω‖ₑ with hb
  have ha_m : AEMeasurable a P := ((hX₀.sub hX₀').enorm.const_mul _).aemeasurable
  have hc_m : AEMeasurable c P := hwZd.enorm
  have hb_m : AEMeasurable b P := hwR.enorm
  have hpt0 : ∀ᵐ ω ∂P, ‖windowPath 0 T X ω - windowPath 0 T Xb ω‖ₑ ≤ a ω + c ω + b ω := by
    filter_upwards [hXc, hXbc, hRc, hZdc] with ω hX' hXb' hR' hZd'
    rw [← gfb4_windowPath_sub X Xb hX' hXb']
    refine gfb4_windowPath_enorm_le T (fun t ω => X t ω - Xb t ω) ω _ fun t ht => ?_
    have e : X t ω - Xb t ω = S.VE t 0 (S.j (X₀ ω - X₀' ω)) + Zd t ω + R t ω := by
      rw [hXd t ht, hXbd t ht]
      simp only [map_sub, hZd]
      abel
    have hV : ‖S.VE t 0 (S.j (X₀ ω - X₀' ω))‖ₑ ≤ a ω := by
      have h1 := hS.norm_le hT le_rfl ht.1 ht.2 (X₀ ω - X₀' ω)
      have h2 : ‖S.VE t 0 (S.j (X₀ ω - X₀' ω))‖ ≤ C * ‖X₀ ω - X₀' ω‖ :=
        h1.trans (mul_le_mul_of_nonneg_right hCD (norm_nonneg _))
      have e1 : ‖X₀ ω - X₀' ω‖ₑ = ENNReal.ofReal ‖X₀ ω - X₀' ω‖ := by rw [ofReal_norm]
      have e2 : ‖S.VE t 0 (S.j (X₀ ω - X₀' ω))‖ₑ =
          ENNReal.ofReal ‖S.VE t 0 (S.j (X₀ ω - X₀' ω))‖ := by rw [ofReal_norm]
      rw [e2, ha]
      simp only []
      rw [e1, ← ENNReal.ofReal_mul ((detConst_pos T K).le.trans hCD)]
      exact ENNReal.ofReal_le_ofReal h2
    show ‖X t ω - Xb t ω‖ₑ ≤ a ω + c ω + b ω
    rw [e]
    calc ‖S.VE t 0 (S.j (X₀ ω - X₀' ω)) + Zd t ω + R t ω‖ₑ
        ≤ ‖S.VE t 0 (S.j (X₀ ω - X₀' ω)) + Zd t ω‖ₑ + ‖R t ω‖ₑ := enorm_add_le _ _
      _ ≤ (‖S.VE t 0 (S.j (X₀ ω - X₀' ω))‖ₑ + ‖Zd t ω‖ₑ) + ‖R t ω‖ₑ := by
          gcongr; exact enorm_add_le _ _
      _ ≤ a ω + c ω + b ω := by
          gcongr
          · exact gfb4_enorm_section_le Zd hZd' ht
          · exact gfb4_enorm_section_le R hR' ht
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (‖windowPath 0 T X ω - windowPath 0 T Xb ω‖ ^ p) ≤
      (a ω + c ω + b ω) ^ p := by
    filter_upwards [hpt0] with ω hω
    rw [ofReal_norm_rpow hp0.le, ofReal_norm]
    exact ENNReal.rpow_le_rpow hω hp0.le
  have hMink : (∫⁻ ω, (a ω + c ω + b ω) ^ p ∂P) ^ (1 / p) ≤
      (∫⁻ ω, a ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, b ω ^ p ∂P) ^ (1 / p) := by
    have h1 := ENNReal.lintegral_Lp_add_le (μ := P) (f := fun ω => a ω + c ω) (g := b)
      (ha_m.add hc_m) hb_m hp1
    have h2 := ENNReal.lintegral_Lp_add_le (μ := P) (f := a) (g := c) ha_m hc_m hp1
    calc (∫⁻ ω, (a ω + c ω + b ω) ^ p ∂P) ^ (1 / p)
        ≤ (∫⁻ ω, (a ω + c ω) ^ p ∂P) ^ (1 / p) + (∫⁻ ω, b ω ^ p ∂P) ^ (1 / p) := h1
      _ ≤ ((∫⁻ ω, a ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p)) +
            (∫⁻ ω, b ω ^ p ∂P) ^ (1 / p) := add_le_add h2 le_rfl
  have hapart : (∫⁻ ω, a ω ^ p ∂P) ^ (1 / p) =
      ENNReal.ofReal C * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) :=
    gfb4_lp_const_mul P hp0 (ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun ω => ‖X₀ ω - X₀' ω‖ₑ)
  have hcpart : (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p) ≤ ENNReal.ofReal C *
      (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^ (1 / 2 : ℝ) := by
    refine (gfb4_lp_le_two P hc_m hp).trans ?_
    have h3 : ∫⁻ ω, c ω ^ (2 : ℝ) ∂P ≤
        ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P := by
      refine le_trans (lintegral_mono_ae ?_) hsup
      filter_upwards [hZdc] with ω hω
      rw [ENNReal.rpow_two]
      gcongr
      exact enorm_windowPath_le Zd hω
    calc (∫⁻ ω, c ω ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^
            (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow h3 (by norm_num)
      _ = ENNReal.ofReal Cm ^ (1 / (2 : ℝ)) *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^ (1 / (2 : ℝ)) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^ (1 / (2 : ℝ)) := by
          gcongr
          rw [ENNReal.ofReal_rpow_of_nonneg hCm0 (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.sqrt_eq_rpow]
          exact hCs
  calc (∫⁻ ω, ENNReal.ofReal (‖windowPath 0 T X ω - windowPath 0 T Xb ω‖ ^ p) ∂P) ^ (1 / p)
      ≤ (∫⁻ ω, (a ω + c ω + b ω) ^ p ∂P) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (by positivity)
    _ ≤ (∫⁻ ω, a ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, b ω ^ p ∂P) ^ (1 / p) :=
        hMink
    _ ≤ ENNReal.ofReal C * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ∂P) ^ (1 / 2 : ℝ) := by
        rw [hapart, add_right_comm]
        gcongr

end HRS.GF
