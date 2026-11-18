import HRS.MH.WpSpec2
import HRS.MH.WpP1
import HRS.Main.GFB4Aux13

/-!
# P2: `HRS.MH.Wp.gfwp_wasserstein_comparison`

The proof of `HRS.GF.gfb4_wasserstein_comparison_meas` (GFB4Aux13.lean:86) for every `p ≥ 2`: the maximal estimate is
`HRS.MH.WpP.maximal_estimate_meas_p_proof` (P1, WpP1.lean) and the cost term is `(∫⁻ (∫⁻ cost)^{p/2})^{1/p}`.
The helper lemmas `gfb4_*` (GFB4Aux11-13) are reused from `HRS.GF`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.WpP

open HRS HRS.GF HRS.Uniform HRS.Uniform.Q45 HRS.Uniform.Q54c

theorem gfwp_wasserstein_comparison_proof :
    type_of% @HRS.MH.Wp.gfwp_wasserstein_comparison := by
  intro T K p hT hp
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨Cm, hCm0, hmax⟩ := maximal_estimate_meas_p_proof T K p hT hp
  refine ⟨max (detConst T K) (max 1 Cm), le_max_of_le_left (detConst_pos T K).le, ?_⟩
  intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS X₀ X₀' hX₀ hX₀' M G hMm hGm Sd cost hMG hcost Z Zb R hZ hZb
    hZc hZbc hRc hZm hZbm hRm X Xb hXd hXbd
  have hev := hS.1
  set C : ℝ := max (detConst T K) (max 1 Cm) with hC
  have hCD : detConst T K ≤ C := le_max_left _ _
  have hCpow : Cm ^ (1 / p) ≤ C := by
    have hCm' : Cm ^ (1 / p) ≤ max 1 Cm := by
      rcases le_total Cm 1 with h | h
      · exact (Real.rpow_le_one hCm0 h (div_nonneg zero_le_one hp0.le)).trans (le_max_left _ _)
      · calc Cm ^ (1 / p) ≤ Cm ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h ((div_le_one hp0).2 (by linarith))
          _ = Cm := Real.rpow_one Cm
          _ ≤ max 1 Cm := le_max_right _ _
    exact hCm'.trans (le_max_right _ _)
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
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zd t ω‖ₑ) ^ p ∂P ≤
      ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P := by
    calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zd t ω‖ₑ) ^ p ∂P
        ≤ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ) ^ p ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hall] with ω hω
          have : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zd t ω‖ₑ) = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ :=
            iSup_congr fun t => iSup_congr fun ht => by rw [hω t ht]
          rw [this]
      _ ≤ ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal
            (traceNormForm ((fun r ω => if r ≤ T then Sd r ω else 0) r ω))) ^ (p / 2) ∂P := hZ'bd
      _ ≤ ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P := by
          refine mul_le_mul' (le_refl _) ?_
          refine lintegral_mono_ae ?_
          filter_upwards [hcost] with ω hω
          refine ENNReal.rpow_le_rpow ?_ (by linarith)
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          simp only [hr.2, ite_true]
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
      (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P) ^ (1 / p) := by
    have h3 : ∫⁻ ω, c ω ^ p ∂P ≤
        ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P := by
      refine le_trans (lintegral_mono_ae ?_) hsup
      filter_upwards [hZdc] with ω hω
      exact ENNReal.rpow_le_rpow (enorm_windowPath_le Zd hω) hp0.le
    calc (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p)
        ≤ (ENNReal.ofReal Cm * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P) ^
            (1 / p) := ENNReal.rpow_le_rpow h3 (div_nonneg zero_le_one hp0.le)
      _ = ENNReal.ofReal Cm ^ (1 / p) *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P) ^ (1 / p) :=
          ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hp0.le)
      _ ≤ ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P) ^ (1 / p) := by
          gcongr
          rw [ENNReal.ofReal_rpow_of_nonneg hCm0 (div_nonneg zero_le_one hp0.le)]
          exact ENNReal.ofReal_le_ofReal hCpow
  calc (∫⁻ ω, ENNReal.ofReal (‖windowPath 0 T X ω - windowPath 0 T Xb ω‖ ^ p) ∂P) ^ (1 / p)
      ≤ (∫⁻ ω, (a ω + c ω + b ω) ^ p ∂P) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (div_nonneg zero_le_one hp0.le)
    _ ≤ (∫⁻ ω, a ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, c ω ^ p ∂P) ^ (1 / p) + (∫⁻ ω, b ω ^ p ∂P) ^ (1 / p) :=
        hMink
    _ ≤ ENNReal.ofReal C * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (cost r ω)) ^ (p / 2) ∂P) ^ (1 / p) := by
        rw [hapart, add_right_comm]
        gcongr

end HRS.MH.WpP
