import HRS.Sections.AdjKGlueAux1
import HRS.PDE.MovFinalConsumers

/-!
# ADJK-GLUE, part 2: `moving_integrated_forcing` (Lemma 5.8, third assertion)

Joint continuity of `(r, z) ↦ V^{t,r} z`, a.s. Bochner integrability of `r ↦ V^{t,r} R_r`, the coordinate
identity for `∫_0^t V^{t,r} R_r dr`, and the assembly with `moving_pair_moments_proof'` and C3.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_joint_continuous {m CV t : ℝ} (ht : 0 ≤ t)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hplain : IsPlainEvolution Vev t)
    (hbd : ∀ u : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV) :
    Continuous (fun p : ℝ × NegSobolev d m => Vev t (clampTI t p.1) p.2) := by
  have hcl : Continuous (clampTI t) := by unfold clampTI; fun_prop
  have hc : ∀ z : NegSobolev d m, Continuous (fun r : ℝ => Vev t (clampTI t r) z) := by
    intro z
    have h := hplain.2.2 z
    exact h.comp_continuous (continuous_const.prodMk hcl)
      (fun r => ⟨(clampTI_mem ht r).1, (clampTI_mem ht r).2, le_rfl⟩)
  rw [continuous_iff_continuousAt]
  intro p0
  have h1 : Tendsto (fun p : ℝ × NegSobolev d m => Vev t (clampTI t p.1) p0.2) (𝓝 p0)
      (𝓝 (Vev t (clampTI t p0.1) p0.2)) :=
    ((hc p0.2).comp continuous_fst).continuousAt
  have h2 : Tendsto (fun p : ℝ × NegSobolev d m => Vev t (clampTI t p.1) (p.2 - p0.2)) (𝓝 p0) (𝓝 0) := by
    have hlim : Tendsto (fun p : ℝ × NegSobolev d m => CV * ‖p.2 - p0.2‖) (𝓝 p0) (𝓝 0) := by
      have hcc : Continuous (fun p : ℝ × NegSobolev d m => CV * ‖p.2 - p0.2‖) :=
        continuous_const.mul ((continuous_snd.sub continuous_const).norm)
      have := hcc.tendsto p0
      rwa [show CV * ‖p0.2 - p0.2‖ = 0 by simp] at this
    refine squeeze_zero_norm (fun p => ?_) hlim
    calc ‖Vev t (clampTI t p.1) (p.2 - p0.2)‖ ≤ ‖Vev t (clampTI t p.1)‖ * ‖p.2 - p0.2‖ :=
          (Vev t _).le_opNorm _
      _ ≤ CV * ‖p.2 - p0.2‖ := mul_le_mul_of_nonneg_right
          (hbd _ (clampTI_mem ht _).1 (clampTI_mem ht _).2) (norm_nonneg _)
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr (fun p => ?_)
  rw [← map_add]
  congr 1
  abel

theorem adjkg_enorm_le_one_add (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  by_cases hx : x ≤ 1
  · exact le_add_right hx
  · push_neg at hx
    refine le_add_left ?_
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 2 := pow_le_pow_right₀ hx.le (by norm_num)

/-- A.s. Bochner integrability of `r ↦ V^{t,r} R_r` on `(0,t]`, for all `t ≥ 0`. -/
theorem adjkg_conv_integrable {m CV : ℝ} (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T)
    (hbd : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ → Ω → NegSobolev d m) (hR : Measurable (Function.uncurry R)) {b : ℝ}
    (hRb : ∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → IntegrableOn (fun r => Vev t r (R r ω)) (Set.Ioc 0 t) := by
  have hCV0 : 0 ≤ CV := le_trans (norm_nonneg _) (hbd 0 0 le_rfl le_rfl)
  have hjoint : Measurable (fun p : Ω × ℝ => ‖R p.2 p.1‖ₑ ^ 2) :=
    (measurable_enorm.comp (hR.comp measurable_swap)).pow_const 2
  have hfin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∫⁻ r in Set.Ioc (0 : ℝ) n, ‖R r ω‖ₑ ^ 2 < ⊤ := by
    intro n
    set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) n) with hν
    have hmeas : Measurable (fun ω => ∫⁻ r, ‖R r ω‖ₑ ^ 2 ∂ν) := hjoint.lintegral_prod_right'
    have hle : ∫⁻ ω, ∫⁻ r, ‖R r ω‖ₑ ^ 2 ∂ν ∂P ≤ ENNReal.ofReal (b ^ 2) * ENNReal.ofReal n := by
      rw [lintegral_lintegral_swap (hjoint.aemeasurable (μ := P.prod ν))]
      calc ∫⁻ r, ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P ∂ν ≤ ∫⁻ r, ENNReal.ofReal (b ^ 2) ∂ν :=
            setLIntegral_mono' measurableSet_Ioc (fun r hr => hRb r hr.1.le)
        _ = ENNReal.ofReal (b ^ 2) * ENNReal.ofReal n := by
            rw [lintegral_const, hν, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ae_lt_top hmeas (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hle)
  filter_upwards [ae_all_iff.2 hfin] with ω hω t ht
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc 0 n := Set.Ioc_subset_Ioc_right hn
  have h2 : ∫⁻ r in Set.Ioc (0 : ℝ) t, ‖R r ω‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hsub) (hω n)
  have hRm : Measurable (fun r => R r ω) := hR.comp (measurable_id.prodMk measurable_const)
  have hG := adjkg_joint_continuous ht Vev (hplain t ht) (fun u hu hut => hbd u t hu hut)
  have hmeasI : Measurable (fun r => Vev t (clampTI t r) (R r ω)) :=
    hG.measurable.comp (measurable_id.prodMk hRm)
  have hae : AEStronglyMeasurable (fun r => Vev t r (R r ω)) (volume.restrict (Set.Ioc 0 t)) := by
    refine hmeasI.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    show Vev t (clampTI t r) (R r ω) = Vev t r (R r ω)
    rw [clampTI_of_mem ⟨hr.1.le, hr.2⟩]
  refine ⟨hae, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ r in Set.Ioc (0 : ℝ) t, ‖Vev t r (R r ω)‖ₑ
      ≤ ∫⁻ r in Set.Ioc (0 : ℝ) t, ENNReal.ofReal CV * (1 + ‖R r ω‖ₑ ^ 2) := by
        refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
        have h1 : ‖Vev t r (R r ω)‖ ≤ CV * ‖R r ω‖ :=
          ((Vev t r).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbd r t hr.1.le hr.2)
            (norm_nonneg _))
        calc ‖Vev t r (R r ω)‖ₑ = ENNReal.ofReal ‖Vev t r (R r ω)‖ := (ofReal_norm_eq_enorm _).symm
          _ ≤ ENNReal.ofReal (CV * ‖R r ω‖) := ENNReal.ofReal_le_ofReal h1
          _ = ENNReal.ofReal CV * ‖R r ω‖ₑ := by
              rw [ENNReal.ofReal_mul hCV0, ofReal_norm_eq_enorm]
          _ ≤ ENNReal.ofReal CV * (1 + ‖R r ω‖ₑ ^ 2) :=
              mul_le_mul' le_rfl (adjkg_enorm_le_one_add _)
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left measurable_const]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.2 ⟨?_, h2⟩)
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
        simp

/-- The coordinates of `∫_0^t V^{t,r} R_r dr` are the integrated forcing coordinates. -/
theorem adjkg_coord_integral {Ω : Type u} {N : ℕ} (hd : 2 ≤ d)
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {Vev₂ : ℝ → ℝ → NegSobolev d ((d : ℝ) + 3) →L[ℝ] NegSobolev d ((d : ℝ) + 3)}
    (hdual₂ : IsDualEvolution htr.dyn ρ ((d : ℝ) + 3) Vev₂) {CV₂ : ℝ}
    (hCV₂ : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev₂ t u‖ ≤ CV₂)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) {t : ℝ} (ht : 0 ≤ t)
    (hint : IntegrableOn (fun r => Vev t r (adjkgR m s ρ X r ω)) (Set.Ioc 0 t))
    (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (∫ r in (0 : ℝ)..t, Vev t r (adjkgR m s ρ X r ω)) k =
      evolvingForcingCoord htr.dyn ρ X k t ω := by
  have hint' : IntervalIntegrable (fun r => Vev t r (adjkgR m s ρ X r ω)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hint
  have h1 : NegSobolev.fourierCoeff (∫ r in (0 : ℝ)..t, Vev t r (adjkgR m s ρ X r ω)) k =
      ∫ r in (0 : ℝ)..t, NegSobolev.fourierCoeff (Vev t r (adjkgR m s ρ X r ω)) k :=
    (ContinuousLinearMap.intervalIntegral_comp_comm (adjkdCoord m k) hint').symm
  rw [h1]
  unfold evolvingForcingCoord
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le ht] at hr
  exact adjkg_coord_eq hd htr hm hdual hdual₂ hCV₂ X ω hr.1 hr.2 k

end HRS.AdjK
