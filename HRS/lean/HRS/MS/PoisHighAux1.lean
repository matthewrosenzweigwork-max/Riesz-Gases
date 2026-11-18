import Mathlib
import HRS.MS.PoisGradAux2
import HRS.MS.PoisLipAux3

/-!
# POIS-HIGHSM (part 1): continuity of `E a_r(φ_τ x)` and the Duhamel principle for `P_t`

Helper lemmas carry the prefix `hs_`.  This file contains the pathwise/Itô-free Duhamel principle used
to differentiate the semigroup:

* `hs_avg_tendsto`: the average `(s - s₀)⁻¹ ∫_{s₀}^s H(r, s) dr` tends to `H(s₀, s₀)`.
* `hs_cont_sg`: `(r, τ, x) ↦ E a_r(φ_τ x)` is continuous on `{τ ∈ [0,T]}` for a bounded jointly
  continuous `a`.
* `hs_duhamel`: if `v_s = v_0 + ∫ a` is a family of `C²` functions with `L v_s = a_s - F_s`
  (`a`, `F`, `v` bounded and jointly continuous), then
  `v_t = P_t v_0 + ∫_0^t P_{t-s} F_s ds`.  Proof: `ψ(s) = P_{t-s} v_s(x)` has derivative
  `P_{t-s} F_s (x)` (Kolmogorov equation for `v_{s₀}` and dominated convergence for the time variation
  of `v_s`).
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisGrad HRS.MS.PoisMax HRS.MS.PoisMoll
open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

noncomputable section

universe u

namespace HRS.MS.PoisHigh

variable {d : ℕ}

/-- The average `(s - s₀)⁻¹ ∫_{s₀}^s H(r, s) dr` tends to `H(s₀, s₀)` for a jointly continuous `H`. -/
theorem hs_avg_tendsto {H : ℝ → ℝ → ℝ} (hH : Continuous fun p : ℝ × ℝ => H p.1 p.2) (s0 : ℝ) :
    Tendsto (fun s => (s - s0)⁻¹ * ∫ r in s0..s, H r s) (𝓝[≠] s0) (𝓝 (H s0 s0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hc := Metric.continuousAt_iff.1 (hH.continuousAt (x := (s0, s0)))
  obtain ⟨δ, hδ, hδH⟩ := hc (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs hsd => ?_⟩
  have hs0 : s ≠ s0 := hs
  have hne : s - s0 ≠ 0 := sub_ne_zero.2 hs0
  have hdist : |s - s0| < δ := by simpa [Real.dist_eq] using hsd
  have hbd : ∀ r ∈ Ι s0 s, ‖H r s - H s0 s0‖ ≤ ε / 2 := by
    intro r hr
    have hr' : |r - s0| ≤ |s - s0| := by
      rcases le_total s0 s with h | h
      · rw [uIoc_of_le h] at hr
        rw [abs_of_nonneg (by linarith [hr.1]), abs_of_nonneg (by linarith)]
        linarith [hr.2]
      · rw [uIoc_of_ge h] at hr
        rw [abs_of_nonpos (by linarith [hr.2]), abs_of_nonpos (by linarith)]
        linarith [hr.1]
    have h1 : dist (r, s) (s0, s0) < δ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]; exact lt_of_le_of_lt hr' hdist
      · rw [Real.dist_eq]; exact hdist
    have := hδH h1
    rw [Real.dist_eq] at this
    exact (by simpa [Real.norm_eq_abs] using this.le)
  have hint : IntervalIntegrable (fun r => H r s) volume s0 s :=
    (hH.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  have h1 : (∫ r in s0..s, H r s) - (s - s0) * H s0 s0 = ∫ r in s0..s, (H r s - H s0 s0) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := s0) (b := s)
    (f := fun r => H r s - H s0 s0) (C := ε / 2) hbd
  rw [← h1] at h2
  have h3 : (s - s0)⁻¹ * (∫ r in s0..s, H r s) - H s0 s0 =
      (s - s0)⁻¹ * ((∫ r in s0..s, H r s) - (s - s0) * H s0 s0) := by
    field_simp
  rw [Real.dist_eq, h3, ← Real.norm_eq_abs, norm_mul, norm_inv, Real.norm_eq_abs]
  have hpos : 0 < |s - s0| := abs_pos.2 hne
  calc |s - s0|⁻¹ * ‖(∫ r in s0..s, H r s) - (s - s0) * H s0 s0‖
      ≤ |s - s0|⁻¹ * (ε / 2 * |s - s0|) := by
        gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

section Flow

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem hs_meas_flow {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) (hn : SgNoise W) {t : ℝ} (ht : 0 ≤ t) (y : Euc d) :
    Measurable (fun o => flowMap q B (fun s => W s o) t y) := by
  have h1 : Measurable (fun p : Ω × Euc d => flowMap q B (fun s => W s p.1) t p.2) :=
    sg_measurable_flowMap hn hq.le hm hB ht
  have h2 : Measurable (fun o : Ω => (o, y)) := measurable_id.prodMk measurable_const
  have h3 := h1.comp h2
  exact h3

/-- Continuity of `(r, τ, x) ↦ E a_r(φ_τ x)` for a bounded jointly continuous `a`. -/
theorem hs_cont_sg [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {T : ℝ}
    (hT : 0 ≤ T) {a : ℝ → Euc d → ℝ} (ha : Continuous fun p : ℝ × Euc d => a p.1 p.2) {K : ℝ}
    (hK : ∀ r y, |a r y| ≤ K) :
    ContinuousOn (fun p : ℝ × ℝ × Euc d => sg P W q B p.2.1 (a p.1) p.2.2)
      {p : ℝ × ℝ × Euc d | p.2.1 ∈ Icc 0 T} := by
  have hn := sgNoise_of_brownian hW
  obtain ⟨C, hC, hpath⟩ := kl_pathω (q := q) (Mb := Mb) hq hm hT hn
  unfold sg
  refine continuousOn_of_dominated (bound := fun _ => K) (fun p hp => ?_) (fun p hp => ?_)
    (integrable_const _) (Eventually.of_forall fun o => ?_)
  · have hm1 := hs_meas_flow (W := W) hq (by omega) hB hn hp.1 p.2.2
    exact ((ha.comp (continuous_const.prodMk continuous_id)).measurable.comp hm1).aestronglyMeasurable
  · exact Eventually.of_forall fun o => by simpa using hK _ _
  · have hk := (hpath B hB o).cont_phi
    have h1 : ContinuousOn (fun p : ℝ × ℝ × Euc d => (p.2.1, p.2.2))
        {p : ℝ × ℝ × Euc d | p.2.1 ∈ Icc 0 T} := by fun_prop
    have h2 : ContinuousOn (fun p : ℝ × ℝ × Euc d =>
        flowMap q B (fun s => W s o) p.2.1 p.2.2) {p : ℝ × ℝ × Euc d | p.2.1 ∈ Icc 0 T} :=
      hk.comp h1 (fun p hp => ⟨hp, mem_univ _⟩)
    exact (ha.comp_continuousOn ((continuousOn_fst).prodMk h2))

theorem hs_sg_sub [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {τ : ℝ}
    (hτ : 0 ≤ τ) {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) {Kf Kg : ℝ}
    (hKf : ∀ y, |f y| ≤ Kf) (hKg : ∀ y, |g y| ≤ Kg) (x : Euc d) :
    sg P W q B τ (fun y => f y - g y) x = sg P W q B τ f x - sg P W q B τ g x := by
  have hn := sgNoise_of_brownian hW
  have hm1 := hs_meas_flow (W := W) hq hm hB hn hτ x
  unfold sg
  refine integral_sub ?_ ?_
  · exact Integrable.of_bound (hf.measurable.comp hm1).aestronglyMeasurable Kf
      (Eventually.of_forall fun o => by simpa using hKf _)
  · exact Integrable.of_bound (hg.measurable.comp hm1).aestronglyMeasurable Kg
      (Eventually.of_forall fun o => by simpa using hKg _)

/-- **Duhamel principle.**  If `v_s = v_0 + ∫ a` is a family of `C²` functions, `a`, `v`, `F` are bounded
and jointly continuous and `L v_s = a_s - F_s` (`L = kolmL`), then `v_t = P_t v_0 + ∫_0^t P_{t-s} F_s ds`. -/
theorem hs_duhamel [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {T : ℝ}
    (hT : 0 < T) {v a F : ℝ → Euc d → ℝ} (hvc : Continuous fun p : ℝ × Euc d => v p.1 p.2)
    (hac : Continuous fun p : ℝ × Euc d => a p.1 p.2)
    (hFc : Continuous fun p : ℝ × Euc d => F p.1 p.2) {Kv Ka KF : ℝ}
    (hKv : ∀ r y, |v r y| ≤ Kv) (hKa : ∀ r y, |a r y| ≤ Ka) (hKF : ∀ r y, |F r y| ≤ KF)
    (hv2 : ∀ s ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (v s) ∧ ∃ M1 M2 : ℝ,
      (∀ y, ‖fderiv ℝ (v s) y‖ ≤ M1) ∧ ∀ y, ‖iteratedFDeriv ℝ 2 (v s) y‖ ≤ M2)
    (hint : ∀ s ∈ Icc (0 : ℝ) T, ∀ s0 ∈ Icc (0 : ℝ) T, ∀ y,
      v s y - v s0 y = ∫ r in s0..s, a r y)
    (hL : ∀ s ∈ Icc (0 : ℝ) T, ∀ y, kolmL q B (v s) y = a s y - F s y) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (x : Euc d) :
    v t x = sg P W q B t (v 0) x + ∫ s in (0 : ℝ)..t, sg P W q B (t - s) (F s) x := by
  have hn := sgNoise_of_brownian hW
  have hm1 : 1 ≤ m := by omega
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · subst h0
    simp [gs_sg_zero hq.le hm1 hB hn]
  have hT0 : 0 ≤ T := hT.le
  obtain ⟨C, hC, hpath⟩ := kl_pathω (q := q) (Mb := Mb) hq hm hT0 hn
  set Y : ℝ → Ω → Euc d := fun τ o => flowMap q B (fun s => W s o) τ x with hY
  -- continuity of `ψ` and of the candidate derivative
  have hS : ∀ {g : ℝ → Euc d → ℝ} {K : ℝ}, (Continuous fun p : ℝ × Euc d => g p.1 p.2) →
      (∀ r y, |g r y| ≤ K) → ContinuousOn (fun s : ℝ => sg P W q B (t - s) (g s) x) (Icc 0 t) := by
    intro g K hg hK
    have h := hs_cont_sg hW hq hm hB hT0 hg hK
    have h2 : ContinuousOn (fun s : ℝ => ((s, t - s, x) : ℝ × ℝ × Euc d)) (Icc 0 t) := by fun_prop
    exact h.comp h2 (fun s hs => by
      show t - s ∈ Icc (0 : ℝ) T
      exact ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩)
  have hψc := hS hvc hKv
  have hFi : IntervalIntegrable (fun s : ℝ => sg P W q B (t - s) (F s) x) volume 0 t :=
    (hS hFc hKF).intervalIntegrable_of_Icc htpos.le
  -- derivative of `ψ`
  have hder : ∀ s0 ∈ Ioo (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => sg P W q B (t - s) (v s) x) (sg P W q B (t - s0) (F s0) x) s0 := by
    intro s0 hs0
    have hs0T : s0 ∈ Icc (0 : ℝ) T := ⟨hs0.1.le, hs0.2.le.trans ht.2⟩
    have hτ0 : 0 < t - s0 := by linarith [hs0.2]
    obtain ⟨hcd, M1, M2, hM1, hM2⟩ := hv2 s0 hs0T
    -- the Kolmogorov part
    have hK := (pois_kolmogorov hq hm hB hW hcd hM1 hM2).2.2.1 x (t - s0) hτ0
    have hBq : HasDerivAt (fun s : ℝ => sg P W q B (t - s) (v s0) x)
        (-(sg P W q B (t - s0) (kolmL q B (v s0)) x)) s0 := by
      have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) s0 := by
        simpa using (hasDerivAt_id s0).const_sub t
      have := hK.comp s0 h1
      exact this.congr_deriv (by ring)
    -- the time-dependence of `v`
    have hA : HasDerivAt (fun s : ℝ => sg P W q B (t - s) (v s) x - sg P W q B (t - s) (v s0) x)
        (sg P W q B (t - s0) (a s0) x) s0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      have hev : ∀ᶠ s in 𝓝[≠] s0, s ∈ Ioo (0 : ℝ) t :=
        nhdsWithin_le_nhds (Ioo_mem_nhds hs0.1 hs0.2)
      -- global clamped flow
      set Yc : ℝ → Ω → Euc d := fun s o => flowMap q B (fun r => W r o) (clampT T (t - s)) x
        with hYc
      have hYcc : ∀ o, Continuous fun s : ℝ => Yc s o := fun o => by
        have hk := (hpath B hB o).cont_phi
        have h1 : Continuous fun s : ℝ => ((clampT T (t - s), x) : ℝ × Euc d) :=
          ((continuous_clampT T).comp (continuous_const.sub continuous_id)).prodMk continuous_const
        exact hk.comp_continuous h1 (fun s => ⟨clampT_mem hT0 _, mem_univ _⟩)
      have hYeq : ∀ s ∈ Ioo (0 : ℝ) t, ∀ o, Yc s o = Y (t - s) o := fun s hs o => by
        simp only [hYc, hY]
        rw [clampT_of_mem (⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩ : t - s ∈ Icc (0 : ℝ) T)]
      -- the integrand
      set G : ℝ → Ω → ℝ := fun s o => (s - s0)⁻¹ * (v s (Y (t - s) o) - v s0 (Y (t - s) o))
        with hG
      have hmY : ∀ s ∈ Ioo (0 : ℝ) t, Measurable fun o => Y (t - s) o := fun s hs =>
        hs_meas_flow (W := W) hq hm1 hB hn (by linarith [hs.2]) x
      have hvs : ∀ s, Continuous (v s) := fun s => hvc.comp (continuous_const.prodMk continuous_id)
      have hslope : ∀ s ∈ Ioo (0 : ℝ) t,
          slope (fun s : ℝ => sg P W q B (t - s) (v s) x - sg P W q B (t - s) (v s0) x) s0 s =
            ∫ o, G s o ∂P := by
        intro s hs
        have hsT : t - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
        have hsub := hs_sg_sub hW hq hm1 hB hsT.1 (f := v s) (g := v s0) (hvs s) (hvs s0)
          (hKv s) (hKv s0) x
        have hI : ∫ o, G s o ∂P = (s - s0)⁻¹ *
            sg P W q B (t - s) (fun y => v s y - v s0 y) x := by
          unfold sg
          rw [← integral_const_mul]
        rw [hI, hsub, slope_def_field, sub_self, sub_zero, div_eq_inv_mul]
      have hbdG : ∀ s ∈ Ioo (0 : ℝ) t, s ≠ s0 → ∀ o, ‖G s o‖ ≤ Ka := by
        intro s hs hne o
        have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
        have h1 := hint s hsT s0 hs0T (Y (t - s) o)
        have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := s0) (b := s)
          (f := fun r => a r (Y (t - s) o)) (C := Ka) (fun r _ => by simpa using hKa r _)
        have hpos : 0 < |s - s0| := abs_pos.2 (sub_ne_zero.2 hne)
        simp only [hG]
        rw [h1, norm_mul, norm_inv, Real.norm_eq_abs]
        calc |s - s0|⁻¹ * ‖∫ r in s0..s, a r (Y (t - s) o)‖ ≤ |s - s0|⁻¹ * (Ka * |s - s0|) := by
              gcongr
          _ = Ka := by field_simp
      have hlim : ∀ o, Tendsto (fun s => G s o) (𝓝[≠] s0) (𝓝 (a s0 (Y (t - s0) o))) := by
        intro o
        have hHc : Continuous fun p : ℝ × ℝ => a p.1 (Yc p.2 o) :=
          hac.comp (continuous_fst.prodMk ((hYcc o).comp continuous_snd))
        have h1 := hs_avg_tendsto (H := fun r s => a r (Yc s o)) hHc s0
        rw [hYeq s0 hs0 o] at h1
        refine h1.congr' ?_
        filter_upwards [hev] with s hs
        have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
        simp only [hG]
        rw [hint s hsT s0 hs0T (Y (t - s) o)]
        congr 1
        refine intervalIntegral.integral_congr (fun r _ => ?_)
        simp only [hYeq s hs o]
      have hmain : Tendsto (fun s => ∫ o, G s o ∂P) (𝓝[≠] s0)
          (𝓝 (∫ o, a s0 (Y (t - s0) o) ∂P)) := by
        refine tendsto_integral_filter_of_dominated_convergence (fun _ => Ka) ?_ ?_
          (integrable_const _) (Eventually.of_forall hlim)
        · filter_upwards [hev] with s hs
          have := (hvs s).measurable.comp (hmY s hs)
          have h2 := (hvs s0).measurable.comp (hmY s hs)
          exact (measurable_const.mul (this.sub h2)).aestronglyMeasurable
        · filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
          exact Eventually.of_forall fun o => hbdG s hs hne o
      refine hmain.congr' ?_
      filter_upwards [hev] with s hs
      exact (hslope s hs).symm
    have hψ : HasDerivAt (fun s : ℝ => sg P W q B (t - s) (v s) x)
        (sg P W q B (t - s0) (a s0) x + -(sg P W q B (t - s0) (kolmL q B (v s0)) x)) s0 :=
      (hA.add hBq).congr_of_eventuallyEq (Eventually.of_forall fun s => by simp)
    refine hψ.congr_deriv ?_
    -- identify the derivative
    have hFeq : F s0 = fun y => a s0 y - kolmL q B (v s0) y := funext fun y => by
      have := hL s0 hs0T y
      linarith
    have hKc : Continuous (kolmL q B (v s0)) := by
      have : kolmL q B (v s0) = fun y => a s0 y - F s0 y := funext fun y => hL s0 hs0T y
      rw [this]
      exact (hac.comp (continuous_const.prodMk continuous_id)).sub
        (hFc.comp (continuous_const.prodMk continuous_id))
    have hKb : ∀ y, |kolmL q B (v s0) y| ≤ Ka + KF := fun y => by
      rw [hL s0 hs0T y]
      exact (abs_sub _ _).trans (add_le_add (hKa _ _) (hKF _ _))
    have has : Continuous (a s0) := hac.comp (continuous_const.prodMk continuous_id)
    rw [hFeq, hs_sg_sub hW hq hm1 hB hτ0.le (f := a s0) (g := kolmL q B (v s0)) has hKc
      (hKa s0) hKb x]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htpos.le hψc hder hFi
  rw [hftc]
  simp only [sub_zero, sub_self]
  rw [gs_sg_zero hq.le hm1 hB hn]
  ring

end Flow

theorem hs_gsD_norm {φ : Euc d → ℝ} {n : ℕ} (hφ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) φ)
    (e y : Euc d) :
    ‖iteratedFDeriv ℝ n (gsD e φ) y‖ ≤ ‖e‖ * ‖iteratedFDeriv ℝ (n + 1) φ y‖ := by
  have h1 : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ φ) y :=
    (hφ.fderiv_right (m := n) (by exact_mod_cast le_refl _)).contDiffAt
  have := norm_iteratedFDeriv_clm_apply_const (c := e) (x := y) (n := n) (N := (n : WithTop ℕ∞))
    h1 le_rfl
  rw [norm_iteratedFDeriv_fderiv] at this
  exact this

section CD1

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- `‖D sg_s h‖ ≤ e^{q+Mb} M1` on `[0,1]`. -/
theorem hs_D_bd [IsProbabilityMeasure P] (hW : SgNoise W) {q Mb : ℝ} (hq : 0 < q) {m : ℕ}
    (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {h : Euc d → ℝ}
    (hh : ContDiff ℝ 2 h) {M0 M1 : ℝ} (hM0 : ∀ y, ‖h y‖ ≤ M0) (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (y : Euc d) :
    ‖fderiv ℝ (sg P W q B s h) y‖ ≤ Real.exp (q + Mb) * M1 := by
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  have := sg_fderiv_bound q Mb hq m hm P W hW B hB h (hh.of_le (by norm_num)) M0 M1 hM0 hM1 s hs.1 y
  refine this.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) ((norm_nonneg _).trans (hM1 0)))
  nlinarith [hs.2, hs.1]

set_option maxHeartbeats 1000000 in
/-- **Commutator Duhamel formula** (smooth drift, compactly supported smooth data):
`∂_e P_t f = P_t ∂_e f + ∫_0^t P_{t-s} (Du_s · (-q e + DB e)) ds`, `u_s = P_s f`. -/
theorem hs_cd1 [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q M3 : ℝ} (hq : 0 < q)
    {B : Euc d → Euc d} (hB : HasCbBound 3 M3 B) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (e : Euc d) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Euc d) :
    fderiv ℝ (sg P W q B t f) x e = sg P W q B t (gsD e f) x +
      ∫ s in (0 : ℝ)..t, sg P W q B (t - s)
        (fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e)) x := by
  have hWs := sgNoise_of_brownian hW
  have hM3 : 0 ≤ M3 := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  obtain ⟨C, -, hC⟩ := hfc.exists_bound_iteratedFDeriv hf 3
  have hM0 : ∀ y, ‖f y‖ ≤ C := fun y => by
    have := hC 0 (by norm_num) y; rwa [norm_iteratedFDeriv_zero] at this
  have hM1 : ∀ y, ‖fderiv ℝ f y‖ ≤ C := fun y => by
    have := hC 1 (by norm_num) y; rwa [norm_iteratedFDeriv_one] at this
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ C := fun y => hC 2 (by norm_num) y
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf3 : ContDiff ℝ 3 f := hf.of_le (by norm_num)
  have hKf := pois_kolmogorov hq (m := 3) (by norm_num) hB hW hf2 hM1 hM2
  have hI1 := hKf.2.2.2 1 one_pos
  have hB2 : ContDiff ℝ 2 B := hB.1.of_le (by norm_num)
  obtain ⟨⟨M0g, hM0g⟩, ⟨M1g, hM1g⟩, ⟨M2g, hM2g⟩⟩ := gs_g_bounds (q := q) hB2 hf hfc
  have hgs := gs_g_smooth (q := q) hB2 hf
  have hKg := pois_kolmogorov hq (m := 3) (by norm_num) hB hW hgs hM1g
    (fun y => by simpa using hM2g y)
  have hIg := hKg.2.2.2 1 one_pos
  obtain ⟨hc1, hc2, hderU, hderV⟩ := gs_package (P := P) (W := W) hq hB hW hf hfc e
  have hB1 : ∀ y, ‖fderiv ℝ B y‖ ≤ M3 := fun y => by
    have := hB.2 1 (by norm_num) y; rwa [norm_iteratedFDeriv_one] at this
  -- clamped families
  have hcl : Continuous fun p : ℝ × Euc d => ((clampT 1 p.1, p.2) : ℝ × Euc d) :=
    ((continuous_clampT 1).comp continuous_fst).prodMk continuous_snd
  have hclm : ∀ p : ℝ × Euc d, ((clampT 1 p.1, p.2) : ℝ × Euc d) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set (Euc d)) :=
    fun p => ⟨clampT_mem zero_le_one _, mem_univ _⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ → Euc d → ℝ, ∀ s y,
      v s y = fderiv ℝ (sg P W q B (clampT 1 s) f) y e := ⟨fun s y => _, fun s y => rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ → Euc d → ℝ, ∀ s y,
      a s y = fderiv ℝ (sg P W q B (clampT 1 s) (kolmL q B f)) y e :=
    ⟨fun s y => _, fun s y => rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → Euc d → ℝ, ∀ s y,
      F s y = fderiv ℝ (sg P W q B (clampT 1 s) f) y (-q • e + fderiv ℝ B y e) :=
    ⟨fun s y => _, fun s y => rfl⟩
  have hvc : Continuous fun p : ℝ × Euc d => v p.1 p.2 := by
    have := hc2.comp_continuous hcl hclm
    refine this.congr (fun p => ?_)
    simp only [Function.comp, hvdef]
  have hac : Continuous fun p : ℝ × Euc d => a p.1 p.2 := by
    have := ((ContinuousLinearMap.apply ℝ ℝ e).continuous.comp_continuousOn
      hIg.cont_fderiv).comp_continuous hcl hclm
    refine this.congr (fun p => ?_)
    simp only [Function.comp, hadef]
    rfl
  have hFc : Continuous fun p : ℝ × Euc d => F p.1 p.2 := by
    have hb : Continuous fun y : Euc d => -q • e + fderiv ℝ B y e :=
      continuous_const.add ((hB2.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    have h1 : ContinuousOn (fun p : ℝ × Euc d =>
        fderiv ℝ (sg P W q B p.1 f) p.2 (-q • e + fderiv ℝ B p.2 e)) (Icc 0 1 ×ˢ univ) :=
      hI1.cont_fderiv.clm_apply (hb.comp continuous_snd).continuousOn
    have := h1.comp_continuous hcl hclm
    refine this.congr (fun p => ?_)
    simp only [Function.comp, hFdef]
  -- bounds
  have hDf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (sg P W q B s f) y‖ ≤ Real.exp (q + M3) * C :=
    fun s hs y => hs_D_bd hWs hq (by norm_num) hB hf2 hM0 hM1 hs y
  have hDg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, ‖fderiv ℝ (sg P W q B s (kolmL q B f)) y‖ ≤
      Real.exp (q + M3) * M1g := fun s hs y =>
    hs_D_bd hWs hq (by norm_num) hB hgs hM0g hM1g hs y
  have hKv : ∀ r y, |v r y| ≤ Real.exp (q + M3) * C * ‖e‖ := fun r y => by
    rw [hvdef]
    have := (fderiv ℝ (sg P W q B (clampT 1 r) f) y).le_opNorm e
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right (hDf _ (clampT_mem zero_le_one r) y) (norm_nonneg _))
  have hKa : ∀ r y, |a r y| ≤ Real.exp (q + M3) * M1g * ‖e‖ := fun r y => by
    rw [hadef]
    have := (fderiv ℝ (sg P W q B (clampT 1 r) (kolmL q B f)) y).le_opNorm e
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right (hDg _ (clampT_mem zero_le_one r) y) (norm_nonneg _))
  have hKF : ∀ r y, |F r y| ≤ Real.exp (q + M3) * C * (q * ‖e‖ + M3 * ‖e‖) := fun r y => by
    rw [hFdef]
    have h1 := (fderiv ℝ (sg P W q B (clampT 1 r) f) y).le_opNorm (-q • e + fderiv ℝ B y e)
    rw [Real.norm_eq_abs] at h1
    have h2 : ‖-q • e + fderiv ℝ B y e‖ ≤ q * ‖e‖ + M3 * ‖e‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_neg, Real.norm_of_nonneg hq.le]
      · exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB1 y) (norm_nonneg _))
    exact h1.trans (mul_le_mul (hDf _ (clampT_mem zero_le_one r) y) h2 (norm_nonneg _)
      ((norm_nonneg _).trans (hDf 0 ⟨le_rfl, zero_le_one⟩ 0)))
  -- regularity of the slices
  have hu3 : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ 3 (sg P W q B s f) ∧
      ∃ M' : ℝ, ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j (sg P W q B s f) y‖ ≤ M' := fun s hs =>
    gs_sg_cd (P := P) (W := W) hq hB hWs (k := 3) le_rfl hf3 (M := C) (fun i hi => hC i hi)
      (T := 1) hs
  have hv2 : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ 2 (v s) ∧ ∃ M1 M2 : ℝ,
      (∀ y, ‖fderiv ℝ (v s) y‖ ≤ M1) ∧ ∀ y, ‖iteratedFDeriv ℝ 2 (v s) y‖ ≤ M2 := by
    intro s hs
    obtain ⟨hφ, M', hM'⟩ := hu3 s hs
    have hvs : v s = gsD e (sg P W q B s f) := by
      funext y; rw [hvdef, clampT_of_mem hs]; rfl
    rw [hvs]
    refine ⟨gs_D_contDiff (n := 2) hφ e, ‖e‖ * M', ‖e‖ * M', fun y => ?_, fun y => ?_⟩
    · have h1 := hs_gsD_norm (n := 1) (by exact_mod_cast hφ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) e y
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact h1.trans (mul_le_mul_of_nonneg_left (hM' 2 (by norm_num) y) (norm_nonneg _))
    · exact (hs_gsD_norm (n := 2) (by exact_mod_cast hφ) e y).trans
        (mul_le_mul_of_nonneg_left (hM' 3 le_rfl y) (norm_nonneg _))
  -- the time derivative of `v`
  have hdv : ∀ y, ∀ r ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s => v s y) (a r y) (Icc 0 1) r := by
    intro y r hr
    have h1 := hderV r hr y
    have e2 : sg P W q B r (kolmL q B f) = kolmL q B (sg P W q B r f) :=
      funext (gs_K3 hq hB hW hf hfc hr.1)
    have e1 : gsD e (kolmL q B (sg P W q B r f)) y = a r y := by
      rw [hadef, clampT_of_mem hr, e2]; rfl
    rw [e1] at h1
    refine h1.congr (fun s hs => ?_) ?_
    · rw [hvdef, clampT_of_mem hs]
    · rw [hvdef, clampT_of_mem hr]
  have hftc : ∀ y, ∀ s1 s2 : ℝ, 0 ≤ s1 → s1 ≤ s2 → s2 ≤ 1 →
      v s2 y - v s1 y = ∫ r in s1..s2, a r y := by
    intro y s1 s2 h1 h12 h2
    have hcv : Continuous fun r => v r y := hvc.comp (continuous_id.prodMk continuous_const)
    have hca : Continuous fun r => a r y := hac.comp (continuous_id.prodMk continuous_const)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h12 hcv.continuousOn
      (fun r hr => (hdv y r ⟨h1.trans hr.1.le, hr.2.le.trans h2⟩).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt h1 hr.1) (lt_of_lt_of_le hr.2 h2)))
      (hca.intervalIntegrable _ _)]
  have hint : ∀ s ∈ Icc (0 : ℝ) 1, ∀ s0 ∈ Icc (0 : ℝ) 1, ∀ y,
      v s y - v s0 y = ∫ r in s0..s, a r y := by
    intro s hs s0 hs0 y
    rcases le_total s0 s with h | h
    · exact hftc y s0 s hs0.1 h hs.2
    · rw [intervalIntegral.integral_symm, ← hftc y s s0 hs.1 h hs0.2]
      ring
  have hL : ∀ s ∈ Icc (0 : ℝ) 1, ∀ y, kolmL q B (v s) y = a s y - F s y := by
    intro s hs y
    obtain ⟨hφ, -⟩ := hu3 s hs
    have h1 := gs_D_kolmL (q := q) (hB.1.of_le (by norm_num)) hφ e y
    have e2 : sg P W q B s (kolmL q B f) = kolmL q B (sg P W q B s f) :=
      funext (gs_K3 hq hB hW hf hfc hs.1)
    have e3 : a s y = gsD e (kolmL q B (sg P W q B s f)) y := by
      rw [hadef, clampT_of_mem hs, e2]; rfl
    have e4 : v s = gsD e (sg P W q B s f) := by
      funext y; rw [hvdef, clampT_of_mem hs]; rfl
    have e5 : F s y = fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e) := by
      rw [hFdef, clampT_of_mem hs]
    rw [e3, e4, e5, h1]
    ring
  have key := hs_duhamel hW hq (m := 3) (by norm_num) hB (T := 1) one_pos hvc hac hFc hKv hKa hKF
    hv2 hint hL ht x
  have hv0 : v 0 = gsD e f := by
    funext y
    rw [hvdef, clampT_of_mem (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1)]
    rw [show sg P W q B 0 f = f from funext (gs_sg_zero hq.le (by norm_num) hB hWs f)]
    rfl
  have hvt : v t x = fderiv ℝ (sg P W q B t f) x e := by
    rw [hvdef, clampT_of_mem ht]
  rw [hv0, hvt] at key
  rw [key]
  congr 1
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hFs : F s = fun y => fderiv ℝ (sg P W q B s f) y (-q • e + fderiv ℝ B y e) :=
    funext fun y => by rw [hFdef, clampT_of_mem hs']
  rw [hFs]

end CD1

end HRS.MS.PoisHigh
