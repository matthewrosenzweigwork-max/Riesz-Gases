import HRS.ME.CritEngine
import HRS.ME.CritBures
import HRS.ME.CritSpec
import HRS.MD.EQBurnBurnMain
import HRS.MD.EQBurnBurnInit
import HRS.MD.EQTrace
import HRS.MD.Stat
import HRS.MD.EQRemInt13
import HRS.Uniform.Q14Aux6
import HRS.Uniform.Q07cAux7
import HRS.Uniform.Q48cCov

/-!
# Task A4: `crit_burnin_of_evo` (proof of `HRS.ME.Crit.crit_burnin_of_evo`)

Route of `HRS.MD.EQBurnBurn.eq_burnin_of_evo_proof` with the critical engine `HRS.ME.CritEngine.crit_engine_proof` (single `W_2`
inequality, Bures cost) in place of `eqb_engine`, the remainder term from `CritForcing`, and the Bures term by Tonelli, the uniform
Bures estimate `HRS.ME.CritBures.crit_bures2_uniform_proof` and stationarity.  At `s = d/2`, `δ_N² ≤ 4 N⁻¹`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.CritBurnin

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.T25P HRS.MD.EQ29 HRS.MD.EQBurnBurn

variable {d : ℕ}

/-- The entries of the empirical covariance form are measurable in the configuration. -/
theorem crit_bu_entry_meas {m q : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (hq : 0 ≤ q) {N : ℕ} (hN : 0 < N)
    (x y : NegSobolev d m) :
    Measurable fun X : Config d N => covForm m q (empirical X) x y := by
  have e : (fun X : Config d N => covForm m q (empirical X) x y) = fun X : Config d N =>
      ∑ j : Fin d, (N : ℝ)⁻¹ * ∑ i : Fin N, inner ℝ (Real.sqrt (2 * q) • bVec m j (X i)) x *
        inner ℝ (Real.sqrt (2 * q) • bVec m j (X i)) y := by
    funext X
    rw [HRS.Uniform.Q14.q14_covForm_apply hm hq (empirical X) x y]
    refine Finset.sum_congr rfl fun j _ => ?_
    haveI := HRS.empirical_isProbabilityMeasure hN X
    exact HRS.pair_empirical hN X (fun a => inner ℝ (Real.sqrt (2 * q) • bVec m j a) x *
      inner ℝ (Real.sqrt (2 * q) • bVec m j a) y)
  rw [e]
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  have hb : Continuous fun a : Torus d => Real.sqrt (2 * q) • bVec m j a :=
    (HRS.Uniform.Q14.q14_continuous_bVec hm j).const_smul (Real.sqrt (2 * q))
  have h1 : Continuous fun a : Torus d => inner ℝ (Real.sqrt (2 * q) • bVec m j a) x :=
    Continuous.inner hb continuous_const
  have h2 : Continuous fun a : Torus d => inner ℝ (Real.sqrt (2 * q) • bVec m j a) y :=
    Continuous.inner hb continuous_const
  have hc : Continuous fun a : Torus d => inner ℝ (Real.sqrt (2 * q) • bVec m j a) x *
      inner ℝ (Real.sqrt (2 * q) • bVec m j a) y := h1.mul h2
  exact hc.measurable.comp (measurable_pi_apply i)

/-- Measurability of the Bures cost of the empirical covariance, as a function of a measurable parameter. -/
theorem crit_bu_meas {α : Type*} [MeasurableSpace α] {m q : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (hq : 0 ≤ q) {N : ℕ}
    (hN : 0 < N) (D : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) (hD : IsTraceClassCov D)
    (Y : α → Config d N) (hY : Measurable Y) :
    Measurable fun a => bures2 (covForm m q (empirical (Y a))) D := by
  obtain ⟨ι₀, hι₀, e0, -⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type (H := NegSobolev d m)
  haveI := hι₀
  refine HRS.Uniform.Q07c.measurable_bures2 e0 (C := fun a => covForm m q (empirical (Y a))) (D := fun _ => D)
    (fun a => ?_) (fun _ => hD) (fun x y => ?_) (fun x y => measurable_const)
  · haveI := HRS.empirical_isProbabilityMeasure hN (Y a)
    exact (HRS.Uniform.Q14.q14_covForm_trace hm hq (empirical (Y a))).1
  · exact (crit_bu_entry_meas hm hq hN x y).comp hY

/-- The Bures term of the critical burn-in: Tonelli, stationarity (`ν` the law at each time) and the uniform Bures bound. -/
theorem crit_bu_tonelli {m q c a T : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (hq : 0 ≤ q) {N : ℕ} (hN : 0 < N)
    (D : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ) (hD : IsTraceClassCov D)
    {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (hc : 0 < c) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (Y : ℝ → Ω₁ → Config d N)
    (hJ : Measurable fun p : ℝ × Ω₁ => Y (min (a + T) p.1) p.2)
    (ν : Measure (Config d N))
    (hν : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → P₁.map (Y t) = ν)
    {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hB : ∫⁻ x, ENNReal.ofReal (bures2 (covForm m q (empirical x)) D) ∂ν ≤ ENNReal.ofReal B0) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
      bures2 (covForm m q (empirical (Y r ω))) D)) ∂P₁ ≤ ENNReal.ofReal ((1 / (2 * c) + T) * B0) := by
  have hS0 : 0 ≤ a + T := by linarith
  have hK : 0 ≤ 1 / (2 * c) + T := add_nonneg (div_nonneg zero_le_one (by linarith)) hT
  have hBm : Measurable fun x : Config d N => ENNReal.ofReal (bures2 (covForm m q (empirical x)) D) :=
    (crit_bu_meas (α := Config d N) hm hq hN D hD (fun x => x) measurable_id).ennreal_ofReal
  have hg : Continuous fun r : ℝ => Real.exp (-c * max (a - r) 0) ^ 2 :=
    (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_id).max
      continuous_const))).pow 2
  have hG : Measurable fun p : ℝ × Ω₁ => ENNReal.ofReal (Real.exp (-c * max (a - p.1) 0) ^ 2 *
      bures2 (covForm m q (empirical (Y (min (a + T) p.1) p.2))) D) :=
    ((hg.measurable.comp measurable_fst).mul
      (crit_bu_meas hm hq hN D hD (fun p : ℝ × Ω₁ => Y (min (a + T) p.1) p.2) hJ)).ennreal_ofReal
  have hinner : ∀ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
      bures2 (covForm m q (empirical (Y r ω))) D)) =
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) := by
    intro ω
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [min_eq_right hr.2]
  calc ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        bures2 (covForm m q (empirical (Y r ω))) D)) ∂P₁
      = ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D)) ∂P₁ := lintegral_congr hinner
    _ = ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ∫⁻ ω, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
        bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) ∂P₁ :=
        (lintegral_lintegral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) (a + T))) (ν := P₁)
          (f := fun r ω => ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D)) hG.aemeasurable).symm
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
          ENNReal.ofReal B0 := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hYr : Measurable (Y (min (a + T) r)) := hJ.comp (measurable_const.prodMk measurable_id)
        have hfun : ∀ ω, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) =
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
              ENNReal.ofReal (bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) := by
          intro ω
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
        have hmap : ∫⁻ ω, ENNReal.ofReal (bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) ∂P₁ =
            ∫⁻ x, ENNReal.ofReal (bures2 (covForm m q (empirical x)) D) ∂(P₁.map (Y (min (a + T) r))) :=
          (lintegral_map hBm hYr).symm
        rw [show (∫⁻ ω, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
            bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) ∂P₁) =
            ∫⁻ ω, ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2) *
              ENNReal.ofReal (bures2 (covForm m q (empirical (Y (min (a + T) r) ω))) D) ∂P₁ from
            lintegral_congr hfun]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap,
          hν (min (a + T) r) (le_min hS0 hr.1) (min_le_left _ _)]
        gcongr
    _ = (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2)) *
          ENNReal.ofReal B0 := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / (2 * c) + T) * ENNReal.ofReal B0 := by
        gcongr
        exact eqb_exp_lintegral_le hc ha hT
    _ = ENNReal.ofReal ((1 / (2 * c) + T) * B0) := by
        rw [ENNReal.ofReal_mul hK]

/-- At `s = d/2`: `δ_N² ≤ 4 N⁻¹` for `N ≥ 2`. -/
theorem crit_bu_delta_sq {N : ℕ} (hN : 2 ≤ N) :
    deltaN d ((d : ℝ) / 2) N ^ 2 ≤ 4 * (N : ℝ)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hdelta : deltaN d ((d : ℝ) / 2) N = (N : ℝ)⁻¹ * (1 + Real.log N) := by
    unfold deltaN
    rw [if_neg (lt_irrefl _), if_pos rfl, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  have hlogN : Real.log N ≤ 2 * Real.sqrt N - 2 := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hN0)
    rw [Real.log_sqrt hN0.le] at h1
    linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hsqrt0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hδ0 : 0 ≤ deltaN d ((d : ℝ) / 2) N := by
    rw [hdelta]; exact mul_nonneg (inv_nonneg.2 hN0.le) (by linarith)
  have hδle : deltaN d ((d : ℝ) / 2) N ≤ 2 * (N : ℝ)⁻¹ * Real.sqrt N := by
    rw [hdelta]
    have h1 : 1 + Real.log N ≤ 2 * Real.sqrt N := by linarith
    calc (N : ℝ)⁻¹ * (1 + Real.log N) ≤ (N : ℝ)⁻¹ * (2 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hN0.le)
      _ = 2 * (N : ℝ)⁻¹ * Real.sqrt N := by ring
  have hsq2 : (2 * (N : ℝ)⁻¹ * Real.sqrt N) ^ 2 = 4 * (N : ℝ)⁻¹ := by
    calc (2 * (N : ℝ)⁻¹ * Real.sqrt N) ^ 2 = 4 * (N : ℝ)⁻¹ * (Real.sqrt N ^ 2 * (N : ℝ)⁻¹) := by ring
      _ = 4 * (N : ℝ)⁻¹ * ((N : ℝ) * (N : ℝ)⁻¹) := by rw [hsq]
      _ = 4 * (N : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hN0.ne', mul_one]
  have := pow_le_pow_left₀ hδ0 hδle 2
  linarith

theorem crit_burnin_of_evo_proof {d : ℕ} : type_of% (@HRS.ME.Crit.crit_burnin_of_evo d) := by
  classical
  intro hd hs0 hsd V hV βm βp hβm hββ m hm T hT K c Cmax hK hc hCmax hevo hforce
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmd : (d : ℝ) / 2 + 2 < m := by linarith
  have hm1 : (d : ℝ) + 1 < m := by linarith
  have hm3 : (d : ℝ) + 3 ≤ m := by linarith
  have hmh : (d : ℝ) / 2 < m := by linarith
  have hmd2 : (d : ℝ) < 2 * m := by linarith
  have hmcrit : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := max_lt hm1 hmd
  have hK'0 : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Cp, hCp0, hinp⟩ := HRS.MD.EQInit.eq_init_particle_proof hd hs0 hsd V hV βm βp hβm hββ m hmh
  obtain ⟨Cg, hCg0, hing⟩ := HRS.MD.EQInit.eq_init_gauss_proof hd hs0 hsd V hV βm βp hβm hββ m hmh
  obtain ⟨C0, hC0, hbur⟩ := HRS.ME.CritBures.crit_bures2_uniform_proof hd hs0 hsd V hV βm βp hβm hββ m hm3
  obtain ⟨Cf, hCf0, hfor⟩ := hforce
  set S0 : ℝ := Real.sqrt Cp + Real.sqrt Cg with hS0def
  have hS00 : 0 ≤ S0 := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set Q : ℝ := 2 * ((max K 1) ^ 2 + Real.sqrt Cmax) + max K 1 + 1 with hQdef
  have hQ0 : 0 ≤ Q := by
    have h1 := Real.sqrt_nonneg Cmax
    have h2 := sq_nonneg (max K 1)
    have h3 : 0 ≤ max K 1 := le_of_lt hK'0
    rw [hQdef]; linarith
  have hK0 : 0 ≤ 1 / (2 * c) + T := add_nonneg (div_nonneg zero_le_one (by linarith)) hT.le
  have hD1 : 0 ≤ (1 / (2 * c) + T) * C0 := mul_nonneg hK0 hC0.le
  set Kb : ℝ := Real.sqrt (5 * ((1 / (2 * c) + T) * C0)) with hKbdef
  have hKb0 : 0 ≤ Kb := Real.sqrt_nonneg _
  have hCc0 : 0 < Q * S0 + Cf + Q * Kb + 1 := by
    have h1 := mul_nonneg hQ0 hS00
    have h2 := mul_nonneg hQ0 hKb0
    linarith
  refine ⟨Q * S0 + Cf + Q * Kb + 1, c, hCc0, hc, ?_⟩
  intro β hβ ρβ hρβ a ha hqa N hN Ω _ P _ X₀ W X hX Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hq : 0 ≤ β⁻¹ := (inv_pos.2 hβ0).le
  obtain ⟨hρc, -, -⟩ := HRS.MD.EQTrace.eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ β hβ ρβ hρβ N hN
  haveI : IsFiniteMeasure (withDensityReal ρβ) :=
    HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hρc
  have hDtr : IsTraceClassCov (covForm m β⁻¹ (withDensityReal ρβ)) :=
    (HRS.Uniform.Q14.q14_covForm_trace hmd hq _).1
  obtain ⟨Vev, hEv, hdual⟩ := hevo β hβ ρβ hρβ
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π, hπ, ℱ₁, W'', η', hX', hF', hη'm, hη'map, hW2⟩ :=
    HRS.ME.CritEngine.crit_engine_proof hd hs0 hsd V hV hβ0 ρβ hρβ m hmcrit hK'0 hc hT Vev
      (HRS.MD.EQBurnBurn.eqb_ev_max hEv) hdual ha hN P X₀ W X hX P' Z hZ
  have hN0 : 0 < N := by omega
  have hN0R : (0 : ℝ) < N := by exact_mod_cast hN0
  -- the rational notation of the normalized constant
  set u : ℝ := (N : ℝ) ^ (-(1 : ℝ) / 2) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hu2 : u ^ 2 = (N : ℝ)⁻¹ := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num [Real.rpow_neg_one]
  -- stationarity on the enlarged space
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 (a + T) hN P₁ _ _ _ hX'
  have hYm : ∀ t : ℝ≥0, Measurable (fun ω' => X t (π ω')) := fun t =>
    (hF'.adapted t).mono (ℱ₁.le t) le_rfl
  -- the initial term
  have hGprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) := by
    rw [← hstat 0 (by simp; linarith)]
    exact (Measure.isProbabilityMeasure_map_iff (hYm 0).aemeasurable).2 inferInstance
  have hzm : Measurable (zetaE m (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β)) :=
    (HRS.MD.EQLawPath.eqlaw_continuous_zetaE hmd2 (by omega) _).measurable
  have hmap0 : P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω'')) = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β :=
    hstat 0 (by simp; linarith)
  have hζ0m : Measurable (fun ω => zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω))) := by
    rw [hmap0]; exact hzm.comp (hYm 0)
  have hI1 : ∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω))‖ₑ ^ 2 ∂P₁ ≤
      ENNReal.ofReal Cp := by
    rw [hmap0]
    have := lintegral_map (μ := P₁) (f := fun x => ‖zetaE m (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) x‖ₑ ^ 2)
      (g := fun ω' => X (0 : ℝ≥0) (π ω')) (hzm.enorm.pow_const 2) (hYm 0)
    rw [← this, hmap0]
    exact hinp β hβ ρβ hρβ N hN
  have hI2 : ∫⁻ ω, ‖η' ω‖ₑ ^ 2 ∂P₁ ≤ ENNReal.ofReal Cg := by
    have h1 := lintegral_map (μ := P₁) (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := η')
      (measurable_enorm.pow_const 2) hη'm
    have h2 := lintegral_map (μ := P') (f := fun y : NegSobolev d m => ‖y‖ₑ ^ 2) (g := Z 0)
      (measurable_enorm.pow_const 2) (hZ.meas 0)
    rw [← h1, hη'map, h2]
    exact hing β hβ ρβ hρβ P' Z hZ
  obtain ⟨-, hD2⟩ := eqb_init_diff P₁ _ η' hζ0m.aemeasurable hη'm.aemeasurable hCp0.le hCg0.le hI1 hI2
  -- the remainder term
  have hRem := hfor β hβ ρβ hρβ N hN P₁ (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω'))
    (fun t ω' => X t (π ω')) a ha hqa hX'
  have hRemB := eqb_l2_le P₁ (fun ω => (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ
      (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ))) (A := Cf ^ 2 / N) (by positivity) hRem
  have hsqrtR : Real.sqrt (Cf ^ 2 / N) = Cf * u := by
    rw [show Cf ^ 2 / (N : ℝ) = (Cf * u) ^ 2 by rw [mul_pow, hu2, div_eq_mul_inv]]
    exact Real.sqrt_sq (mul_nonneg hCf0 hu0)
  -- the Bures term
  have hJ : Measurable fun p : ℝ × Ω₁ => X (min (a + T) p.1).toNNReal (π p.2) :=
    HRS.MD.EQRem.eqrem_joint_meas ℱ₁ (a + T) (fun t ω' => X t (π ω')) hF'.progressive
  have hν : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → P₁.map (fun ω' => X t.toNNReal (π ω')) =
      canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β := fun t ht0 htS =>
    hstat t.toNNReal (by rw [Real.coe_toNNReal _ ht0]; exact htS)
  have hB0 := hbur β hβ ρβ hρβ N hN
  have hVnn : 0 ≤ (1 / (2 * c) + T) * (C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) :=
    mul_nonneg hK0 (mul_nonneg hC0.le (add_nonneg (inv_nonneg.2 hN0R.le) (sq_nonneg _)))
  have hEB := crit_bu_tonelli hmd hq hN0 (covForm m β⁻¹ (withDensityReal ρβ)) hDtr P₁ hc ha hT.le
    (fun r ω => X r.toNNReal (π ω)) hJ (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) hν
    (B0 := C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))
    (mul_nonneg hC0.le (add_nonneg (inv_nonneg.2 hN0R.le) (sq_nonneg _))) hB0
  have hT3 : (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
      bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^
      (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Kb * u) := by
    refine (ENNReal.rpow_le_rpow hEB (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hVnn (by norm_num), ← Real.sqrt_eq_rpow]
    apply ENNReal.ofReal_le_ofReal
    have hδ := crit_bu_delta_sq (d := d) hN
    have h1 : (N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2 ≤ 5 * (N : ℝ)⁻¹ := by linarith
    have h2 : C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) ≤ C0 * (5 * (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left h1 hC0.le
    have h3 : (1 / (2 * c) + T) * (C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)) ≤
        (1 / (2 * c) + T) * (C0 * (5 * (N : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h2 hK0
    have h4 : (1 / (2 * c) + T) * (C0 * (5 * (N : ℝ)⁻¹)) = 5 * ((1 / (2 * c) + T) * C0) * u ^ 2 := by
      rw [hu2]; ring
    have h5 : 0 ≤ 5 * ((1 / (2 * c) + T) * C0) := by linarith
    calc Real.sqrt ((1 / (2 * c) + T) * (C0 * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2)))
        ≤ Real.sqrt (5 * ((1 / (2 * c) + T) * C0) * u ^ 2) := Real.sqrt_le_sqrt (h3.trans_eq h4)
      _ = Kb * u := by
        rw [Real.sqrt_mul h5, Real.sqrt_sq hu0]
  -- assembling the three terms
  have hT1 : (∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ^ (2 : ℝ)
      ∂P₁) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal S0 := hD2
  have hQe0 : 0 ≤ Q * Real.exp (-c * a) := mul_nonneg hQ0 (Real.exp_pos _).le
  have hT2 : (∫⁻ ω, (⨆ t ∈ ratTimes a T, (coordEnergy m (fun k => statForcingCoord d hs0 hsd V hβ0 ρβ
      (fun t ω' => X t (π ω')) k t ω)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (Cf * u) := by
    refine hRemB.trans (le_of_eq ?_)
    rw [hsqrtR]
  have hfinal : ENNReal.ofReal (Q * Real.exp (-c * a)) * ENNReal.ofReal S0 + ENNReal.ofReal (Cf * u) +
      ENNReal.ofReal Q * ENNReal.ofReal (Kb * u) ≤
      ENNReal.ofReal ((Q * S0 + Cf + Q * Kb + 1) * (Real.exp (-c * a) + u)) := by
    have hE0 : 0 ≤ Real.exp (-c * a) := (Real.exp_pos _).le
    rw [← ENNReal.ofReal_mul hQe0, ← ENNReal.ofReal_mul hQ0,
      ← ENNReal.ofReal_add (mul_nonneg hQe0 hS00) (mul_nonneg hCf0 hu0),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hQe0 hS00) (mul_nonneg hCf0 hu0))
        (mul_nonneg hQ0 (mul_nonneg hKb0 hu0))]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [mul_nonneg (mul_nonneg hQ0 hS00) hu0, mul_nonneg hCf0 hE0,
      mul_nonneg (mul_nonneg hQ0 hKb0) hE0, hE0, hu0]
  refine hW2.trans ?_
  have hA1 : ENNReal.ofReal (Q * Real.exp (-c * a)) * (∫⁻ ω, ‖zetaE m (P₁.map (fun ω'' => X (0 : ℝ≥0) (π ω''))) (X (0 : ℝ≥0) (π ω)) - η' ω‖ₑ ^ (2 : ℝ) ∂P₁) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Q * Real.exp (-c * a)) * ENNReal.ofReal S0 := by gcongr
  have hA3 : ENNReal.ofReal Q * (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 *
      bures2 (covForm m β⁻¹ (empirical (X r.toNNReal (π ω)))) (covForm m β⁻¹ (withDensityReal ρβ)))) ∂P₁) ^
      (1 / (2 : ℝ)) ≤ ENNReal.ofReal Q * ENNReal.ofReal (Kb * u) := by gcongr
  refine (add_le_add (add_le_add hA1 hT2) hA3).trans ?_
  exact hfinal

end HRS.ME.CritBurnin

end
