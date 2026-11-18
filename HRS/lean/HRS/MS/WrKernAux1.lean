import HRS.Whole.Q34Aux18
import HRS.MS.WrRowAux3

/-!
# HRS.MS.WrKernAux1 -- kernel estimates for the whole-space static estimate (WR-13c1)

Pure real analysis on `ℝ^d` for `0 < s < d`, with a probability density `ρ ≤ M` only (no lower bound,
no smoothness, no calibration, no poles).  All constants depend on `(d, s, M, B, K0)` only.

* `wr13c_radial_J`: `∫ g(x-y)² e^{-u g(x-y)} dμ(y) ≤ C J_s(u)` for all `u > 0`
  (`J_s(u) = 1 | 1 + |log u| | 1 + u^{d/s-2}` for `2s < d | = d | > d`).
  Proof by a pointwise cut at `|z| = u^{1/s}` (no substitution needed).
* `wr13c_conv_L2_sub`, `wr13c_conv_L2_crit`, `wr13c_conv_L2_super`, `wr13c_conv_L2_E`: the `L²(μ)` bound for
  `g * f` (`|f| ≤ B`, `‖f‖₁ ≤ ε ≤ 1`) with rate `ε | ε √log(e/ε) | ε^{3/2-s/d}`.
  The case `d/2 < s` is `Q34.l2_bound`; the cases `s ≤ d/2` use a three-zone split
  (`|z| < R`, `R ≤ |z| < 1`, `|z| ≥ 1`) with Young's inequality in the two near zones and the
  trivial bound `g ≤ 1` in the far zone (the far square of `g` is not integrable when `2s ≤ d`).
* `wr13c_conv_L2_delta`: the `δ_N`-form (`δ_N = deltaN d s N`): for `∫|f| ≤ K0 √(δ_N/N)` and `N ≥ N0`,
  `‖g*f‖_{L²(μ)} ≤ C δ_N`.
* `wr13c_sup_conv_small`, `wr13c_sup_conv_delta`: `‖g*f‖_∞ ≤ C ε^{1-s/d}` (`Q34.sup_bound`) and its
  `δ_N`-form.
* `wr13c_sup_conv_eventually_small`: `‖g*f‖_∞ ≤ η` for `N ≥ N1(η)` (uniform `‖z_N‖_∞ → 0` input).
* `wr13c_schur_W`, `wr13c_schur_W_real`: Schur test `‖∫ |h(·,y)| |f(y)| dμ(y)‖_{L²(μ)} ≤ C B ‖f‖_{L²(μ)}` for
  `|h| ≤ B (1 + rieszWeight)` (row bound `wr3_lintegral_W_row`).
* `wr13c_Kmu_nonneg`, `wr13c_Kmu_pair_integrable`, `wr13c_resolvent_norm_le`: positivity of `K_μ`
  with absolute integrability against `μ ⊗ μ` and `‖(I+βK_μ)⁻¹‖ ≤ 1`, from `Q34Aux10-18`.

Adjustments w.r.t. the sketch in `docs/WR_B_PLAN.md`: statements hold for all `u > 0` at once (both
`u ≤ 1` and `u > 1`); the `δ_N`-forms carry an explicit threshold `N0` (depending on `K0`) which makes
`ε = K0 √(δ_N/N) ≤ 1`; the sub-critical case does not need `ε ≤ 1` nor the bound `B`; the Schur test
assumes `0 ≤ B` and allows `0 ≤ s < d`; `Kmu_nonneg` is proved for all `u ∈ L²(μ)` (not only mean zero)
and also in the `Kop`/`MemL2Zero` form.
Helper lemmas carry the prefix `wr13c_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Metric Filter
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ}

/-! ### 1. The radial integral -/

/-- The three-case majorant `J_s(u)` of the radial integral. -/
def wr13c_J (d : ℕ) (s u : ℝ) : ℝ :=
  if 2 * s < d then 1 else if 2 * s = d then 1 + |Real.log u| else 1 + u ^ ((d : ℝ) / s - 2)

theorem wr13c_one_le_J {s : ℝ} (u : ℝ) (hu : 0 < u) : 1 ≤ wr13c_J d s u := by
  unfold wr13c_J
  split_ifs
  · exact le_rfl
  · linarith [abs_nonneg (Real.log u)]
  · linarith [Real.rpow_nonneg hu.le ((d : ℝ) / s - 2)]

theorem wr13c_sq_rpow {s : ℝ} (w : Euc d) : (‖w‖ ^ (-s)) ^ 2 = ‖w‖ ^ (-(2 * s)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1; push_cast; ring

/-- Near/far splitting for a convolution against `μ = ρ dx`: if `Φ ≤ H + 1` then
`∫ Φ(x-y) dμ(y) ≤ M ∫ H + 1`. -/
theorem wr13c_near_far {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (Φ H : Euc d → ℝ≥0∞) (hH : Measurable H) (hΦ : Measurable Φ)
    (hle : ∀ w, Φ w ≤ H w + 1) (x : Euc d) :
    ∫⁻ y, Φ (x - y) ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal M * (∫⁻ w, H w) + 1 := by
  have := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  calc ∫⁻ y, Φ (x - y) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫⁻ y, (H (x - y) + 1) ∂(HRS.Whole.withDensityReal ρ) := lintegral_mono fun y => hle _
    _ = ∫⁻ y, H (x - y) ∂(HRS.Whole.withDensityReal ρ) + 1 := by
        rw [lintegral_add_right _ measurable_const]
        simp
    _ ≤ ENNReal.ofReal M * (∫⁻ w, H w) + 1 :=
        add_le_add (HRS.Whole.Q34.lintegral_conv_le hρ hM H hH x) le_rfl

/-- The radial integrand `g² e^{-u g}` in terms of `t = g(w) = ‖w‖^{-s}`. -/
def wr13c_phi (s u : ℝ) (w : Euc d) : ℝ :=
  (‖w‖ ^ (-s)) ^ 2 * Real.exp (-(u * ‖w‖ ^ (-s)))

theorem wr13c_phi_nonneg (s u : ℝ) (w : Euc d) : 0 ≤ wr13c_phi s u w := by
  unfold wr13c_phi
  positivity

theorem wr13c_measurable_phi (s u : ℝ) : Measurable (wr13c_phi (d := d) s u) := by
  unfold wr13c_phi
  have : Measurable (fun w : Euc d => ‖w‖ ^ (-s)) := measurable_norm.pow_const _
  exact (this.pow_const 2).mul (Real.measurable_exp.comp (measurable_const.mul this).neg)

theorem wr13c_phi_le_sq {s : ℝ} (u : ℝ) (hu : 0 < u) (hs : 0 < s) (w : Euc d) :
    wr13c_phi s u w ≤ ‖w‖ ^ (-(2 * s)) := by
  unfold wr13c_phi
  have ht : 0 ≤ ‖w‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
  have h1 : Real.exp (-(u * ‖w‖ ^ (-s))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  calc (‖w‖ ^ (-s)) ^ 2 * Real.exp (-(u * ‖w‖ ^ (-s))) ≤ (‖w‖ ^ (-s)) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = ‖w‖ ^ (-(2 * s)) := by rw [mul_one, wr13c_sq_rpow]

theorem wr13c_phi_le_lin {s : ℝ} (u : ℝ) (hu : 0 < u) (w : Euc d) :
    wr13c_phi s u w ≤ (1 / u) * ‖w‖ ^ (-s) := by
  unfold wr13c_phi
  set t : ℝ := ‖w‖ ^ (-s) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) _
  have h1 : u * t * Real.exp (-(u * t)) ≤ 1 := by
    have h2 : u * t ≤ Real.exp (u * t) := by linarith [Real.add_one_le_exp (u * t)]
    have h3 : Real.exp (u * t) * Real.exp (-(u * t)) = 1 := by
      rw [← Real.exp_add]; simp
    calc u * t * Real.exp (-(u * t)) ≤ Real.exp (u * t) * Real.exp (-(u * t)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 1 := h3
  have : t ^ 2 * Real.exp (-(u * t)) = (1 / u) * t * (u * t * Real.exp (-(u * t))) := by
    field_simp
  rw [this]
  calc (1 / u) * t * (u * t * Real.exp (-(u * t))) ≤ (1 / u) * t * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (1 / u) * t := mul_one _

theorem wr13c_ball_split (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {u : ℝ} (hu : 0 < u) :
    ∫⁻ w in ball (0 : Euc d) 1, ENNReal.ofReal (wr13c_phi s u w) ≤
      ENNReal.ofReal (sphereArea d / ((d : ℝ) - s) * u ^ ((d : ℝ) / s - 2)) +
        ∫⁻ w in {w : Euc d | ‖w‖ ∈ Ico (u ^ (1 / s)) 1}, ENNReal.ofReal (‖w‖ ^ (-(2 * s))) := by
  have hdm : 0 < (d : ℝ) - s := by linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  set r0 : ℝ := u ^ (1 / s) with hr0
  have hr0p : 0 < r0 := Real.rpow_pos_of_pos hu _
  have hsub : ball (0 : Euc d) 1 ⊆ ball (0 : Euc d) r0 ∪ {w : Euc d | ‖w‖ ∈ Ico r0 1} := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    by_cases h : ‖w‖ < r0
    · left; simpa using h
    · right; exact ⟨not_lt.1 h, hw1⟩
  have h1 : ∫⁻ w in ball (0 : Euc d) r0, ENNReal.ofReal (wr13c_phi s u w) ≤
      ENNReal.ofReal (sphereArea d / ((d : ℝ) - s) * u ^ ((d : ℝ) / s - 2)) := by
    have e : r0 ^ ((d : ℝ) - s) = u ^ ((d : ℝ) / s - 2) * u := by
      rw [hr0, ← Real.rpow_mul hu.le, ← Real.rpow_add_one hu.ne']
      congr 1; field_simp; ring
    calc ∫⁻ w in ball (0 : Euc d) r0, ENNReal.ofReal (wr13c_phi s u w)
        ≤ ∫⁻ w in ball (0 : Euc d) r0, ENNReal.ofReal ((1 / u) * ‖w‖ ^ (-s)) :=
          lintegral_mono fun w => ENNReal.ofReal_le_ofReal (wr13c_phi_le_lin u hu w)
      _ = ∫⁻ w in ball (0 : Euc d) r0, ENNReal.ofReal (1 / u) * ENNReal.ofReal (‖w‖ ^ (-s)) := by
          refine lintegral_congr fun w => ?_
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (1 / u) * ∫⁻ w in ball (0 : Euc d) r0, ENNReal.ofReal (‖w‖ ^ (-s)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (1 / u) *
            ENNReal.ofReal (sphereArea d * (r0 ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
          rw [HRS.Whole.Q34.lintegral_ball_rpow hd hr0p hsd]
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), e]
          congr 1
          field_simp
  calc ∫⁻ w in ball (0 : Euc d) 1, ENNReal.ofReal (wr13c_phi s u w)
      ≤ ∫⁻ w in ball (0 : Euc d) r0 ∪ {w : Euc d | ‖w‖ ∈ Ico r0 1},
          ENNReal.ofReal (wr13c_phi s u w) := lintegral_mono_set hsub
    _ ≤ (∫⁻ w in ball (0 : Euc d) r0, ENNReal.ofReal (wr13c_phi s u w)) +
        ∫⁻ w in {w : Euc d | ‖w‖ ∈ Ico r0 1}, ENNReal.ofReal (wr13c_phi s u w) :=
        lintegral_union_le _ _ _
    _ ≤ _ := by
        refine add_le_add h1 (lintegral_mono fun w => ?_)
        exact ENNReal.ofReal_le_ofReal (wr13c_phi_le_sq u hu hs0 w)

/-- The mass of `g² e^{-ug}` on the unit ball: `≤ C J_s(u)`, for all `u > 0`. -/
theorem wr13c_radial_ball (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ u : ℝ, 0 < u →
      ∫⁻ w in ball (0 : Euc d) 1, ENNReal.ofReal (wr13c_phi s u w) ≤
        ENNReal.ofReal (C0 * wr13c_J d s u) := by
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases h1 : 2 * s < d
  · -- subcritical: `φ ≤ ‖w‖^{-2s}`
    have h2 : 0 < (d : ℝ) - 2 * s := by linarith
    refine ⟨sphereArea d * (1 / ((d : ℝ) - 2 * s)), by positivity, fun u hu => ?_⟩
    have hJ : wr13c_J d s u = 1 := by unfold wr13c_J; rw [if_pos h1]
    rw [hJ, mul_one]
    calc ∫⁻ w in ball (0 : Euc d) 1, ENNReal.ofReal (wr13c_phi s u w)
        ≤ ∫⁻ w in ball (0 : Euc d) 1, ENNReal.ofReal (‖w‖ ^ (-(2 * s))) :=
          lintegral_mono fun w => ENNReal.ofReal_le_ofReal (wr13c_phi_le_sq u hu hs0 w)
      _ = ENNReal.ofReal (sphereArea d * (1 ^ ((d : ℝ) - 2 * s) / ((d : ℝ) - 2 * s))) :=
          HRS.Whole.Q34.lintegral_ball_rpow hd one_pos h1
      _ = _ := by rw [Real.one_rpow, one_div]
  · have h1' : (d : ℝ) ≤ 2 * s := not_lt.1 h1
    by_cases hc : 2 * s = d
    · -- critical
      have hp : (d : ℝ) / s - 2 = 0 := by
        have : (d : ℝ) = 2 * s := hc.symm
        rw [this]; field_simp; ring
      refine ⟨sphereArea d / ((d : ℝ) - s) + sphereArea d / s, by positivity, fun u hu => ?_⟩
      have hJ : wr13c_J d s u = 1 + |Real.log u| := by
        unfold wr13c_J; rw [if_neg h1, if_pos hc]
      rw [hJ]
      refine (wr13c_ball_split hd hs0 hsd hu).trans ?_
      rw [hp, Real.rpow_zero, mul_one]
      have hann : ∫⁻ w in {w : Euc d | ‖w‖ ∈ Ico (u ^ (1 / s)) 1}, ENNReal.ofReal (‖w‖ ^ (-(2 * s))) ≤
          ENNReal.ofReal (sphereArea d / s * |Real.log u|) := by
        have hr0p : 0 < u ^ (1 / s) := Real.rpow_pos_of_pos hu _
        by_cases hu1 : u ≤ 1
        · have hr1 : u ^ (1 / s) ≤ 1 := Real.rpow_le_one hu.le hu1 (by positivity)
          rw [wr3_lintegral_annulus hd hr0p hr1]
          refine ENNReal.ofReal_le_ofReal ?_
          have hex : (d : ℝ) - 1 - 2 * s = -1 := by linarith
          have hint : ∫ t in (u ^ (1 / s))..1, t ^ ((d : ℝ) - 1 - 2 * s) = -(1 / s * Real.log u) := by
            rw [hex]
            simp only [Real.rpow_neg_one]
            rw [integral_inv_of_pos hr0p one_pos, one_div (u ^ (1 / s)), Real.log_inv,
              Real.log_rpow hu]
          rw [hint]
          calc sphereArea d * -(1 / s * Real.log u) = sphereArea d / s * (-Real.log u) := by ring
            _ ≤ sphereArea d / s * |Real.log u| :=
                mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity)
        · push Not at hu1
          have hr1 : 1 ≤ u ^ (1 / s) := Real.one_le_rpow hu1.le (by positivity)
          have hE : Ico (u ^ (1 / s)) 1 = ∅ := Set.Ico_eq_empty (not_lt.2 hr1)
          have hset : {w : Euc d | ‖w‖ ∈ Ico (u ^ (1 / s)) 1} = ∅ := by
            ext w; simp only [mem_setOf_eq, hE]; simp
          rw [hset]; simp
      calc _ ≤ ENNReal.ofReal (sphereArea d / ((d : ℝ) - s)) + ENNReal.ofReal (sphereArea d / s * |Real.log u|) := by
            gcongr
        _ ≤ _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have : 0 ≤ |Real.log u| := abs_nonneg _
            nlinarith [mul_nonneg (div_nonneg hsA hdm.le) this, div_nonneg hsA hs0.le]
    · have hsup : (d : ℝ) < 2 * s := lt_of_le_of_ne h1' (Ne.symm hc)
      have h2 : 0 < 2 * s - (d : ℝ) := by linarith
      refine ⟨sphereArea d / ((d : ℝ) - s) + sphereArea d / (2 * s - (d : ℝ)), by positivity,
        fun u hu => ?_⟩
      have hJ : wr13c_J d s u = 1 + u ^ ((d : ℝ) / s - 2) := by
        unfold wr13c_J; rw [if_neg h1, if_neg hc]
      rw [hJ]
      have hr0p : 0 < u ^ (1 / s) := Real.rpow_pos_of_pos hu _
      have hup : 0 ≤ u ^ ((d : ℝ) / s - 2) := Real.rpow_nonneg hu.le _
      have hann : ∫⁻ w in {w : Euc d | ‖w‖ ∈ Ico (u ^ (1 / s)) 1}, ENNReal.ofReal (‖w‖ ^ (-(2 * s))) ≤
          ENNReal.ofReal (sphereArea d * (u ^ ((d : ℝ) / s - 2) / (2 * s - (d : ℝ)))) := by
        have hsub : {w : Euc d | ‖w‖ ∈ Ico (u ^ (1 / s)) 1} ⊆ {w : Euc d | u ^ (1 / s) ≤ ‖w‖} :=
          fun w hw => hw.1
        refine (lintegral_mono_set hsub).trans ?_
        rw [HRS.Whole.Q34.lintegral_compl_rpow hd hr0p hsup]
        have e : (u ^ (1 / s)) ^ ((d : ℝ) - 2 * s) = u ^ ((d : ℝ) / s - 2) := by
          rw [← Real.rpow_mul hu.le]
          congr 1; field_simp
        rw [e]
      refine (wr13c_ball_split hd hs0 hsd hu).trans ?_
      calc _ ≤ ENNReal.ofReal (sphereArea d / ((d : ℝ) - s) * u ^ ((d : ℝ) / s - 2)) +
            ENNReal.ofReal (sphereArea d * (u ^ ((d : ℝ) / s - 2) / (2 * s - (d : ℝ)))) := by
            gcongr
        _ ≤ _ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have e1 : sphereArea d * (u ^ ((d : ℝ) / s - 2) / (2 * s - (d : ℝ))) =
                sphereArea d / (2 * s - (d : ℝ)) * u ^ ((d : ℝ) / s - 2) := by ring
            rw [e1, ← add_mul]
            have : 0 ≤ sphereArea d / ((d : ℝ) - s) + sphereArea d / (2 * s - (d : ℝ)) := by
              positivity
            nlinarith

theorem wr13c_phi_eq {s : ℝ} (hs0 : 0 < s) (u : ℝ) (z : Euc d) :
    HRS.Whole.rieszKernel d s z ^ 2 * Real.exp (-(u * HRS.Whole.rieszKernel d s z)) =
      wr13c_phi s u z := by
  unfold wr13c_phi
  rw [HRS.Whole.Q34.rieszKernel_eq hs0.ne']

/-- **Radial integral** (`radial_J`): `∫ g(x-y)² e^{-u g(x-y)} dμ(y) ≤ C J_s(u)` for all `u > 0`
(`lintegral` form, so no Bochner junk), uniformly in `x` and in `ρ ≤ M`. -/
theorem wr13c_radial_J (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ u : ℝ, 0 < u → ∀ x : Euc d,
        ∫⁻ y, ENNReal.ofReal (HRS.Whole.rieszKernel d s (x - y) ^ 2 *
            Real.exp (-(u * HRS.Whole.rieszKernel d s (x - y)))) ∂(HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (C * wr13c_J d s u) := by
  obtain ⟨C0, hC0, hball⟩ := wr13c_radial_ball hd hs0 hsd
  refine ⟨max M 0 * C0 + 1, by positivity, fun ρ hρ hM u hu x => ?_⟩
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  rw [max_eq_left hM0]
  simp_rw [wr13c_phi_eq hs0]
  set H : Euc d → ℝ≥0∞ :=
    (ball (0 : Euc d) 1).indicator (fun w => ENNReal.ofReal (wr13c_phi s u w)) with hH
  have hHm : Measurable H :=
    (ENNReal.measurable_ofReal.comp (wr13c_measurable_phi s u)).indicator measurableSet_ball
  have hle : ∀ w : Euc d, ENNReal.ofReal (wr13c_phi s u w) ≤ H w + 1 := by
    intro w
    by_cases hw : w ∈ ball (0 : Euc d) 1
    · simp [hH, hw]
    · have h1 : 1 ≤ ‖w‖ := by simpa using hw
      have h2 : ‖w‖ ^ (-(2 * s)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      calc ENNReal.ofReal (wr13c_phi s u w) ≤ 1 := by
            simpa using ENNReal.ofReal_le_ofReal ((wr13c_phi_le_sq u hu hs0 w).trans h2)
        _ ≤ H w + 1 := le_add_self
  have key := wr13c_near_far hρ hM (fun w => ENNReal.ofReal (wr13c_phi s u w)) H hHm
    (ENNReal.measurable_ofReal.comp (wr13c_measurable_phi s u)) hle x
  refine key.trans ?_
  have hIH : ∫⁻ w, H w ≤ ENNReal.ofReal (C0 * wr13c_J d s u) := by
    rw [hH, lintegral_indicator measurableSet_ball]
    exact hball u hu
  have hJ1 := wr13c_one_le_J (d := d) (s := s) u hu
  calc ENNReal.ofReal M * (∫⁻ w, H w) + 1
      ≤ ENNReal.ofReal M * ENNReal.ofReal (C0 * wr13c_J d s u) + ENNReal.ofReal 1 := by
        gcongr; simp
    _ = ENNReal.ofReal (M * (C0 * wr13c_J d s u) + 1) := by
        rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_add (by positivity) zero_le_one]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [mul_nonneg hM0 hC0, mul_nonneg (mul_nonneg hM0 hC0) (sub_nonneg.2 hJ1)]

/-- Bochner form of `wr13c_radial_J`: the integrand is integrable and its integral is `≤ C J_s(u)`. -/
theorem wr13c_radial_J_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ u : ℝ, 0 < u → ∀ x : Euc d,
        MeasureTheory.Integrable (fun y => HRS.Whole.rieszKernel d s (x - y) ^ 2 *
            Real.exp (-(u * HRS.Whole.rieszKernel d s (x - y)))) (HRS.Whole.withDensityReal ρ) ∧
        ∫ y, HRS.Whole.rieszKernel d s (x - y) ^ 2 *
            Real.exp (-(u * HRS.Whole.rieszKernel d s (x - y))) ∂(HRS.Whole.withDensityReal ρ) ≤
          C * wr13c_J d s u := by
  obtain ⟨C, hC, h⟩ := wr13c_radial_J hd hs0 hsd M
  refine ⟨C, hC, fun ρ hρ hM u hu x => ?_⟩
  have hJ1 := wr13c_one_le_J (d := d) (s := s) u hu
  have hm : Measurable (fun y : Euc d => HRS.Whole.rieszKernel d s (x - y) ^ 2 *
      Real.exp (-(u * HRS.Whole.rieszKernel d s (x - y)))) := by
    simp_rw [wr13c_phi_eq hs0]
    exact (wr13c_measurable_phi s u).comp (measurable_const.sub measurable_id)
  exact HRS.Whole.Q34.integrable_of_lintegral_le (μ := HRS.Whole.withDensityReal ρ) hm
    (fun z => by positivity) (by positivity) (h ρ hρ hM u hu x)

/-! ### 2. The `L²(μ)` convolution estimate -/

theorem wr13c_add3_sq_le (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  calc (a + b + c) ^ 2 ≤ 2 * ((a + b) ^ 2 + c ^ 2) := HRS.Whole.Q34.add_sq_le _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + c ^ 2) := by
        gcongr
        exact HRS.Whole.Q34.add_sq_le a b
    _ = 4 * (a ^ 2 + b ^ 2) + 2 * c ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 + b ^ 2) + 4 * c ^ 2 := by gcongr; norm_num
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by ring

theorem wr13c_lintegral_nu_le {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (Φ : Euc d → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal M * ∫⁻ x, Φ x := by
  rw [HRS.Whole.Q34.lintegral_nu hρ Φ hΦ, ← lintegral_const_mul _ hΦ]
  exact lintegral_mono fun x => mul_le_mul' (ENNReal.ofReal_le_ofReal (hM x)) le_rfl

/-- Abstract three-zone estimate for a convolution: if the kernel `g` is dominated by
`G₁ + G₂ + G₃` with `G₃ ≤ 1`, then Young's inequality in the first two zones (Lebesgue `L²`, converted
to `L²(μ)` by `ρ ≤ M`) and the trivial bound in the third zone give the `L²(μ)` estimate. -/
theorem wr13c_conv_abstract {s : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (F : Euc d → ℝ≥0∞) (hF : Measurable F) (G1 G2 G3 : Euc d → ℝ≥0∞)
    (hG1 : Measurable G1) (hG2 : Measurable G2) (hG3 : Measurable G3) (hG3le : ∀ w, G3 w ≤ 1)
    (hsplit : ∀ w, ENNReal.ofReal (‖w‖ ^ (-s)) ≤ G1 w + G2 w + G3 w) :
    ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * F y) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      4 * (ENNReal.ofReal M * ((∫⁻ w, G1 w) ^ 2 * (∫⁻ y, F y ^ 2) +
        (∫⁻ y, F y) ^ 2 * ∫⁻ w, G2 w ^ 2) + (∫⁻ y, F y) ^ 2) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set A1 : Euc d → ℝ≥0∞ := fun x => ∫⁻ w, G1 w * F (x - w) with hA1
  set A2 : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, F y * G2 (x - y) with hA2
  set A3 : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, G3 (x - y) * F y with hA3
  have hA1m : Measurable A1 :=
    Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d => G1 p.2 * F (p.1 - p.2))
      ((hG1.comp measurable_snd).mul (hF.comp (measurable_fst.sub measurable_snd)))
  have hA2m : Measurable A2 :=
    Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d => F p.2 * G2 (p.1 - p.2))
      ((hF.comp measurable_snd).mul (hG2.comp (measurable_fst.sub measurable_snd)))
  have hA3m : Measurable A3 :=
    Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d => G3 (p.1 - p.2) * F p.2)
      ((hG3.comp (measurable_fst.sub measurable_snd)).mul (hF.comp measurable_snd))
  have hpt : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * F y ≤ A1 x + A2 x + A3 x := by
    intro x
    have e1 : A1 x = ∫⁻ y, G1 (x - y) * F y := by
      have := lintegral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
        (fun y : Euc d => G1 (x - y) * F y) x
      rw [← this]
      simp only [sub_sub_cancel, hA1]
    have hm1 : Measurable (fun y : Euc d => G1 (x - y) * F y) :=
      (hG1.comp (measurable_const.sub measurable_id)).mul hF
    have hm2 : Measurable (fun y : Euc d => G2 (x - y) * F y) :=
      (hG2.comp (measurable_const.sub measurable_id)).mul hF
    have e2 : A2 x = ∫⁻ y, G2 (x - y) * F y := by
      simp only [hA2]
      exact lintegral_congr fun y => mul_comm _ _
    have hm3 : Measurable (fun y : Euc d => G3 (x - y) * F y) :=
      (hG3.comp (measurable_const.sub measurable_id)).mul hF
    calc ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * F y
        ≤ ∫⁻ y, (G1 (x - y) * F y + G2 (x - y) * F y + G3 (x - y) * F y) := by
          refine lintegral_mono fun y => ?_
          calc ENNReal.ofReal (‖x - y‖ ^ (-s)) * F y
              ≤ (G1 (x - y) + G2 (x - y) + G3 (x - y)) * F y := by
                gcongr; exact hsplit _
            _ = _ := by ring
      _ = (∫⁻ y, G1 (x - y) * F y) + (∫⁻ y, G2 (x - y) * F y) + ∫⁻ y, G3 (x - y) * F y := by
          have hm12 : Measurable (fun y : Euc d => G1 (x - y) * F y + G2 (x - y) * F y) :=
            hm1.add hm2
          rw [lintegral_add_left hm12, lintegral_add_left hm1]
      _ = A1 x + A2 x + A3 x := by rw [e1, e2]
  have hA3le : ∀ x, A3 x ≤ ∫⁻ y, F y := by
    intro x
    refine lintegral_mono fun y => ?_
    calc G3 (x - y) * F y ≤ 1 * F y := mul_le_mul_left (hG3le _) _
      _ = F y := one_mul _
  have hnu1 := (wr13c_lintegral_nu_le hρ hM (fun x => A1 x ^ 2) (hA1m.pow_const 2)).trans
    (mul_le_mul' (le_refl (ENNReal.ofReal M)) (HRS.Whole.Q34.young_L1_L2 G1 F hG1 hF))
  have hnu2 := (wr13c_lintegral_nu_le hρ hM (fun x => A2 x ^ 2) (hA2m.pow_const 2)).trans
    (mul_le_mul' (le_refl (ENNReal.ofReal M)) (HRS.Whole.Q34.young_L1_L2 F G2 hF hG2))
  have hnu3 : ∫⁻ x, A3 x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ (∫⁻ y, F y) ^ 2 := by
    calc ∫⁻ x, A3 x ^ 2 ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫⁻ x, (∫⁻ y, F y) ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
          lintegral_mono fun x => pow_le_pow_left' (hA3le x) 2
      _ = (∫⁻ y, F y) ^ 2 := by simp
  calc ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * F y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫⁻ x, 4 * (A1 x ^ 2 + A2 x ^ 2 + A3 x ^ 2) ∂(HRS.Whole.withDensityReal ρ) :=
        lintegral_mono fun x => (pow_le_pow_left' (hpt x) 2).trans (wr13c_add3_sq_le _ _ _)
    _ = 4 * (∫⁻ x, A1 x ^ 2 ∂(HRS.Whole.withDensityReal ρ) +
          ∫⁻ x, A2 x ^ 2 ∂(HRS.Whole.withDensityReal ρ) +
          ∫⁻ x, A3 x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
        have h12 : Measurable (fun x : Euc d => A1 x ^ 2 + A2 x ^ 2) :=
          (hA1m.pow_const 2).add (hA2m.pow_const 2)
        have h1 : Measurable (fun x : Euc d => A1 x ^ 2) := hA1m.pow_const 2
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left h12, lintegral_add_left h1]
    _ ≤ 4 * (ENNReal.ofReal M * ((∫⁻ w, G1 w) ^ 2 * (∫⁻ y, F y ^ 2)) +
          ENNReal.ofReal M * ((∫⁻ y, F y) ^ 2 * ∫⁻ w, G2 w ^ 2) + (∫⁻ y, F y) ^ 2) := by
        gcongr
    _ = _ := by rw [← mul_add]

/-- `‖f‖₁ ≤ ε` in `lintegral` form. -/
theorem wr13c_F_L1 {f : Euc d → ℝ} (hfi : Integrable f) {ε : ℝ} (hε : ∫ x, |f x| ≤ ε) :
    ∫⁻ y, ENNReal.ofReal |f y| ≤ ENNReal.ofReal ε := by
  rw [← ofReal_integral_eq_lintegral_ofReal hfi.abs
      (Filter.Eventually.of_forall fun y => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hε

/-- Moments of `F = |f|` from `|f| ≤ B`, `‖f‖₁ ≤ ε`. -/
theorem wr13c_F_facts {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hfi : Integrable f) {ε : ℝ} (hε : ∫ x, |f x| ≤ ε) :
    (∫⁻ y, ENNReal.ofReal |f y|) ≤ ENNReal.ofReal ε ∧
      ∫⁻ y, ENNReal.ofReal |f y| ^ 2 ≤ ENNReal.ofReal (B * ε) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hFm : Measurable (fun y => ENNReal.ofReal |f y|) := hf.abs.ennreal_ofReal
  have h1 := wr13c_F_L1 hfi hε
  refine ⟨h1, ?_⟩
  calc ∫⁻ y, ENNReal.ofReal |f y| ^ 2 ≤ ∫⁻ y, ENNReal.ofReal B * ENNReal.ofReal |f y| := by
        refine lintegral_mono fun y => ?_
        rw [pow_two]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hB y)) le_rfl
    _ = ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal |f y| := lintegral_const_mul _ hFm
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal ε := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (B * ε) := (ENNReal.ofReal_mul hB0).symm

/-- From a `lintegral` bound of the square of `g * |f|` to the Bochner form. -/
theorem wr13c_conv_finish {s : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {f : Euc d → ℝ} (hf : Measurable f) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2
        ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal K) :
    MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ K := by
  have hTm := HRS.Whole.Q34.measurable_conv (s := s) hf
  have hT2m : Measurable (fun x : Euc d => (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2) := hTm.pow_const 2
  have hpt : ∀ x : Euc d, ENNReal.ofReal ((∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2) ≤
      (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal |∫ y, ‖x - y‖ ^ (-s) * f y| ≤
        ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| := by
      have := enorm_integral_le_lintegral_enorm (μ := (volume : Measure (Euc d)))
        (fun y => ‖x - y‖ ^ (-s) * f y)
      rw [Real.enorm_eq_ofReal_abs] at this
      refine this.trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ENNReal.ofReal ((∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2)
        = ENNReal.ofReal |∫ y, ‖x - y‖ ^ (-s) * f y| ^ 2 := by
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ ≤ _ := pow_le_pow_left' h1 2
  obtain ⟨hI, hV⟩ := HRS.Whole.Q34.integrable_of_lintegral_le
    (μ := HRS.Whole.withDensityReal ρ) hT2m (fun x => sq_nonneg _) hK
    ((lintegral_mono hpt).trans h)
  exact ⟨(memLp_two_iff_integrable_sq hTm.aestronglyMeasurable).2 hI, hV⟩

/-- If `‖f‖₁ = 0` the convolution `g * f` vanishes identically. -/
theorem wr13c_conv_zero {s : ℝ} {f : Euc d → ℝ} (hfi : Integrable f) (hε : ∫ x, |f x| ≤ 0) :
    ∀ x : Euc d, ∫ y, ‖x - y‖ ^ (-s) * f y = 0 := by
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hz : ∫ y, |f y| = 0 := le_antisymm hε hint0
  have hae : (fun y => |f y|) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg _) hfi.abs).1 hz
  intro x
  have hae2 : (fun y => ‖x - y‖ ^ (-s) * f y) =ᵐ[volume] 0 := by
    filter_upwards [hae] with y hy
    have : f y = 0 := abs_eq_zero.1 hy
    simp [this]
  rw [integral_congr_ae hae2]
  simp

theorem wr13c_conv_trivial {s : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {f : Euc d → ℝ} (hfi : Integrable f) (hε : ∫ x, |f x| ≤ 0) :
    MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
      ∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ) = 0 := by
  have h0 := wr13c_conv_zero (s := s) hfi hε
  simp only [h0]
  refine ⟨MemLp.zero, ?_⟩
  simp

/-! #### Subcritical case `2s < d` -/

theorem wr13c_G2_sq_sub (hd : 1 ≤ d) {s : ℝ} (hsub : 2 * s < d) :
    ∫⁻ w, ((ball (0 : Euc d) 1).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s))) w) ^ 2 =
      ENNReal.ofReal (sphereArea d * (1 / ((d : ℝ) - 2 * s))) := by
  have : ∀ w : Euc d, ((ball (0 : Euc d) 1).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s))) w) ^ 2 =
      (ball (0 : Euc d) 1).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-(2 * s)))) w := by
    intro w
    by_cases hw : w ∈ ball (0 : Euc d) 1
    · simp only [indicator_of_mem hw]
      rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (norm_nonneg _) _), wr13c_sq_rpow]
    · simp [indicator_of_notMem hw]
  simp_rw [this]
  rw [lintegral_indicator measurableSet_ball, HRS.Whole.Q34.lintegral_ball_rpow hd one_pos hsub,
    Real.one_rpow, one_div]

theorem wr13c_conv_L2_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hsub : 2 * s < d)
    (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, Measurable f → Integrable f →
      ∀ ε : ℝ, ∫ x, |f x| ≤ ε →
        ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
          Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤ C * ε := by
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have h2 : 0 < (d : ℝ) - 2 * s := by linarith
  refine ⟨Real.sqrt (4 * (|M| * (sphereArea d * (1 / ((d : ℝ) - 2 * s))) + 1)), Real.sqrt_nonneg _, ?_⟩
  intro f hf hfi ε hε ρ hρ hM
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 ≤ ε := hint0.trans hε
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  rw [abs_of_nonneg hM0]
  set F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y| with hF
  have hFm : Measurable F := hf.abs.ennreal_ofReal
  have hF1 : ∫⁻ y, F y ≤ ENNReal.ofReal ε := wr13c_F_L1 hfi hε
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set G2 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) 1).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s)))
    with hG2
  set G3 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) 1)ᶜ.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s)))
    with hG3
  have hgm : Measurable (fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-s))) :=
    (measurable_norm.pow_const _).ennreal_ofReal
  have hG2m : Measurable G2 := hgm.indicator measurableSet_ball
  have hG3m : Measurable G3 := hgm.indicator measurableSet_ball.compl
  have hG3le : ∀ w, G3 w ≤ 1 := by
    intro w
    by_cases hw : w ∈ ball (0 : Euc d) 1
    · simp [hG3, hw]
    · have h1 : 1 ≤ ‖w‖ := by simpa using hw
      have : ‖w‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      have hw' : w ∈ (ball (0 : Euc d) 1)ᶜ := hw
      simp only [hG3, indicator_of_mem hw']
      simpa using ENNReal.ofReal_le_ofReal this
  have hsplit : ∀ w, ENNReal.ofReal (‖w‖ ^ (-s)) ≤ (fun _ : Euc d => (0 : ℝ≥0∞)) w + G2 w + G3 w := by
    intro w
    by_cases hw : w ∈ ball (0 : Euc d) 1
    · simp [hG2, hG3, hw]
    · have hw' : w ∈ (ball (0 : Euc d) 1)ᶜ := hw
      simp [hG2, hG3, hw, hw']
  have key := wr13c_conv_abstract hρ hM F hFm (fun _ => 0) G2 G3 measurable_const hG2m hG3m hG3le
    hsplit
  rw [wr13c_G2_sq_sub hd hsub] at key
  simp only [lintegral_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    zero_add] at key
  have hK : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2
      ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (ε ^ 2 * (4 * (M * (sphereArea d * (1 / ((d : ℝ) - 2 * s))) + 1))) := by
    refine key.trans ?_
    have hε2 : (∫⁻ y, F y) ^ 2 ≤ ENNReal.ofReal (ε ^ 2) := by
      calc (∫⁻ y, F y) ^ 2 ≤ ENNReal.ofReal ε ^ 2 := pow_le_pow_left' hF1 2
        _ = ENNReal.ofReal (ε ^ 2) := (ENNReal.ofReal_pow hε0 2).symm
    have hA0 : 0 ≤ sphereArea d * (1 / ((d : ℝ) - 2 * s)) := by positivity
    calc 4 * (ENNReal.ofReal M * ((∫⁻ y, F y) ^ 2 * ENNReal.ofReal (sphereArea d * (1 / ((d : ℝ) - 2 * s)))) +
          (∫⁻ y, F y) ^ 2)
        ≤ 4 * (ENNReal.ofReal M * (ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal (sphereArea d * (1 / ((d : ℝ) - 2 * s)))) +
          ENNReal.ofReal (ε ^ 2)) := by gcongr
      _ = ENNReal.ofReal (ε ^ 2 * (4 * (M * (sphereArea d * (1 / ((d : ℝ) - 2 * s))) + 1))) := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (sq_nonneg ε),
            ← ENNReal.ofReal_mul hM0,
            ← ENNReal.ofReal_add (by positivity) (sq_nonneg ε), ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
  obtain ⟨hmem, hint⟩ := wr13c_conv_finish hρ hf (by positivity) hK
  refine ⟨hmem, ?_⟩
  calc Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ))
      ≤ Real.sqrt (ε ^ 2 * (4 * (M * (sphereArea d * (1 / ((d : ℝ) - 2 * s))) + 1))) :=
        Real.sqrt_le_sqrt hint
    _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0, mul_comm]

/-! #### Three-zone estimate (`s ≥ d/2`) -/

theorem wr13c_three_zone (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {R : ℝ} (hR0 : 0 < R)
    (hR1 : R ≤ 1) {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    (hfi : Integrable f) {ε : ℝ} (hε : ∫ x, |f x| ≤ ε) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2
        ∂(HRS.Whole.withDensityReal ρ) ≤
      4 * (ENNReal.ofReal M * ((ENNReal.ofReal (sphereArea d * (R ^ ((d : ℝ) - s) / ((d : ℝ) - s)))) ^ 2 *
          ENNReal.ofReal (B * ε) +
        (ENNReal.ofReal ε) ^ 2 * ENNReal.ofReal (sphereArea d * ∫ t in R..1, t ^ ((d : ℝ) - 1 - 2 * s))) +
        (ENNReal.ofReal ε) ^ 2) := by
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  obtain ⟨hF1, hF2⟩ := wr13c_F_facts hf hB hfi hε
  set F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y| with hF
  have hFm : Measurable F := hf.abs.ennreal_ofReal
  have hgm : Measurable (fun w : Euc d => ENNReal.ofReal (‖w‖ ^ (-s))) :=
    (measurable_norm.pow_const _).ennreal_ofReal
  set S1 : Set (Euc d) := ball (0 : Euc d) R with hS1
  set S2 : Set (Euc d) := {w : Euc d | ‖w‖ ∈ Ico R 1} with hS2
  set S3 : Set (Euc d) := {w : Euc d | 1 ≤ ‖w‖} with hS3
  have hS1m : MeasurableSet S1 := measurableSet_ball
  have hS2m : MeasurableSet S2 := measurable_norm measurableSet_Ico
  have hS3m : MeasurableSet S3 := measurableSet_le measurable_const measurable_norm
  set G1 : Euc d → ℝ≥0∞ := S1.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s))) with hG1
  set G2 : Euc d → ℝ≥0∞ := S2.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s))) with hG2
  set G3 : Euc d → ℝ≥0∞ := S3.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s))) with hG3
  have hG1m : Measurable G1 := hgm.indicator hS1m
  have hG2m : Measurable G2 := hgm.indicator hS2m
  have hG3m : Measurable G3 := hgm.indicator hS3m
  have hG3le : ∀ w, G3 w ≤ 1 := by
    intro w
    by_cases hw : w ∈ S3
    · have h1 : 1 ≤ ‖w‖ := hw
      have : ‖w‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      simp only [hG3, indicator_of_mem hw]
      simpa using ENNReal.ofReal_le_ofReal this
    · simp [hG3, hw]
  have hsplit : ∀ w, ENNReal.ofReal (‖w‖ ^ (-s)) ≤ G1 w + G2 w + G3 w := by
    intro w
    by_cases h1 : ‖w‖ < R
    · have hw : w ∈ S1 := by simpa [hS1] using h1
      simp only [hG1, indicator_of_mem hw]
      exact le_self_add.trans le_self_add
    · by_cases h2 : ‖w‖ < 1
      · have hw : w ∈ S2 := ⟨not_lt.1 h1, h2⟩
        simp only [hG2, indicator_of_mem hw]
        exact le_add_self.trans le_self_add
      · have hw : w ∈ S3 := not_lt.1 h2
        simp only [hG3, indicator_of_mem hw]
        exact le_add_self
  have key := wr13c_conv_abstract hρ hM F hFm G1 G2 G3 hG1m hG2m hG3m hG3le hsplit
  have hI1 : ∫⁻ w, G1 w = ENNReal.ofReal (sphereArea d * (R ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
    rw [hG1, lintegral_indicator hS1m, HRS.Whole.Q34.lintegral_ball_rpow hd hR0 hsd]
  have hI2 : ∫⁻ w, G2 w ^ 2 =
      ENNReal.ofReal (sphereArea d * ∫ t in R..1, t ^ ((d : ℝ) - 1 - 2 * s)) := by
    have : ∀ w : Euc d, G2 w ^ 2 = S2.indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-(2 * s)))) w := by
      intro w
      by_cases hw : w ∈ S2
      · simp only [hG2, indicator_of_mem hw]
        rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (norm_nonneg _) _), wr13c_sq_rpow]
      · simp [hG2, indicator_of_notMem hw]
    simp_rw [this]
    rw [lintegral_indicator hS2m]
    exact wr3_lintegral_annulus hd hR0 hR1
  rw [hI1, hI2] at key
  refine key.trans ?_
  gcongr

theorem wr13c_ofReal_expr {M a b c e : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) :
    4 * (ENNReal.ofReal M * (ENNReal.ofReal a ^ 2 * ENNReal.ofReal b +
      ENNReal.ofReal e ^ 2 * ENNReal.ofReal c) + ENNReal.ofReal e ^ 2) =
      ENNReal.ofReal (4 * (M * (a ^ 2 * b + e ^ 2 * c) + e ^ 2)) := by
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow he,
    ← ENNReal.ofReal_mul (sq_nonneg a), ← ENNReal.ofReal_mul (sq_nonneg e),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hM,
    ← ENNReal.ofReal_add (by positivity) (sq_nonneg e), ← ENNReal.ofReal_mul (by norm_num)]

theorem wr13c_log_e_div {ε : ℝ} (hε : 0 < ε) : Real.log (Real.exp 1 / ε) = 1 - Real.log ε := by
  rw [Real.log_div (Real.exp_pos 1).ne' hε.ne', Real.log_exp]

/-! #### Critical case `2s = d` -/

theorem wr13c_conv_L2_crit (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hcrit : 2 * s = d)
    (B M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
          Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
            C * (ε * Real.sqrt (Real.log (Real.exp 1 / ε))) := by
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set A : ℝ := sphereArea d with hA
  refine ⟨Real.sqrt (4 * (|M| * (A / ((d : ℝ) - s)) ^ 2 * |B| + |M| * (A / d) + 1)),
    Real.sqrt_nonneg _, ?_⟩
  intro f hf hB hfi ε hε1 hε ρ hρ hM
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 ≤ ε := hint0.trans hε
  rw [abs_of_nonneg hM0, abs_of_nonneg hB0]
  rcases hε0.eq_or_lt with hε' | hεpos
  · subst hε'
    obtain ⟨hm, hz⟩ := wr13c_conv_trivial hρ hfi hε
    refine ⟨hm, ?_⟩
    rw [hz]; simp
  have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε0 hε1
  set R : ℝ := ε ^ (1 / (d : ℝ)) with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hεpos _
  have hR1 : R ≤ 1 := Real.rpow_le_one hε0 hε1 (by positivity)
  have hRd : R ^ (d : ℝ) = ε := by
    rw [hR, ← Real.rpow_mul hεpos.le]
    have : 1 / (d : ℝ) * d = 1 := by field_simp
    rw [this, Real.rpow_one]
  have h2 : (R ^ ((d : ℝ) - s)) ^ 2 = ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    have : ((d : ℝ) - s) * ((2 : ℕ) : ℝ) = d := by push_cast; linarith
    rw [this, hRd]
  have hlogR : Real.log R = 1 / (d : ℝ) * Real.log ε := by
    rw [hR, Real.log_rpow hεpos]
  have hex : (d : ℝ) - 1 - 2 * s = -1 := by linarith
  have hint : ∫ t in R..1, t ^ ((d : ℝ) - 1 - 2 * s) = -(1 / (d : ℝ) * Real.log ε) := by
    rw [hex]
    simp only [Real.rpow_neg_one]
    rw [integral_inv_of_pos hR0 one_pos, one_div R, Real.log_inv, hlogR]
  have hz := wr13c_three_zone hd hs0 hsd hR0 hR1 hf hB hfi hε hρ hM
  rw [hint] at hz
  have hc0 : 0 ≤ A * -(1 / (d : ℝ) * Real.log ε) := by
    have : 0 ≤ -(1 / (d : ℝ) * Real.log ε) := by
      have : 0 ≤ 1 / (d : ℝ) * -Real.log ε := mul_nonneg (by positivity) (by linarith)
      linarith
    positivity
  have ha0 : 0 ≤ A * (R ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
    have := Real.rpow_nonneg hR0.le ((d : ℝ) - s)
    positivity
  rw [wr13c_ofReal_expr hM0 ha0 (mul_nonneg hB0 hε0) hc0 hε0] at hz
  -- the real bound
  set L : ℝ := 1 - Real.log ε with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  set C2 : ℝ := 4 * (M * (A / ((d : ℝ) - s)) ^ 2 * B + M * (A / d) + 1) with hC2
  have hC20 : 0 ≤ C2 := by positivity
  have hKle : 4 * (M * ((A * (R ^ ((d : ℝ) - s) / ((d : ℝ) - s))) ^ 2 * (B * ε) +
      ε ^ 2 * (A * -(1 / (d : ℝ) * Real.log ε))) + ε ^ 2) ≤ ε ^ 2 * (C2 * L) := by
    have e1 : (A * (R ^ ((d : ℝ) - s) / ((d : ℝ) - s))) ^ 2 * (B * ε) =
        (A / ((d : ℝ) - s)) ^ 2 * B * ε ^ 2 := by
      rw [mul_pow, div_pow, h2]
      field_simp
    rw [e1]
    have hnl : 0 ≤ -Real.log ε := by linarith
    have e2 : ε ^ 2 * (A * -(1 / (d : ℝ) * Real.log ε)) = ε ^ 2 * (A / d * -Real.log ε) := by
      ring
    rw [e2]
    have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
    have hP : 0 ≤ M * (A / ((d : ℝ) - s)) ^ 2 * B := by positivity
    have hQ : 0 ≤ M * (A / d) := by positivity
    have : 4 * (M * ((A / ((d : ℝ) - s)) ^ 2 * B * ε ^ 2 + ε ^ 2 * (A / d * -Real.log ε)) + ε ^ 2) =
        ε ^ 2 * (4 * (M * (A / ((d : ℝ) - s)) ^ 2 * B + M * (A / d) * -Real.log ε + 1)) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hε2
    rw [hC2]
    have : M * (A / d) * -Real.log ε ≤ M * (A / d) * L := mul_le_mul_of_nonneg_left (by rw [hL]; linarith) hQ
    nlinarith [mul_nonneg hP (sub_nonneg.2 hL1)]
  have hK : ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2
      ∂(HRS.Whole.withDensityReal ρ) ≤ ENNReal.ofReal (ε ^ 2 * (C2 * L)) :=
    hz.trans (ENNReal.ofReal_le_ofReal hKle)
  obtain ⟨hmem, hint2⟩ := wr13c_conv_finish hρ hf (by positivity) hK
  refine ⟨hmem, ?_⟩
  rw [wr13c_log_e_div hεpos, ← hL]
  calc Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ))
      ≤ Real.sqrt (ε ^ 2 * (C2 * L)) := Real.sqrt_le_sqrt hint2
    _ = Real.sqrt C2 * (ε * Real.sqrt L) := by
        rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε0, Real.sqrt_mul hC20]
        ring

/-! #### Supercritical case `d < 2s` (`Q34.l2_bound`) and the unified statement -/

theorem wr13c_conv_L2_super (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hsup : (d : ℝ) < 2 * s)
    (B M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
          Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
            C * ε ^ (3 / 2 - s / d) := by
  obtain ⟨C, hC⟩ := HRS.Whole.Q34.l2_bound hd hs0 hsd hsup B M
  refine ⟨max C 0, le_max_right _ _, fun f hf hB hfi ε hε1 hε ρ hρ hM => ?_⟩
  obtain ⟨hm, hb⟩ := hC f hf hB hfi ε hε1 hε ρ hρ hM
  refine ⟨hm, hb.trans ?_⟩
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hint0.trans hε) _)

/-- The three-case rate `ε | ε √log(e/ε) | ε^{3/2-s/d}` of the `L²(μ)` convolution estimate. -/
def wr13c_convRate (d : ℕ) (s ε : ℝ) : ℝ :=
  if 2 * s < d then ε
  else if 2 * s = d then ε * Real.sqrt (Real.log (Real.exp 1 / ε))
  else ε ^ (3 / 2 - s / d)

/-- **`L²(μ)` convolution estimate** (`conv_L2_E`, TeX `W:eq:euc-convolution-L2`): for
`|f| ≤ B`, `‖f‖₁ ≤ ε ≤ 1`, `‖g * f‖_{L²(μ)} ≤ C · wr13c_convRate d s ε`, uniformly in `ρ ≤ M`. -/
theorem wr13c_conv_L2_E (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (B M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
          Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
            C * wr13c_convRate d s ε := by
  by_cases h1 : 2 * s < d
  · obtain ⟨C, hC0, hC⟩ := wr13c_conv_L2_sub hd hs0 hsd h1 M
    refine ⟨C, hC0, fun f hf hB hfi ε hε1 hε ρ hρ hM => ?_⟩
    unfold wr13c_convRate
    rw [if_pos h1]
    exact hC f hf hfi ε hε ρ hρ hM
  · by_cases hc : 2 * s = d
    · obtain ⟨C, hC0, hC⟩ := wr13c_conv_L2_crit hd hs0 hsd hc B M
      refine ⟨C, hC0, fun f hf hB hfi ε hε1 hε ρ hρ hM => ?_⟩
      unfold wr13c_convRate
      rw [if_neg h1, if_pos hc]
      exact hC f hf hB hfi ε hε1 hε ρ hρ hM
    · have hsup : (d : ℝ) < 2 * s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hc)
      obtain ⟨C, hC0, hC⟩ := wr13c_conv_L2_super hd hs0 hsd hsup B M
      refine ⟨C, hC0, fun f hf hB hfi ε hε1 hε ρ hρ hM => ?_⟩
      unfold wr13c_convRate
      rw [if_neg h1, if_neg hc]
      exact hC f hf hB hfi ε hε1 hε ρ hρ hM

/-! ### 3. The `δ_N` forms -/

theorem wr13c_deltaN_sub {s : ℝ} (h : 2 * s < d) (N : ℕ) : deltaN d s N = (N : ℝ)⁻¹ := by
  unfold deltaN; rw [if_pos (by linarith)]

theorem wr13c_deltaN_crit {s : ℝ} (h : 2 * s = d) {N : ℕ} (hN : 1 ≤ N) :
    deltaN d s N = (N : ℝ)⁻¹ * (1 + Real.log N) := by
  have h1 : ¬ s < (d : ℝ) / 2 := by linarith
  have h2 : s = (d : ℝ) / 2 := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold deltaN
  rw [if_neg h1, if_pos h2, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]

theorem wr13c_deltaN_super {s : ℝ} (h : (d : ℝ) < 2 * s) (N : ℕ) :
    deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := by
  have h1 : ¬ s < (d : ℝ) / 2 := by linarith
  have h2 : ¬ s = (d : ℝ) / 2 := by intro hh; linarith
  unfold deltaN
  rw [if_neg h1, if_neg h2]

theorem wr13c_sqrt_inv_mul {x L : ℝ} (hx : 0 < x) (hL : 0 ≤ L) :
    Real.sqrt (x⁻¹ * L / x) = x⁻¹ * Real.sqrt L := by
  rw [show x⁻¹ * L / x = (x⁻¹) ^ 2 * L by field_simp, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity)]

/-- **`δ_N`-form of `conv_L2_E`**: if `|f| ≤ B` and `‖f‖₁ ≤ K0 √(δ_N/N)` with `N ≥ N0`, then
`‖g * f‖_{L²(μ)} ≤ C δ_N`, `δ_N = deltaN d s N`, uniformly in `ρ ≤ M`. -/
theorem wr13c_conv_L2_delta (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (B M K0 : ℝ) :
    ∃ C : ℝ, ∃ N0 : ℕ, 0 ≤ C ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
        ∫ x, |f x| ≤ K0 * Real.sqrt (deltaN d s N / N) →
        ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (HRS.Whole.withDensityReal ρ) ∧
          Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ≤
            C * deltaN d s N := by
  set K1 : ℝ := max K0 1 with hK1
  have hK1one : 1 ≤ K1 := le_max_right _ _
  have hK10 : 0 < K1 := by linarith
  have hK0K1 : K0 ≤ K1 := le_max_left _ _
  set N0 : ℕ := ⌈K1 ^ 2⌉₊ + 1 with hN0
  have hNK : ∀ N : ℕ, N0 ≤ N → K1 ^ 2 ≤ N ∧ (1 : ℝ) ≤ N := by
    intro N hN
    have h1 : K1 ^ 2 ≤ ⌈K1 ^ 2⌉₊ := Nat.le_ceil _
    have h2 : (⌈K1 ^ 2⌉₊ + 1 : ℕ) ≤ N := hN
    have h3 : ((⌈K1 ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
    push_cast at h3
    refine ⟨by linarith, ?_⟩
    have : (0 : ℝ) ≤ ⌈K1 ^ 2⌉₊ := Nat.cast_nonneg _
    linarith
  by_cases h1 : 2 * s < d
  · obtain ⟨C1, hC10, hC1⟩ := wr13c_conv_L2_sub hd hs0 hsd h1 M
    refine ⟨C1 * K1, N0, by positivity, fun N hN f hf hB hfi hεf ρ hρ hM => ?_⟩
    obtain ⟨hN2, hN1⟩ := hNK N hN
    have hN0' : (0 : ℝ) < N := by linarith
    have hδ := wr13c_deltaN_sub (d := d) h1 N
    have hsq : Real.sqrt (deltaN d s N / N) = (N : ℝ)⁻¹ := by
      rw [hδ]
      have := wr13c_sqrt_inv_mul (x := (N : ℝ)) (L := 1) hN0' zero_le_one
      simpa using this
    rw [hsq] at hεf
    have hεK : ∫ x, |f x| ≤ K1 * (N : ℝ)⁻¹ :=
      hεf.trans (mul_le_mul_of_nonneg_right hK0K1 (by positivity))
    obtain ⟨hm, hb⟩ := hC1 f hf hfi _ hεK ρ hρ hM
    refine ⟨hm, hb.trans (le_of_eq ?_)⟩
    rw [hδ]; ring
  · by_cases hc : 2 * s = d
    · obtain ⟨C1, hC10, hC1⟩ := wr13c_conv_L2_crit hd hs0 hsd hc B M
      refine ⟨C1 * K1, N0, by positivity, fun N hN f hf hB hfi hεf ρ hρ hM => ?_⟩
      obtain ⟨hN2, hN1⟩ := hNK N hN
      have hN0' : (0 : ℝ) < N := by linarith
      have hNn : 1 ≤ N := by exact_mod_cast hN1
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
      set L : ℝ := 1 + Real.log N with hL
      have hL1 : 1 ≤ L := by rw [hL]; linarith
      have hδ := wr13c_deltaN_crit (d := d) hc hNn
      have hsq : Real.sqrt (deltaN d s N / N) = (N : ℝ)⁻¹ * Real.sqrt L := by
        rw [hδ]; exact wr13c_sqrt_inv_mul hN0' (by linarith)
      rw [hsq] at hεf
      have hsL : 1 ≤ Real.sqrt L := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1
      set ε : ℝ := K1 * ((N : ℝ)⁻¹ * Real.sqrt L) with hε
      have hεpos : 0 < ε := by positivity
      have hεK : ∫ x, |f x| ≤ ε :=
        hεf.trans (mul_le_mul_of_nonneg_right hK0K1 (by positivity))
      have hε1 : ε ≤ 1 := by
        have h1' : ε = Real.sqrt (K1 ^ 2 * (deltaN d s N / N)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK10.le, hsq]
        have hδ1 : deltaN d s N ≤ 1 := by
          rw [hδ]
          have := Real.log_le_sub_one_of_pos hN0'
          rw [inv_mul_le_iff₀ hN0']; linarith
        rw [h1']
        rw [Real.sqrt_le_one]
        calc K1 ^ 2 * (deltaN d s N / N) ≤ K1 ^ 2 * (1 / N) := by gcongr
          _ ≤ 1 := by rw [mul_one_div, div_le_one hN0']; exact hN2
      obtain ⟨hm, hb⟩ := hC1 f hf hB hfi ε hε1 hεK ρ hρ hM
      refine ⟨hm, hb.trans ?_⟩
      -- `log (e/ε) ≤ L`
      have hlogε : -Real.log N ≤ Real.log ε := by
        rw [← Real.log_inv]
        refine Real.log_le_log (by positivity) ?_
        calc (N : ℝ)⁻¹ = 1 * ((N : ℝ)⁻¹ * 1) := by ring
          _ ≤ K1 * ((N : ℝ)⁻¹ * Real.sqrt L) := by gcongr
      have hlog : Real.log (Real.exp 1 / ε) ≤ L := by
        rw [wr13c_log_e_div hεpos, hL]; linarith
      have hsqrt : Real.sqrt (Real.log (Real.exp 1 / ε)) ≤ Real.sqrt L := Real.sqrt_le_sqrt hlog
      have hsL2 : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
      rw [hδ]
      calc C1 * (ε * Real.sqrt (Real.log (Real.exp 1 / ε))) ≤ C1 * (ε * Real.sqrt L) := by gcongr
        _ = C1 * K1 * ((N : ℝ)⁻¹ * (Real.sqrt L * Real.sqrt L)) := by rw [hε]; ring
        _ = C1 * K1 * ((N : ℝ)⁻¹ * (1 + Real.log N)) := by rw [hsL2]
    · have hsup : (d : ℝ) < 2 * s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hc)
      obtain ⟨C1, hC10, hC1⟩ := wr13c_conv_L2_super hd hs0 hsd hsup B M
      set p : ℝ := (d : ℝ) / s with hp
      have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hs0]; linarith
      have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hs0]; linarith
      set q : ℝ := 3 / 2 - s / d with hq
      have hq0 : 0 ≤ q := by
        have : s / (d : ℝ) < 1 := by
          rw [div_lt_one (by exact_mod_cast hd)]; exact hsd
        rw [hq]; linarith
      refine ⟨C1 * K1 ^ q, N0, by positivity, fun N hN f hf hB hfi hεf ρ hρ hM => ?_⟩
      obtain ⟨hN2, hN1⟩ := hNK N hN
      have hN0' : (0 : ℝ) < N := by linarith
      have hδ := wr13c_deltaN_super (d := d) hsup N
      have hsq : Real.sqrt (deltaN d s N / N) = (N : ℝ) ^ (-p / 2) := by
        have : deltaN d s N / N = ((N : ℝ) ^ (-p / 2)) ^ 2 := by
          rw [hδ, ← hp, ← Real.rpow_natCast, ← Real.rpow_mul hN0'.le,
            show (1 - p) = (-p) + 1 by ring, Real.rpow_add hN0', Real.rpow_one]
          have : (-p / 2) * ((2 : ℕ) : ℝ) = -p := by push_cast; ring
          rw [this]; field_simp
        rw [this, Real.sqrt_sq (by positivity)]
      rw [hsq] at hεf
      set ε : ℝ := K1 * (N : ℝ) ^ (-p / 2) with hε
      have hεpos : 0 < ε := by positivity
      have hεK : ∫ x, |f x| ≤ ε :=
        hεf.trans (mul_le_mul_of_nonneg_right hK0K1 (by positivity))
      have hε1 : ε ≤ 1 := by
        have h1' : ε = Real.sqrt (K1 ^ 2 * (deltaN d s N / N)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK10.le, hsq]
        have hδ1 : deltaN d s N ≤ 1 := by
          rw [hδ, ← hp]
          exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
        have hδ0 : 0 ≤ deltaN d s N := by rw [hδ]; positivity
        rw [h1', Real.sqrt_le_one]
        calc K1 ^ 2 * (deltaN d s N / N) ≤ K1 ^ 2 * (1 / N) := by gcongr
          _ ≤ 1 := by rw [mul_one_div, div_le_one hN0']; exact hN2
      obtain ⟨hm, hb⟩ := hC1 f hf hB hfi ε hε1 hεK ρ hρ hM
      refine ⟨hm, hb.trans ?_⟩
      have hεq : ε ^ q = K1 ^ q * (N : ℝ) ^ (-p / 2 * q) := by
        rw [hε, Real.mul_rpow hK10.le (by positivity), ← Real.rpow_mul hN0'.le]
      have hexp : -p / 2 * q = -(3 * p / 4 - 1 / 2) := by
        rw [hq, hp]
        have hs' : s ≠ 0 := hs0.ne'
        have hd' : (d : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      have hmono : (N : ℝ) ^ (-p / 2 * q) ≤ (N : ℝ) ^ (1 - p) := by
        refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
        rw [hexp]; linarith
      rw [hδ, ← hp, hεq]
      calc C1 * (K1 ^ q * (N : ℝ) ^ (-p / 2 * q)) ≤ C1 * (K1 ^ q * (N : ℝ) ^ (1 - p)) := by gcongr
        _ = C1 * K1 ^ q * (N : ℝ) ^ (1 - p) := by ring

theorem wr13c_deltaN_pos_le_one (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {N : ℕ}
    (hN : 1 ≤ N) : 0 < deltaN d s N ∧ deltaN d s N ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases h1 : 2 * s < d
  · rw [wr13c_deltaN_sub h1]
    exact ⟨by positivity, inv_le_one_of_one_le₀ hN1⟩
  · by_cases hc : 2 * s = d
    · rw [wr13c_deltaN_crit hc hN]
      have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
      refine ⟨by positivity, ?_⟩
      have := Real.log_le_sub_one_of_pos hN0
      rw [inv_mul_le_iff₀ hN0]; linarith
    · have hsup : (d : ℝ) < 2 * s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hc)
      rw [wr13c_deltaN_super hsup]
      have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
      exact ⟨by positivity, Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)⟩

/-! ### 4. Sup bound for `g * f` -/

/-- **Sup bound** (`Q34.sup_bound`, restated with `rieszKernel`): `|g * f(x)| ≤ C ε^{1-s/d}` for all `x`,
with integrability of `y ↦ g(x-y) f(y)`; independent of `ρ`. -/
theorem wr13c_sup_conv_small (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        (∀ x, Integrable (fun y => HRS.Whole.rieszKernel d s (x - y) * f y)) ∧
        ∀ x, |∫ y, HRS.Whole.rieszKernel d s (x - y) * f y| ≤ C * ε ^ (1 - s / d) := by
  obtain ⟨C, hC⟩ := HRS.Whole.Q34.sup_bound hd hs0 hsd B
  refine ⟨max C 0, le_max_right _ _, fun f hf hB hfi ε hε1 hε => ?_⟩
  obtain ⟨hI, hb⟩ := hC f hf hB hfi ε hε1 hε
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hE : 0 ≤ ε ^ (1 - s / d) := Real.rpow_nonneg (hint0.trans hε) _
  simp_rw [HRS.Whole.Q34.rieszKernel_eq hs0.ne']
  exact ⟨hI, fun x => (hb x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE)⟩

/-- `δ_N`-form of the sup bound: for `‖f‖₁ ≤ K0 √(δ_N/N)`, `N ≥ N0`,
`‖g * f‖_∞ ≤ C (√(δ_N/N))^{1-s/d} ≤ C N^{-(1-s/d)/2}`. -/
theorem wr13c_sup_conv_delta (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (B K0 : ℝ) :
    ∃ C : ℝ, ∃ N0 : ℕ, 0 ≤ C ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
        ∫ x, |f x| ≤ K0 * Real.sqrt (deltaN d s N / N) →
        (∀ x, Integrable (fun y => HRS.Whole.rieszKernel d s (x - y) * f y)) ∧
        (∀ x, |∫ y, HRS.Whole.rieszKernel d s (x - y) * f y| ≤
          C * Real.sqrt (deltaN d s N / N) ^ (1 - s / d)) ∧
        ∀ x, |∫ y, HRS.Whole.rieszKernel d s (x - y) * f y| ≤
          C * (N : ℝ) ^ (-(1 - s / d) / 2) := by
  obtain ⟨C1, hC10, hC1⟩ := wr13c_sup_conv_small hd hs0 hsd B
  set K1 : ℝ := max K0 1 with hK1
  have hK1one : 1 ≤ K1 := le_max_right _ _
  have hK10 : 0 < K1 := by linarith
  have hK0K1 : K0 ≤ K1 := le_max_left _ _
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hexp : 0 ≤ 1 - s / (d : ℝ) := by
    have : s / (d : ℝ) < 1 := by rw [div_lt_one hdpos]; exact hsd
    linarith
  refine ⟨C1 * K1 ^ (1 - s / d), ⌈K1 ^ 2⌉₊ + 1, by positivity, fun N hN f hf hB hfi hεf => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have h2 : (⌈K1 ^ 2⌉₊ + 1 : ℕ) ≤ N := hN
    have h3 : ((⌈K1 ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
    push_cast at h3
    have : (0 : ℝ) ≤ ⌈K1 ^ 2⌉₊ := Nat.cast_nonneg _
    linarith
  have hN2 : K1 ^ 2 ≤ N := by
    have h1 : K1 ^ 2 ≤ ⌈K1 ^ 2⌉₊ := Nat.le_ceil _
    have h2 : (⌈K1 ^ 2⌉₊ + 1 : ℕ) ≤ N := hN
    have h3 : ((⌈K1 ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h2
    push_cast at h3
    linarith
  have hN0' : (0 : ℝ) < N := by linarith
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  obtain ⟨hδ0, hδ1⟩ := wr13c_deltaN_pos_le_one hd hs0 hsd hNn
  set r : ℝ := Real.sqrt (deltaN d s N / N) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hε1 : K1 * r ≤ 1 := by
    have h1' : K1 * r = Real.sqrt (K1 ^ 2 * (deltaN d s N / N)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK10.le]
    rw [h1', Real.sqrt_le_one]
    calc K1 ^ 2 * (deltaN d s N / N) ≤ K1 ^ 2 * (1 / N) := by gcongr
      _ ≤ 1 := by rw [mul_one_div, div_le_one hN0']; exact hN2
  have hεK : ∫ x, |f x| ≤ K1 * r := hεf.trans (mul_le_mul_of_nonneg_right hK0K1 hr0)
  obtain ⟨hI, hb⟩ := hC1 f hf hB hfi (K1 * r) hε1 hεK
  refine ⟨hI, fun x => ?_, fun x => ?_⟩
  · refine (hb x).trans (le_of_eq ?_)
    rw [Real.mul_rpow hK10.le hr0]; ring
  · refine (hb x).trans ?_
    rw [Real.mul_rpow hK10.le hr0]
    have hr_le : r ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := by
      have : r = Real.sqrt (deltaN d s N / N) := hr
      have hq : (N : ℝ) ^ (-(1 : ℝ) / 2) = Real.sqrt ((1 : ℝ) / N) := by
        rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow hN0'.le, ← Real.rpow_neg hN0'.le]
        congr 1; ring
      rw [this, hq]
      exact Real.sqrt_le_sqrt (by gcongr)
    have : r ^ (1 - s / d) ≤ ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ (1 - s / d) :=
      Real.rpow_le_rpow hr0 hr_le hexp
    have e : ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ (1 - s / d) = (N : ℝ) ^ (-(1 - s / d) / 2) := by
      rw [← Real.rpow_mul hN0'.le]; congr 1; ring
    rw [e] at this
    calc C1 * (K1 ^ (1 - s / d) * r ^ (1 - s / d)) =
        C1 * K1 ^ (1 - s / d) * r ^ (1 - s / d) := by ring
      _ ≤ C1 * K1 ^ (1 - s / d) * (N : ℝ) ^ (-(1 - s / d) / 2) := by gcongr

/-- The sup bound of `g * f` tends to `0` uniformly (`‖z_N‖_∞ → 0` input): for every `η > 0` there is `N1`
such that for `N ≥ N1`, `‖f‖₁ ≤ K0 √(δ_N/N)`, `|f| ≤ B` imply `‖g * f‖_∞ ≤ η`. -/
theorem wr13c_sup_conv_eventually_small (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (B K0 : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ N1 : ℕ, ∀ N : ℕ, N1 ≤ N →
      ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
        ∫ x, |f x| ≤ K0 * Real.sqrt (deltaN d s N / N) →
        ∀ x, |∫ y, HRS.Whole.rieszKernel d s (x - y) * f y| ≤ η := by
  obtain ⟨C, N0, hC0, hC⟩ := wr13c_sup_conv_delta hd hs0 hsd B K0
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < (1 - s / (d : ℝ)) / 2 := by
    have : s / (d : ℝ) < 1 := by rw [div_lt_one hdpos]; exact hsd
    linarith
  have ht : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-((1 - s / (d : ℝ)) / 2))) atTop (nhds 0) := by
    have := ((tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa using this
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds hη))
  refine ⟨max N0 N2, fun N hN f hf hB hfi hεf x => ?_⟩
  obtain ⟨-, -, hb⟩ := hC N (le_trans (le_max_left _ _) hN) f hf hB hfi hεf
  refine (hb x).trans ?_
  have := hN2 N (le_trans (le_max_right _ _) hN)
  have e : -((1 - s / (d : ℝ)) / 2) = -(1 - s / (d : ℝ)) / 2 := by ring
  rw [e] at this
  exact this.le

/-! ### 5. Schur test for kernels bounded by `B (1 + W_s)` -/

/-- **Schur test** (`lintegral` form): for `|h(x,y)| ≤ B (1 + rieszWeight s (x-y))` off the diagonal,
`‖∫ |h(·,y)| F(y) dμ(y)‖_{L²(μ)} ≤ C B ‖F‖_{L²(μ)}`, with `C` depending only on `(d, s, M)`
(row bound `wr3_lintegral_W_row`).  Here `0 ≤ s < d`. -/
theorem wr13c_schur_W (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ B : ℝ, 0 ≤ B → ∀ h : Euc d → Euc d → ℝ,
        Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
        (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
        ∀ F : Euc d → ℝ≥0∞, Measurable F →
          ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * F y ∂(HRS.Whole.withDensityReal ρ)) ^ 2
              ∂(HRS.Whole.withDensityReal ρ) ≤
            ENNReal.ofReal (C * B) ^ 2 * ∫⁻ y, F y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hσd := HRS.WeakRef.sigmaOf_lt hd hsd
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdσ : 0 < (d : ℝ) - HRS.WeakRef.sigmaOf d s := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set Wr : ℝ := 1 + (1 + 4 / (d : ℝ)) *
    (|M| * sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) + 1) with hWr
  have hWr0 : 0 ≤ Wr := by rw [hWr]; positivity
  refine ⟨Wr, hWr0, fun ρ hρ hM B hB h hhm hbd F hF => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hM' : ∀ x, ρ x ≤ |M| := fun x => (hM x).trans (le_abs_self M)
  have hrow : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂ν ≤
      ENNReal.ofReal Wr := fun x => wr3_lintegral_W_row hd hs0 hsd hρ hM' x
  have hWm : Measurable (fun p : Euc d × Euc d =>
      ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (p.1 - p.2))) :=
    (measurable_const.add ((wr3_measurable_rieszWeight s).comp
      (measurable_fst.sub measurable_snd))).ennreal_ofReal
  have hWx : ∀ x : Euc d, Measurable (fun y : Euc d =>
      ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))) := fun x =>
    (measurable_const.add ((wr3_measurable_rieszWeight s).comp
      (measurable_const.sub measurable_id))).ennreal_ofReal
  -- the majorant kernel
  set K : Euc d → Euc d → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal B * ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) with hK
  have hKm : Measurable (fun p : Euc d × Euc d => K p.1 p.2) := measurable_const.mul hWm
  have hKx : ∀ x : Euc d, Measurable (K x) := fun x => measurable_const.mul (hWx x)
  have hKrow : ∀ x : Euc d, ∫⁻ y, K x y ∂ν ≤ ENNReal.ofReal B * ENNReal.ofReal Wr := by
    intro x
    simp only [hK]
    rw [lintegral_const_mul _ (hWx x)]
    exact mul_le_mul' le_rfl (hrow x)
  have hKcol : ∀ y : Euc d, ∫⁻ x, K x y ∂ν ≤ ENNReal.ofReal B * ENNReal.ofReal Wr := by
    intro y
    simp only [hK]
    have hm : Measurable (fun x : Euc d =>
        ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))) :=
      (measurable_const.add ((wr3_measurable_rieszWeight s).comp
        (measurable_id.sub measurable_const))).ennreal_ofReal
    rw [lintegral_const_mul _ hm]
    refine mul_le_mul' le_rfl ?_
    have e : ∀ x : Euc d, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) =
        ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (y - x)) := by
      intro x
      unfold HRS.Whole.rieszWeight
      rw [norm_sub_rev x y]
    simp_rw [e]
    exact hrow y
  -- pointwise domination `|h| ≤ K` a.e.
  have hdom : ∀ x : Euc d, ∀ᵐ y ∂ν, ENNReal.ofReal |h x y| ≤ K x y := by
    intro x
    filter_upwards [wr3_ae_ne hd ρ x] with y hy
    have := hbd x y (Ne.symm hy)
    simp only [hK]
    rw [← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal this
  have h1 : ∀ x : Euc d, (∫⁻ y, ENNReal.ofReal |h x y| * F y ∂ν) ^ 2 ≤
      (ENNReal.ofReal B * ENNReal.ofReal Wr) * ∫⁻ y, K x y * F y ^ 2 ∂ν := by
    intro x
    have hle : ∫⁻ y, ENNReal.ofReal |h x y| * F y ∂ν ≤ ∫⁻ y, K x y * F y ∂ν :=
      lintegral_mono_ae (by filter_upwards [hdom x] with y hy using mul_le_mul_left hy _)
    calc (∫⁻ y, ENNReal.ofReal |h x y| * F y ∂ν) ^ 2 ≤ (∫⁻ y, K x y * F y ∂ν) ^ 2 :=
          pow_le_pow_left' hle 2
      _ ≤ (∫⁻ y, K x y ∂ν) * ∫⁻ y, K x y * F y ^ 2 ∂ν :=
          HRS.Whole.Q34.weighted_cs ν (K x) F (hKx x) hF
      _ ≤ _ := mul_le_mul' (hKrow x) le_rfl
  have hjoint : Measurable (fun p : Euc d × Euc d => K p.1 p.2 * F p.2 ^ 2) :=
    hKm.mul ((hF.comp measurable_snd).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, ENNReal.ofReal |h x y| * F y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal B * ENNReal.ofReal Wr) * ∫⁻ y, K x y * F y ^ 2 ∂ν ∂ν :=
        lintegral_mono h1
    _ = (ENNReal.ofReal B * ENNReal.ofReal Wr) * ∫⁻ x, ∫⁻ y, K x y * F y ^ 2 ∂ν ∂ν := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d => K p.1 p.2 * F p.2 ^ 2)
          hjoint
    _ = (ENNReal.ofReal B * ENNReal.ofReal Wr) * ∫⁻ y, ∫⁻ x, K x y * F y ^ 2 ∂ν ∂ν := by
        congr 1
        exact lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ (ENNReal.ofReal B * ENNReal.ofReal Wr) *
          ∫⁻ y, (ENNReal.ofReal B * ENNReal.ofReal Wr) * F y ^ 2 ∂ν := by
        refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
        have hm : Measurable (fun x : Euc d => K x y) := Measurable.of_uncurry_right (f := K) hKm (y := y)
        rw [lintegral_mul_const (F y ^ 2) hm]
        exact mul_le_mul' (hKcol y) le_rfl
    _ = ENNReal.ofReal (Wr * B) ^ 2 * ∫⁻ y, F y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hF.pow_const 2), ← mul_assoc, ENNReal.ofReal_mul hWr0]
        ring

/-- Bochner form of the Schur test: `‖∫ h(·,y) f(y) dμ(y)‖_{L²(μ)} ≤ C B ‖f‖_{L²(μ)}` for `f ∈ L²(μ)`
(the image is in `L²(μ)`; no junk value is involved). -/
theorem wr13c_schur_W_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ B : ℝ, 0 ≤ B → ∀ h : Euc d → Euc d → ℝ,
        Measurable (fun p : Euc d × Euc d => h p.1 p.2) →
        (∀ x y, x ≠ y → |h x y| ≤ B * (1 + HRS.Whole.rieszWeight s (x - y))) →
        ∀ f : Euc d → ℝ, Measurable f → MemLp f 2 (HRS.Whole.withDensityReal ρ) →
          MemLp (fun x : Euc d => ∫ y, h x y * f y ∂(HRS.Whole.withDensityReal ρ)) 2
              (HRS.Whole.withDensityReal ρ) ∧
          ∫ x, (∫ y, h x y * f y ∂(HRS.Whole.withDensityReal ρ)) ^ 2
              ∂(HRS.Whole.withDensityReal ρ) ≤
            (C * B) ^ 2 * ∫ y, f y ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC0, hC⟩ := wr13c_schur_W hd hs0 hsd M
  refine ⟨C, hC0, fun ρ hρ hM B hB h hhm hbd f hf hf2 => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set ν := HRS.Whole.withDensityReal ρ with hν
  have hsm : StronglyMeasurable (fun p : Euc d × Euc d => h p.1 p.2 * f p.2) :=
    (hhm.mul (hf.comp measurable_snd)).stronglyMeasurable
  have hTm : Measurable (fun x : Euc d => ∫ y, h x y * f y ∂ν) :=
    (hsm.integral_prod_right' (ν := ν)).measurable
  have hT2m : Measurable (fun x : Euc d => (∫ y, h x y * f y ∂ν) ^ 2) := hTm.pow_const 2
  set F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y| with hF
  have hFm : Measurable F := hf.abs.ennreal_ofReal
  have hF2 : ∫⁻ y, F y ^ 2 ∂ν = ENNReal.ofReal (∫ y, f y ^ 2 ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [hF]; simp only
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hpt : ∀ x : Euc d, ENNReal.ofReal ((∫ y, h x y * f y ∂ν) ^ 2) ≤
      (∫⁻ y, ENNReal.ofReal |h x y| * F y ∂ν) ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal |∫ y, h x y * f y ∂ν| ≤ ∫⁻ y, ENNReal.ofReal |h x y| * F y ∂ν := by
      have := enorm_integral_le_lintegral_enorm (μ := ν) (fun y => h x y * f y)
      rw [Real.enorm_eq_ofReal_abs] at this
      refine this.trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
    calc ENNReal.ofReal ((∫ y, h x y * f y ∂ν) ^ 2)
        = ENNReal.ofReal |∫ y, h x y * f y ∂ν| ^ 2 := by
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ ≤ _ := pow_le_pow_left' h1 2
  have hint0 : 0 ≤ ∫ y, f y ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg _
  have hK : ∫⁻ x, ENNReal.ofReal ((∫ y, h x y * f y ∂ν) ^ 2) ∂ν ≤
      ENNReal.ofReal ((C * B) ^ 2 * ∫ y, f y ^ 2 ∂ν) := by
    refine (lintegral_mono hpt).trans ?_
    refine (hC ρ hρ hM B hB h hhm hbd F hFm).trans (le_of_eq ?_)
    rw [hF2, ← ENNReal.ofReal_pow (mul_nonneg hC0 hB), ← ENNReal.ofReal_mul (sq_nonneg _)]
  obtain ⟨hI, hV⟩ := HRS.Whole.Q34.integrable_of_lintegral_le (μ := ν) hT2m
    (fun x => sq_nonneg _) (mul_nonneg (sq_nonneg _) hint0) hK
  exact ⟨(memLp_two_iff_integrable_sq hTm.aestronglyMeasurable).2 hI, hV⟩

/-! ### 6. Positivity of `K_μ` and the resolvent bound -/

/-- Absolute integrability of `g(x-y) u(y) v(x)` against `μ ⊗ μ` for `u, v ∈ L²(μ)`, `0 < s < d`,
`ρ ≤ M` (the hypothesis `hI` of `Q34.riesz_posdef` for `ν = μ`). -/
theorem wr13c_Kmu_pair_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {u v : Euc d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp u 2 (HRS.Whole.withDensityReal ρ)) (hv2 : MemLp v 2 (HRS.Whole.withDensityReal ρ)) :
    Integrable (fun p : Euc d × Euc d => HRS.Whole.rieszKernel d s (p.1 - p.2) * (u p.2 * v p.1))
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  have h := HRS.Whole.Q34.tk_pair_integrable hd hs0 hsd hρ hM hu hv hu2 hv2
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [HRS.Whole.Q34.rieszKernel_eq hs0.ne', mul_assoc]

/-- **`K_μ ≥ 0`** (quadratic-form version, valid on all of `L²(μ)`): `⟨u, K_μ u⟩ ≥ 0` where
`K_μ u (x) = ∫ g(x-y) u(y) dμ(y)`, `g = rieszKernel d s`, `0 < s < d`, `ρ ≤ M`.  The Bochner integrals are
not junk: `y ↦ g(x-y) u(y)` is integrable for a.e. `x` and the pair integrand is integrable
(`wr13c_Kmu_pair_integrable`). -/
theorem wr13c_Kmu_nonneg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {u : Euc d → ℝ} (hu : Measurable u) (hu2 : MemLp u 2 (HRS.Whole.withDensityReal ρ)) :
    (∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      Integrable (fun y => HRS.Whole.rieszKernel d s (x - y) * u y) (HRS.Whole.withDensityReal ρ)) ∧
    0 ≤ ∫ x, (∫ y, HRS.Whole.rieszKernel d s (x - y) * u y ∂(HRS.Whole.withDensityReal ρ)) * u x
        ∂(HRS.Whole.withDensityReal ρ) := by
  refine ⟨?_, ?_⟩
  · have := HRS.Whole.Q34.tk_ae_integrable hd hs0 hsd hρ hM hu hu2
    filter_upwards [this] with x hx
    simpa only [HRS.Whole.Q34.rieszKernel_eq hs0.ne'] using hx
  · have := HRS.Whole.Q34.tk_pos hd hs0 hsd hρ hM hu hu2
    simpa only [HRS.Whole.Q34.Tk, HRS.Whole.Q34.rieszKernel_eq hs0.ne'] using this

/-- **`K_μ ≥ 0` on `L²_0(μ)`** in the form used by the susceptibility: `⟨K_μ f, f⟩_{L²(μ)} ≥ 0` for
`f ∈ L²_0(μ)`, with `K_μ = Kop g μ` (`Q34.partC`). -/
theorem wr13c_Kmu_nonneg_L2zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {f : Euc d → ℝ} (hf : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f) :
    0 ≤ HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ)
      (HRS.Whole.Kop (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) f) f := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  exact HRS.Whole.Q34.partC ⟨hd, hs0, hsd, hρ, hM⟩ hf

/-- **`‖(I + β K_μ)⁻¹‖ ≤ 1` on `L²_0(μ)`** (`β > 0`): the response equation `h + β K_μ h = f` has an
`L²_0` solution, unique a.e., with `⟨f, h⟩ ≥ ‖f‖²/(1 + β M_g)`, `⟨f, h⟩ ≤ ‖f‖²` and `‖h‖ ≤ ‖f‖`
(`Q34.partD`, restated with `responseInverse`); `K_μ` is also bounded on `L²_0` by `M_g` (`Q34.partA`). -/
theorem wr13c_resolvent_norm_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    {β : ℝ} (hβ : 0 < β) {f : Euc d → ℝ} (hf : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) f) :
    (∃ h, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h) ∧
    (∀ h1 h2, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h1 →
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h2 →
        h1 =ᵐ[HRS.Whole.withDensityReal ρ] h2) ∧
    HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ)
      (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f) ≤
        HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) f := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  obtain ⟨h1, h2, -, -, h5⟩ := HRS.Whole.Q34.partD ⟨hd, hs0, hsd, hρ, hM⟩ hβ hf
  exact ⟨h1, h2, h5⟩

end HRS.MS.Wr
