import HRS.MS.Comm
import HRS.Whole.Q34Aux1

/-!
# WL-2 (part 1): the envelope measure and the level-set lemma for `K` (S3.5 infrastructure)

Namespace `HRS.MS.Wl`, helper prefix `wl2_`.  `K = sphericalLogKernel`, `ℓ = logWeight`,
`μ = HRS.Whole.withDensityReal ρ`, hypotheses `2 ≤ d` (we only use `1 ≤ d`), `HRS.Whole.IsProbDensity ρ`,
`HasSphericalBound A ρ` (a.e.).

Route C for the level-set lemma (neither of the two routes sketched in `docs/WR_LOG_PLAN.md`; no
inversion and no sphere is needed).  With `ν = (1+|y|²)^{-d} dy`, `s = 1 + |x|²` and
`E_δ(x) = {y | |x-y|² ≤ δ² s (1+|y|²)}` one has `ν(E_δ(x)) ≤ C δ^d` uniformly in `x`
(`wl2_nu_level`): for `|x| ≤ 1` the set is inside a ball of radius `4δ`; for `|x| > 1` it is inside
`{|y| ≥ 1/(4δ)}` (tail of `ν`, polar coordinates) union a ball of radius `2δ s` around `x` on which the
density is `≤ 4^d s^{-d}`.  Since `K x y > L` forces `y ∈ E_{e^{-L}}(x)`, `wl_level` follows.

Main statements (constants `∃ C` quantified before `ρ`, uniform in `x`):
* `wl_logmoment p` : `Integrable (ℓ^p) μ ∧ ∫ ℓ^p dμ ≤ C`;
* `wl_chordal_level` : `μ {y | |x-y|² ≤ δ² (1+|x|²)(1+|y|²)} ≤ ofReal (C δ^d)`;
* `wl_level` : `μ.real {y | L < K x y} ≤ C e^{-dL}` for `L ≥ 0`.
Documented adjustment: the bound `ρ ≤ A (1+|x|²)^{-d}` is used through `max A 1` (for `A ≤ 0`
the hypotheses are contradictory, so nothing is lost).
-/

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole

variable {d : ℕ}

/-- The envelope density `(1+|y|²)^{-d}` (real valued). -/
def wl2_f (d : ℕ) (y : Euc d) : ℝ := ((1 + ‖y‖ ^ 2) ^ d)⁻¹

/-- The envelope measure `ν = (1+|y|²)^{-d} dy`. -/
def wl2_nu (d : ℕ) : Measure (Euc d) :=
  volume.withDensity fun y => ENNReal.ofReal (wl2_f d y)

lemma wl2_f_pos (y : Euc d) : 0 < wl2_f d y := by
  unfold wl2_f; positivity

lemma wl2_f_le_one (y : Euc d) : wl2_f d y ≤ 1 := by
  unfold wl2_f
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by nlinarith [sq_nonneg ‖y‖])

lemma wl2_f_measurable : Measurable (wl2_f d : Euc d → ℝ) := by
  unfold wl2_f
  fun_prop

lemma wl2_nu_apply {S : Set (Euc d)} (hS : MeasurableSet S) :
    wl2_nu d S = ∫⁻ y in S, ENNReal.ofReal (wl2_f d y) := withDensity_apply _ hS

lemma wl2_nu_le_volume : wl2_nu d ≤ volume := by
  refine Measure.le_iff.2 fun S hS => ?_
  rw [wl2_nu_apply hS, ← setLIntegral_one S]
  refine lintegral_mono fun y => ?_
  simpa using wl2_f_le_one y

/-- A pointwise bound `f ≤ c` on a measurable set `S` gives `ν S ≤ c · vol S`. -/
lemma wl2_nu_le_const {S : Set (Euc d)} (hS : MeasurableSet S) {c : ℝ}
    (hc : ∀ y ∈ S, wl2_f d y ≤ c) : wl2_nu d S ≤ ENNReal.ofReal c * volume S := by
  rw [wl2_nu_apply hS, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun y hy => ?_
  exact ENNReal.ofReal_le_ofReal (hc y hy)

/-- Tail of the envelope measure: `ν {R ≤ |y|} ≤ c R^{-d}`. -/
lemma wl2_nu_tail (hd : 1 ≤ d) : ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 < R →
    wl2_nu d {y | R ≤ ‖y‖} ≤ ENNReal.ofReal (c / R ^ d) := by
  have hdr : (d : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hσ : 0 ≤ sphereArea d := by
    unfold sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity)
    positivity
  refine ⟨sphereArea d / d, by positivity, fun R hR => ?_⟩
  have hmeas : MeasurableSet {y : Euc d | R ≤ ‖y‖} := measurableSet_le measurable_const measurable_norm
  rw [wl2_nu_apply hmeas]
  have h1 := HRS.Whole.Q34.lintegral_compl_rpow (d := d) hd hR hdr
  calc ∫⁻ y in {y : Euc d | R ≤ ‖y‖}, ENNReal.ofReal (wl2_f d y)
      ≤ ∫⁻ y in {y : Euc d | R ≤ ‖y‖}, ENNReal.ofReal (‖y‖ ^ (-(2 * (d : ℝ)))) := by
        refine setLIntegral_mono (by fun_prop) fun y hy => ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hy
        have : ‖y‖ ^ (-(2 * (d : ℝ))) = ((‖y‖ ^ 2) ^ d)⁻¹ := by
          rw [Real.rpow_neg hy0.le, ← pow_mul, show 2 * (d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast, mul_comm 2 d, pow_mul]
        rw [this]
        unfold wl2_f
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by linarith) d
    _ = ENNReal.ofReal (sphereArea d * (R ^ ((d : ℝ) - 2 * d) / (2 * d - (d : ℝ)))) := h1
    _ = ENNReal.ofReal (sphereArea d / d / R ^ d) := by
        congr 1
        have : (d : ℝ) - 2 * d = -(d : ℝ) := by ring
        have h2 : 2 * (d : ℝ) - d = d := by ring
        rw [this, h2, Real.rpow_neg hR.le, Real.rpow_natCast]
        field_simp


/-! ### Real-variable geometry of the chordal sets -/

lemma wl2_geom1 {a b t δ : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ht0 : 0 ≤ t) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (ha : a ≤ 1) (hba : b ≤ a + t)
    (h : t ^ 2 ≤ δ ^ 2 * ((1 + a ^ 2) * (1 + b ^ 2))) : t ≤ 4 * δ := by
  have h1 : 1 + a ^ 2 ≤ 2 := by nlinarith
  have h2 : 1 + b ^ 2 ≤ 3 + 2 * t ^ 2 := by
    have : b ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ hb0 (by linarith) 2
    nlinarith [sq_nonneg (t - 1)]
  have h3 : (1 + a ^ 2) * (1 + b ^ 2) ≤ 2 * (3 + 2 * t ^ 2) := by
    apply mul_le_mul h1 h2 (by positivity) (by norm_num)
  have h4 : t ^ 2 ≤ δ ^ 2 * (2 * (3 + 2 * t ^ 2)) :=
    h.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have hδ2 : δ ^ 2 ≤ 1 / 16 := by nlinarith
  have h5 : t ^ 2 ≤ 8 * δ ^ 2 := by nlinarith [sq_nonneg t]
  have : t ^ 2 ≤ (4 * δ) ^ 2 := by nlinarith
  exact le_of_sq_le_sq this (by positivity) |>.trans le_rfl

lemma wl2_geom2 {a b t δ : ℝ} (ha1 : 1 < a) (hb0 : 0 ≤ b) (ht0 : 0 ≤ t) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 4) (hat : a ≤ t + b) (hbt : b ≤ a + t)
    (h : t ^ 2 ≤ δ ^ 2 * ((1 + a ^ 2) * (1 + b ^ 2))) :
    1 / (4 * δ) ≤ b ∨ (a / 2 < b ∧ t ≤ 2 * δ * (1 + a ^ 2)) := by
  have hδ2 : δ ^ 2 ≤ 1 / 16 := by nlinarith
  have hs : 1 + a ^ 2 ≤ 2 * a ^ 2 := by nlinarith
  by_cases hb : b ≤ a / 2
  · left
    have ht : a / 2 ≤ t := by linarith
    have h1 : a ^ 2 / 4 ≤ t ^ 2 := by nlinarith
    have h2 : a ^ 2 / 4 ≤ δ ^ 2 * ((2 * a ^ 2) * (1 + b ^ 2)) := by
      refine h1.trans (h.trans ?_)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hs (by positivity)
    have h3 : 1 ≤ 8 * δ ^ 2 * (1 + b ^ 2) := by
      have ha2 : 0 < a ^ 2 := by positivity
      by_contra hcon
      push Not at hcon
      nlinarith
    have h4 : 1 / 16 ≤ δ ^ 2 * b ^ 2 := by nlinarith [sq_nonneg b]
    have h5 : 1 / 4 ≤ δ * b := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg hδ0.le hb0]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · push Not at hb
    by_cases hb2 : 2 * a ≤ b
    · left
      have ht : b / 2 ≤ t := by linarith
      have hb1 : 1 ≤ b ^ 2 := by nlinarith
      have h1 : b ^ 2 / 4 ≤ t ^ 2 := by nlinarith
      have h2 : (1 + b ^ 2) / 8 ≤ t ^ 2 := by nlinarith
      have h3 : (1 + b ^ 2) / 8 ≤ δ ^ 2 * ((2 * a ^ 2) * (1 + b ^ 2)) := by
        refine h2.trans (h.trans ?_)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hs (by positivity)
      have h4 : 1 / 16 ≤ δ ^ 2 * a ^ 2 := by
        have hp : 0 < 1 + b ^ 2 := by positivity
        by_contra hcon
        push Not at hcon
        nlinarith
      have h5 : 1 / 4 ≤ δ * a := by
        by_contra hcon
        push Not at hcon
        nlinarith [mul_nonneg hδ0.le (by linarith : (0:ℝ) ≤ a)]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · push Not at hb2
      right
      refine ⟨hb, ?_⟩
      have h1 : 1 + b ^ 2 ≤ 4 * (1 + a ^ 2) := by nlinarith
      have h2 : t ^ 2 ≤ δ ^ 2 * ((1 + a ^ 2) * (4 * (1 + a ^ 2))) :=
        h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity))
      have : t ^ 2 ≤ (2 * δ * (1 + a ^ 2)) ^ 2 := by nlinarith
      exact le_of_sq_le_sq this (by positivity)


/-! ### The level-set estimate for the envelope measure -/

/-- Uniform chordal-ball estimate: `ν {|x-y|² ≤ δ² (1+|x|²)(1+|y|²)} ≤ C δ^d`. -/
lemma wl2_nu_level (hd : 1 ≤ d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Euc d) (δ : ℝ), 0 < δ →
    wl2_nu d {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} ≤
      ENNReal.ofReal (C * δ ^ d) := by
  obtain ⟨c, hc0, hc⟩ := wl2_nu_tail hd
  set V : ℝ := (volume (ball (0 : Euc d) 1)).toReal with hVdef
  have hVfin : volume (ball (0 : Euc d) 1) = ENNReal.ofReal V :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set W : ℝ := (volume (closedBall (0 : Euc d) 1)).toReal with hWdef
  have hWfin : volume (closedBall (0 : Euc d) 1) = ENNReal.ofReal W :=
    (ENNReal.ofReal_toReal measure_closedBall_lt_top.ne).symm
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hmass : wl2_nu d univ ≤ ENNReal.ofReal (W + c) := by
    calc wl2_nu d univ ≤ wl2_nu d (closedBall (0 : Euc d) 1 ∪ {y | 1 ≤ ‖y‖}) := by
          refine measure_mono fun y _ => ?_
          by_cases hy : ‖y‖ ≤ 1
          · exact Or.inl (by simpa using hy)
          · exact Or.inr (by show 1 ≤ ‖y‖; linarith [not_le.1 hy])
      _ ≤ wl2_nu d (closedBall (0 : Euc d) 1) + wl2_nu d {y | 1 ≤ ‖y‖} := measure_union_le _ _
      _ ≤ ENNReal.ofReal W + ENNReal.ofReal (c / 1 ^ d) :=
          add_le_add ((wl2_nu_le_volume _).trans hWfin.le) (hc 1 one_pos)
      _ = ENNReal.ofReal (W + c) := by
          rw [← ENNReal.ofReal_add hW0 (by simpa using hc0)]; simp
  refine ⟨(W + c) * 4 ^ d + V * 4 ^ d + c * 4 ^ d + 4 ^ d * 2 ^ d * V, by positivity, ?_⟩
  intro x δ hδ
  set E : Set (Euc d) := {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} with hE
  have hδd : 0 < δ ^ d := by positivity
  have p4 : (0 : ℝ) ≤ 4 ^ d := by positivity
  have p2 : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hWc : 0 ≤ W + c := by positivity
  have t1 : 0 ≤ (W + c) * 4 ^ d := mul_nonneg hWc p4
  have t2 : 0 ≤ V * 4 ^ d := mul_nonneg hV0 p4
  have t3 : 0 ≤ c * 4 ^ d := mul_nonneg hc0 p4
  have t4 : 0 ≤ 4 ^ d * 2 ^ d * V := mul_nonneg (mul_nonneg p4 p2) hV0
  have hmono : ∀ {C' : ℝ}, C' ≤ (W + c) * 4 ^ d + V * 4 ^ d + c * 4 ^ d + 4 ^ d * 2 ^ d * V →
      wl2_nu d E ≤ ENNReal.ofReal (C' * δ ^ d) →
      wl2_nu d E ≤ ENNReal.ofReal (((W + c) * 4 ^ d + V * 4 ^ d + c * 4 ^ d + 4 ^ d * 2 ^ d * V) * δ ^ d) := by
    intro C' hC' h
    exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hC' hδd.le))
  by_cases hδbig : 1 / 4 < δ
  · -- trivial regime
    refine hmono (C' := (W + c) * 4 ^ d) (by linarith) ?_
    refine (measure_mono (subset_univ E)).trans (hmass.trans (ENNReal.ofReal_le_ofReal ?_))
    have h1 : 1 ≤ (4 * δ) ^ d := one_le_pow₀ (by linarith)
    rw [mul_assoc, ← mul_pow]
    nlinarith
  push Not at hδbig
  have hs0 : 0 < 1 + ‖x‖ ^ 2 := by positivity
  by_cases hx : ‖x‖ ≤ 1
  · refine hmono (C' := V * 4 ^ d) (by linarith) ?_
    have hsub : E ⊆ closedBall x (4 * δ) := by
      intro y hy
      rw [mem_closedBall, dist_comm, dist_eq_norm]
      refine wl2_geom1 (norm_nonneg x) (norm_nonneg y) (norm_nonneg _) hδ hδbig hx ?_ hy
      calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
    calc wl2_nu d E ≤ wl2_nu d (closedBall x (4 * δ)) := measure_mono hsub
      _ ≤ volume (closedBall x (4 * δ)) := wl2_nu_le_volume _
      _ = ENNReal.ofReal ((4 * δ) ^ d) * ENNReal.ofReal V := by
          rw [Measure.addHaar_closedBall _ x (by positivity), hfr, hVfin]
      _ = ENNReal.ofReal (V * 4 ^ d * δ ^ d) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; rw [mul_pow]; ring
  · push Not at hx
    set s : ℝ := 1 + ‖x‖ ^ 2 with hs
    set T : Set (Euc d) := {y | 1 / (4 * δ) ≤ ‖y‖} with hT
    set B' : Set (Euc d) := closedBall x (2 * δ * s) ∩ {y | ‖x‖ / 2 < ‖y‖} with hB'
    have hsub : E ⊆ T ∪ B' := by
      intro y hy
      have hy' : ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := hy
      have hat : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have hbt : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
        calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
          _ ≤ _ := norm_sub_le _ _
      rcases wl2_geom2 hx (norm_nonneg y) (norm_nonneg _) hδ hδbig hat hbt hy' with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨?_, h1⟩
        rw [mem_closedBall, dist_comm, dist_eq_norm]
        exact h2
    have hTb : wl2_nu d T ≤ ENNReal.ofReal (c * 4 ^ d * δ ^ d) := by
      refine (hc _ (by positivity)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [one_div, inv_pow]
      rw [div_inv_eq_mul, mul_pow]; ring
    have hBb : wl2_nu d B' ≤ ENNReal.ofReal (4 ^ d * 2 ^ d * V * δ ^ d) := by
      have hmeasB : MeasurableSet B' :=
        measurableSet_closedBall.inter (measurableSet_lt measurable_const measurable_norm)
      have hdens : ∀ y ∈ B', wl2_f d y ≤ 4 ^ d / s ^ d := by
        intro y hy
        have hy2 : ‖x‖ / 2 < ‖y‖ := hy.2
        have h1 : s / 4 ≤ 1 + ‖y‖ ^ 2 := by
          have : (‖x‖ / 2) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy2.le 2
          rw [hs]; nlinarith
        unfold wl2_f
        have h2 : (s / 4) ^ d ≤ (1 + ‖y‖ ^ 2) ^ d := pow_le_pow_left₀ (by positivity) h1 d
        calc ((1 + ‖y‖ ^ 2) ^ d)⁻¹ ≤ ((s / 4) ^ d)⁻¹ := inv_anti₀ (by positivity) h2
          _ = 4 ^ d / s ^ d := by rw [div_pow, inv_div]
      refine (wl2_nu_le_const hmeasB hdens).trans ?_
      calc ENNReal.ofReal (4 ^ d / s ^ d) * volume B'
          ≤ ENNReal.ofReal (4 ^ d / s ^ d) * volume (closedBall x (2 * δ * s)) :=
            mul_le_mul' le_rfl (measure_mono inter_subset_left)
        _ = ENNReal.ofReal (4 ^ d / s ^ d) * (ENNReal.ofReal ((2 * δ * s) ^ d) * ENNReal.ofReal V) := by
            rw [Measure.addHaar_closedBall _ x (by positivity), hfr, hVfin]
        _ = ENNReal.ofReal (4 ^ d * 2 ^ d * V * δ ^ d) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have : s ^ d ≠ 0 := by positivity
            rw [mul_pow, mul_pow]
            field_simp
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    calc wl2_nu d T + wl2_nu d B' ≤ ENNReal.ofReal (c * 4 ^ d * δ ^ d) +
          ENNReal.ofReal (4 ^ d * 2 ^ d * V * δ ^ d) := add_le_add hTb hBb
      _ = ENNReal.ofReal ((c * 4 ^ d + 4 ^ d * 2 ^ d * V) * δ ^ d) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hδd.le)


/-! ### Transfer to `μ = HRS.Whole.withDensityReal ρ` -/

lemma wl2_isProb {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := by
  have hint : Integrable ρ :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

lemma wl2_rpow_eq (x : Euc d) : (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) = wl2_f d x := by
  unfold wl2_f
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- `μ ≤ max A 1 · ν`. -/
lemma wl2_mu_le {A : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hA : HasSphericalBound A ρ) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal (max A 1) • wl2_nu d := by
  refine Measure.le_iff.2 fun S hS => ?_
  unfold HRS.Whole.withDensityReal
  have hm : Measurable (fun y : Euc d => ENNReal.ofReal (wl2_f d y)) :=
    ENNReal.measurable_ofReal.comp wl2_f_measurable
  rw [withDensity_apply _ hS, Measure.smul_apply, smul_eq_mul, wl2_nu_apply hS,
    ← lintegral_const_mul _ hm]
  refine setLIntegral_mono_ae (hm.const_mul _).aemeasurable ?_
  filter_upwards [hA] with y hy _
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right A 1))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← wl2_rpow_eq]
  have hpos : 0 < (1 + ‖y‖ ^ 2) ^ (-(d : ℝ)) := by positivity
  exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left A 1) hpos.le)

/-- The chordal level-set estimate for `μ`: `μ {|x-y|² ≤ δ² (1+|x|²)(1+|y|²)} ≤ C δ^d`. -/
theorem wl_chordal_level (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
    HasSphericalBound A ρ → ∀ (x : Euc d) (δ : ℝ), 0 < δ →
      HRS.Whole.withDensityReal ρ {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} ≤
        ENNReal.ofReal (C * δ ^ d) := by
  obtain ⟨Cν, hCν0, hCν⟩ := wl2_nu_level (d := d) (by omega)
  refine ⟨max A 1 * Cν, mul_nonneg (le_trans zero_le_one (le_max_right A 1)) hCν0, ?_⟩
  intro ρ hρ hA x δ hδ
  have h1 := Measure.le_iff'.1 (wl2_mu_le hρ hA) {y | ‖x - y‖ ^ 2 ≤ δ ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))}
  refine h1.trans ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_assoc (max A 1),
    ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right A 1))]
  exact mul_le_mul' le_rfl (hCν x δ hδ)

lemma wl2_logWeight_measurable : Measurable (logWeight : Euc d → ℝ) := by
  unfold logWeight
  exact (Real.measurable_log.comp (measurable_const.add (measurable_norm.pow_const 2))).const_mul _

lemma wl2_K_measurable : Measurable (fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) := by
  have h1 : Measurable fun p : Euc d × Euc d => Real.log ‖p.1 - p.2‖ :=
    Real.measurable_log.comp (measurable_norm.comp (measurable_fst.sub measurable_snd))
  have h2 : Measurable (logWeight : Euc d → ℝ) := wl2_logWeight_measurable
  have : (fun p : Euc d × Euc d => sphericalLogKernel p.1 p.2) =
      fun p => -Real.log ‖p.1 - p.2‖ + logWeight p.1 + logWeight p.2 := rfl
  rw [this]
  exact (h1.neg.add (h2.comp measurable_fst)).add (h2.comp measurable_snd)

lemma wl2_K_measurable_right (x : Euc d) : Measurable (sphericalLogKernel x) := by
  have : sphericalLogKernel x = fun y => -Real.log ‖x - y‖ + logWeight x + logWeight y := rfl
  rw [this]
  have h1 : Measurable fun y : Euc d => Real.log ‖x - y‖ :=
    Real.measurable_log.comp (measurable_norm.comp (measurable_const.sub measurable_id))
  exact (h1.neg.add measurable_const).add wl2_logWeight_measurable

lemma wl2_logWeight_nonneg (x : Euc d) : 0 ≤ logWeight x := by
  unfold logWeight
  have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 by nlinarith [sq_nonneg ‖x‖])
  linarith

/-- `K x y > L` forces `y` into the chordal ball of radius `e^{-L}` around `x`. -/
lemma wl2_level_subset (x : Euc d) {L : ℝ} :
    {y | L < sphericalLogKernel x y} ⊆
      {y | ‖x - y‖ ^ 2 ≤ (Real.exp (-L)) ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))} := by
  intro y hy
  have hy' : L < sphericalLogKernel x y := hy
  show ‖x - y‖ ^ 2 ≤ (Real.exp (-L)) ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2))
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, norm_zero]
    have : (0 : ℝ) ≤ (Real.exp (-L)) ^ 2 * ((1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2)) := by positivity
    simpa using this
  have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have ha : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hb : 0 < 1 + ‖y‖ ^ 2 := by positivity
  unfold sphericalLogKernel logWeight at hy'
  have hlog : Real.log (‖x - y‖ ^ 2) < Real.log ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2) * Real.exp (-2 * L)) := by
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul ha.ne' hb.ne', Real.log_exp]
    push_cast
    linarith
  have h2 := (Real.log_lt_log_iff (by positivity) (by positivity)).1 hlog
  have h3 : (Real.exp (-L)) ^ 2 = Real.exp (-2 * L) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h3]
  nlinarith

/-- **Level-set lemma** (`ℝ≥0∞` form). -/
theorem wl_level_enn (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ (x : Euc d) (L : ℝ), 0 ≤ L →
      HRS.Whole.withDensityReal ρ {y | L < sphericalLogKernel x y} ≤
        ENNReal.ofReal (C * Real.exp (-(d : ℝ) * L)) := by
  obtain ⟨C, hC0, hC⟩ := wl_chordal_level hd A
  refine ⟨C, hC0, fun ρ hρ hA x L hL => ?_⟩
  have h1 := (measure_mono (μ := HRS.Whole.withDensityReal ρ) (wl2_level_subset x (L := L))).trans
    (hC ρ hρ hA x (Real.exp (-L)) (Real.exp_pos _))
  refine h1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- **Level-set lemma.** `μ {y | L < K x y} ≤ C e^{-dL}` uniformly in `x` and `L ≥ 0`. -/
theorem wl_level (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
    HasSphericalBound A ρ → ∀ (x : Euc d) (L : ℝ), 0 ≤ L →
      (HRS.Whole.withDensityReal ρ).real {y | L < sphericalLogKernel x y} ≤ C * Real.exp (-(d : ℝ) * L) := by
  obtain ⟨C, hC0, hC⟩ := wl_level_enn hd A
  refine ⟨C, hC0, fun ρ hρ hA x L hL => ?_⟩
  unfold Measure.real
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hC ρ hρ hA x L hL)

/-! ### Moments of `ℓ` -/

/-- From a bound on `∫⁻ ofReal f` to integrability and a bound on the Bochner integral. -/
lemma wl2_integrable_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEMeasurable f μ) (h0 : ∀ y, 0 ≤ f y) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤ ENNReal.ofReal C) :
    Integrable f μ ∧ ∫ y, f y ∂μ ≤ C := by
  refine ⟨⟨hf.aestronglyMeasurable, ?_⟩, ?_⟩
  · exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)).2
      (lt_of_le_of_lt hC ENNReal.ofReal_lt_top)
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hf.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC0 hC

lemma wl2_lintegral_nu_le {g G : Euc d → ℝ} (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hG : Integrable G) (hgG : ∀ y, wl2_f d y * g y ≤ G y) :
    ∫⁻ y, ENNReal.ofReal (g y) ∂(wl2_nu d) ≤ ENNReal.ofReal (∫ y, G y) := by
  have hm : Measurable (fun y : Euc d => ENNReal.ofReal (wl2_f d y)) :=
    ENNReal.measurable_ofReal.comp wl2_f_measurable
  have hgm : Measurable (fun y => ENNReal.ofReal (g y)) := ENNReal.measurable_ofReal.comp hg
  unfold wl2_nu
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hgm]
  have hG0 : ∀ y, 0 ≤ G y := fun y =>
    le_trans (mul_nonneg (wl2_f_pos y).le (hg0 y)) (hgG y)
  rw [ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall hG0)]
  refine lintegral_mono fun y => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (wl2_f_pos y).le]
  exact ENNReal.ofReal_le_ofReal (hgG y)

lemma wl2_logWeight_pow_le (p : ℕ) (y : Euc d) :
    logWeight y ^ p ≤ (p.factorial : ℝ) * (1 + ‖y‖) := by
  have h0 := wl2_logWeight_nonneg y
  have h1 := Real.pow_div_factorial_le_exp (logWeight y) h0 p
  have hsq : Real.exp (logWeight y) ^ 2 = 1 + ‖y‖ ^ 2 := by
    rw [← Real.exp_nat_mul]
    unfold logWeight
    push_cast
    rw [show (2 : ℝ) * (1 / 2 * Real.log (1 + ‖y‖ ^ 2)) = Real.log (1 + ‖y‖ ^ 2) by ring,
      Real.exp_log (by positivity)]
  have h2 : Real.exp (logWeight y) ≤ 1 + ‖y‖ := by
    have : Real.exp (logWeight y) ^ 2 ≤ (1 + ‖y‖) ^ 2 := by
      rw [hsq]; nlinarith [norm_nonneg y]
    exact le_of_sq_le_sq this (by positivity)
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  rw [div_le_iff₀ hf] at h1
  nlinarith

lemma wl2_logmoment_pointwise (p : ℕ) (y : Euc d) :
    wl2_f d y * logWeight y ^ p ≤
      (p.factorial : ℝ) * 2 ^ d * (1 + ‖y‖) ^ (-(2 * (d : ℝ) - 1)) := by
  set r : ℝ := 1 + ‖y‖ with hr
  have hr0 : 0 < r := by positivity
  have h1 : r ^ 2 / 2 ≤ 1 + ‖y‖ ^ 2 := by rw [hr]; nlinarith [sq_nonneg (‖y‖ - 1)]
  have h2 : (r ^ 2 / 2) ^ d ≤ (1 + ‖y‖ ^ 2) ^ d := pow_le_pow_left₀ (by positivity) h1 d
  have hf : wl2_f d y ≤ 2 ^ d / r ^ (2 * d) := by
    unfold wl2_f
    calc ((1 + ‖y‖ ^ 2) ^ d)⁻¹ ≤ ((r ^ 2 / 2) ^ d)⁻¹ := inv_anti₀ (by positivity) h2
      _ = 2 ^ d / r ^ (2 * d) := by rw [div_pow, inv_div, ← pow_mul]
  have hrp : r ^ (-(2 * (d : ℝ) - 1)) = r / r ^ (2 * d) := by
    rw [Real.rpow_neg hr0.le, Real.rpow_sub hr0, Real.rpow_one,
      show (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, inv_div]
  rw [hrp]
  have h3 := wl2_logWeight_pow_le p y
  have hp : 0 ≤ wl2_f d y := (wl2_f_pos y).le
  calc wl2_f d y * logWeight y ^ p ≤ (2 ^ d / r ^ (2 * d)) * ((p.factorial : ℝ) * r) :=
        mul_le_mul hf h3 (pow_nonneg (wl2_logWeight_nonneg y) p) (by positivity)
    _ = _ := by ring

/-- **`wl_logmoment`.**  `ℓ^p ∈ L¹(μ)` with a bound depending on `d, A, p` only. -/
theorem wl_logmoment (hd : 2 ≤ d) (A : ℝ) (p : ℕ) : ∃ C : ℝ, ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      Integrable (fun x => logWeight x ^ p) (HRS.Whole.withDensityReal ρ) ∧
        ∫ x, logWeight x ^ p ∂(HRS.Whole.withDensityReal ρ) ≤ C := by
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hint : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-(2 * (d : ℝ) - 1))) := by
    apply integrable_one_add_norm
    rw [hfr]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set J : ℝ := ∫ y : Euc d, (1 + ‖y‖) ^ (-(2 * (d : ℝ) - 1)) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  set c0 : ℝ := max A 1 with hc0
  have hc0' : 0 ≤ c0 := le_trans zero_le_one (le_max_right A 1)
  set Cp : ℝ := (p.factorial : ℝ) * 2 ^ d * J with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  refine ⟨c0 * Cp, fun ρ hρ hA => ?_⟩
  have hgm : Measurable (fun x : Euc d => logWeight x ^ p) := wl2_logWeight_measurable.pow_const p
  have hbd : ∫⁻ y, ENNReal.ofReal (logWeight y ^ p) ∂(wl2_nu d) ≤ ENNReal.ofReal Cp := by
    have := wl2_lintegral_nu_le hgm (fun y => pow_nonneg (wl2_logWeight_nonneg y) p)
      (hint.const_mul ((p.factorial : ℝ) * 2 ^ d)) (fun y => wl2_logmoment_pointwise p y)
    rw [integral_const_mul] at this
    exact this
  refine wl2_integrable_of_lintegral_le hgm.aemeasurable (fun y => pow_nonneg (wl2_logWeight_nonneg y) p)
    (by positivity) ?_
  calc ∫⁻ y, ENNReal.ofReal (logWeight y ^ p) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal (logWeight y ^ p) ∂(ENNReal.ofReal c0 • wl2_nu d) :=
        lintegral_mono' (wl2_mu_le hρ hA) le_rfl
    _ = ENNReal.ofReal c0 * ∫⁻ y, ENNReal.ofReal (logWeight y ^ p) ∂(wl2_nu d) := lintegral_smul_measure _ _
    _ ≤ ENNReal.ofReal c0 * ENNReal.ofReal Cp := mul_le_mul' le_rfl hbd
    _ = ENNReal.ofReal (c0 * Cp) := (ENNReal.ofReal_mul hc0').symm

end HRS.MS.Wl
