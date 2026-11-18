import HRS.Whole.Q34Aux7

/-!
# Packet Q34, helper file 8: the `L²` bound for `g * f`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

theorem add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simpa [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num] using h

/-- `L²(dx)` bound of the near/far splitting of `g * |f|`. -/
theorem l2_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hds : (d : ℝ) < 2 * s)
    {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (hfi : Integrable f)
    {ε : ℝ} (hε : ∫ x, |f x| ≤ ε) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2 ≤
      ENNReal.ofReal (2 * ((sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) ^ 2 * (B * ε) +
        ε ^ 2 * (sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))))) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hsA := sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have h2s : 0 < 2 * s - (d : ℝ) := by linarith
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 ≤ ε := hint0.trans hε
  set F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |f y| with hF
  have hFm : Measurable F := hf.abs.ennreal_ofReal
  set g1 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) r).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s)))
    with hg1
  set g2 : Euc d → ℝ≥0∞ := {z : Euc d | r ≤ ‖z‖}.indicator
    (fun w => ENNReal.ofReal (‖w‖ ^ (-s))) with hg2
  have hg1m : Measurable g1 :=
    ((measurable_norm.pow_const _).ennreal_ofReal).indicator measurableSet_ball
  have hg2m : Measurable g2 :=
    ((measurable_norm.pow_const _).ennreal_ofReal).indicator
      (measurableSet_le measurable_const measurable_norm)
  have hpart : ∀ w : Euc d, ENNReal.ofReal (‖w‖ ^ (-s)) = g1 w + g2 w := by
    intro w
    by_cases hw : ‖w‖ < r
    · have h1 : w ∈ ball (0 : Euc d) r := by simpa using hw
      have h2 : w ∉ {z : Euc d | r ≤ ‖z‖} := by simpa using hw
      simp [hg1, hg2, h1, h2]
    · have h1 : w ∉ ball (0 : Euc d) r := by simpa using hw
      have h2 : w ∈ {z : Euc d | r ≤ ‖z‖} := not_lt.1 hw
      simp [hg1, hg2, h1, h2]
  -- the decomposition `N = N₁ + N₂`
  have hN : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| =
      (∫⁻ w, g1 w * F (x - w)) + ∫⁻ y, F y * g2 (x - y) := by
    intro x
    have e1 : ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| =
        ∫⁻ w, ENNReal.ofReal (‖w‖ ^ (-s)) * F (x - w) := by
      have := lintegral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
        (fun y : Euc d => ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) x
      rw [← this]
      simp only [sub_sub_cancel, hF]
    have e2 : ∫⁻ y, F y * g2 (x - y) = ∫⁻ w, g2 w * F (x - w) := by
      have := lintegral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun y : Euc d => F y * g2 (x - y)) x
      rw [← this]
      simp only [sub_sub_cancel]
      refine lintegral_congr fun w => ?_
      rw [mul_comm]
    have hm1 : Measurable (fun w : Euc d => g1 w * F (x - w)) :=
      hg1m.mul (hFm.comp (measurable_const.sub measurable_id))
    rw [e1, e2, ← lintegral_add_left hm1 (fun w : Euc d => g2 w * F (x - w))]
    refine lintegral_congr fun w => ?_
    rw [hpart w, add_mul]
  have hy1 := young_L1_L2 g1 F hg1m hFm
  have hy2 := young_L1_L2 F g2 hFm hg2m
  -- integrals of `g1`, `F`, `F²`, `g2²`
  have hI1 : ∫⁻ w, g1 w = ENNReal.ofReal (sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
    rw [hg1, lintegral_indicator measurableSet_ball, lintegral_ball_rpow hd hr hsd]
  have hIF : ∫⁻ y, F y = ENNReal.ofReal (∫ y, |f y|) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfi.abs
      (Filter.Eventually.of_forall fun y => abs_nonneg _)]
  have hIF2 : ∫⁻ y, F y ^ 2 ≤ ENNReal.ofReal (B * ε) := by
    calc ∫⁻ y, F y ^ 2 ≤ ∫⁻ y, ENNReal.ofReal B * F y := by
          refine lintegral_mono fun y => ?_
          rw [pow_two]
          exact mul_le_mul' (by simpa [hF] using ENNReal.ofReal_le_ofReal (hB y)) le_rfl
      _ = ENNReal.ofReal B * ∫⁻ y, F y := lintegral_const_mul _ hFm
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal ε := by
          rw [hIF]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hε)
      _ = ENNReal.ofReal (B * ε) := (ENNReal.ofReal_mul hB0).symm
  have hIg2 : ∫⁻ w, g2 w ^ 2 = ENNReal.ofReal (sphereArea d *
      (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) := by
    have : ∀ w : Euc d, g2 w ^ 2 = {z : Euc d | r ≤ ‖z‖}.indicator
        (fun w => ENNReal.ofReal (‖w‖ ^ (-(2 * s)))) w := by
      intro w
      by_cases hw : r ≤ ‖w‖
      · have h2 : w ∈ {z : Euc d | r ≤ ‖z‖} := hw
        simp only [hg2, indicator_of_mem h2]
        rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (norm_nonneg _) _)]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        congr 1; push_cast; ring
      · have h2 : w ∉ {z : Euc d | r ≤ ‖z‖} := hw
        simp [hg2, indicator_of_notMem h2]
    simp_rw [this]
    rw [lintegral_indicator (measurableSet_le measurable_const measurable_norm),
      lintegral_compl_rpow hd hr hds]
  calc ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2
      = ∫⁻ x, ((∫⁻ w, g1 w * F (x - w)) + ∫⁻ y, F y * g2 (x - y)) ^ 2 := by
        refine lintegral_congr fun x => ?_
        rw [hN x]
    _ ≤ ∫⁻ x, 2 * ((∫⁻ w, g1 w * F (x - w)) ^ 2 + (∫⁻ y, F y * g2 (x - y)) ^ 2) :=
        lintegral_mono fun x => add_sq_le _ _
    _ = 2 * ((∫⁻ x, (∫⁻ w, g1 w * F (x - w)) ^ 2) + ∫⁻ x, (∫⁻ y, F y * g2 (x - y)) ^ 2) := by
        have hm1 : Measurable (fun x : Euc d => (∫⁻ w, g1 w * F (x - w)) ^ 2) :=
          (Measurable.lintegral_prod_right' (f := fun p : Euc d × Euc d => g1 p.2 * F (p.1 - p.2))
            ((hg1m.comp measurable_snd).mul (hFm.comp (measurable_fst.sub measurable_snd)))).pow_const 2
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm1]
    _ ≤ 2 * ((∫⁻ w, g1 w) ^ 2 * (∫⁻ x, F x ^ 2) + (∫⁻ y, F y) ^ 2 * ∫⁻ x, g2 x ^ 2) := by
        gcongr
    _ ≤ 2 * ((ENNReal.ofReal (sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s)))) ^ 2 *
          ENNReal.ofReal (B * ε) + (ENNReal.ofReal ε) ^ 2 * ENNReal.ofReal (sphereArea d *
          (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ))))) := by
        rw [hI1, hIg2, hIF]
        gcongr
    _ = _ := by
        have ha : 0 ≤ sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
          have := Real.rpow_nonneg hr.le ((d : ℝ) - s)
          positivity
        have hh : 0 ≤ sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ))) := by
          have := Real.rpow_nonneg hr.le ((d : ℝ) - 2 * s)
          positivity
        rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_pow hε0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]


theorem l2_chain (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hds : (d : ℝ) < 2 * s)
    {f : Euc d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (hfi : Integrable f)
    {ε : ℝ} (hεpos : 0 < ε) (hε : ∫ x, |f x| ≤ ε) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    ∫⁻ x, ENNReal.ofReal ((∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * (2 * (sphereArea d ^ 2 * B / ((d : ℝ) - s) ^ 2 +
        sphereArea d / (2 * s - (d : ℝ)))) * ε ^ (3 - 2 * s / d)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hsA := sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have h2s : 0 < 2 * s - (d : ℝ) := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set T : Euc d → ℝ := fun x => ∫ y, ‖x - y‖ ^ (-s) * f y with hT
  have hTm : Measurable T := by
    have hsm : StronglyMeasurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * f p.2) :=
      (((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).mul
        (hf.comp measurable_snd)).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  have hT2m : Measurable (fun x => ENNReal.ofReal (T x ^ 2)) := (hTm.pow_const 2).ennreal_ofReal
  -- pointwise bound by `N²`
  have hpt : ∀ x : Euc d, ENNReal.ofReal (T x ^ 2) ≤
      (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal |T x| ≤ ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| := by
      have := enorm_integral_le_lintegral_enorm (μ := (volume : Measure (Euc d)))
        (fun y => ‖x - y‖ ^ (-s) * f y)
      rw [Real.enorm_eq_ofReal_abs] at this
      refine this.trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ENNReal.ofReal (T x ^ 2) = ENNReal.ofReal |T x| ^ 2 := by
          rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ ≤ _ := pow_le_pow_left' h1 2
  set r : ℝ := ε ^ (1 / (d : ℝ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hεpos _
  have hcore := l2_core hd hs0 hsd hds hf hB hfi hε hr0
  have e1 : r ^ ((d : ℝ) - s) = ε ^ (1 - s / d) := by
    rw [hr, ← Real.rpow_mul hεpos.le]
    congr 1; field_simp
  have e2 : r ^ ((d : ℝ) - 2 * s) = ε ^ (1 - 2 * s / d) := by
    rw [hr, ← Real.rpow_mul hεpos.le]
    congr 1; field_simp
  have h3 : (ε ^ (1 - s / d)) ^ 2 * ε = ε ^ (3 - 2 * s / d) := by
    have h : (ε ^ (1 - s / d)) ^ 2 = ε ^ ((1 - s / d) * 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεpos.le]
      push_cast; rfl
    rw [h, show (3 - 2 * s / (d : ℝ)) = (1 - s / d) * 2 + 1 by ring,
      Real.rpow_add_one hεpos.ne']
  have h4 : ε ^ 2 * ε ^ (1 - 2 * s / d) = ε ^ (3 - 2 * s / d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hεpos]
    congr 1; push_cast; ring
  have hexpr : 2 * ((sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) ^ 2 * (B * ε) +
        ε ^ 2 * (sphereArea d * (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ))))) =
      (2 * (sphereArea d ^ 2 * B / ((d : ℝ) - s) ^ 2 + sphereArea d / (2 * s - (d : ℝ)))) *
        ε ^ (3 - 2 * s / d) := by
    rw [e1, e2]
    calc _ = 2 * (sphereArea d ^ 2 * B / ((d : ℝ) - s) ^ 2 * ((ε ^ (1 - s / d)) ^ 2 * ε) +
          sphereArea d / (2 * s - (d : ℝ)) * (ε ^ 2 * ε ^ (1 - 2 * s / d))) := by
            have h5 := hdm.ne'
            have h6 := h2s.ne'
            field_simp
      _ = 2 * (sphereArea d ^ 2 * B / ((d : ℝ) - s) ^ 2 * ε ^ (3 - 2 * s / d) +
          sphereArea d / (2 * s - (d : ℝ)) * ε ^ (3 - 2 * s / d)) := by rw [h3, h4]
      _ = _ := by ring
  rw [hexpr] at hcore
  calc ∫⁻ x, ENNReal.ofReal (T x ^ 2) ∂(withDensityReal ρ)
      = ∫⁻ x, ENNReal.ofReal (ρ x) * ENNReal.ofReal (T x ^ 2) := lintegral_nu hρ _ hT2m
    _ ≤ ∫⁻ x, ENNReal.ofReal M * ENNReal.ofReal (T x ^ 2) := by
        refine lintegral_mono fun x => ?_
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hM x)) le_rfl
    _ = ENNReal.ofReal M * ∫⁻ x, ENNReal.ofReal (T x ^ 2) := lintegral_const_mul _ hT2m
    _ ≤ ENNReal.ofReal M * ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y|) ^ 2 :=
        mul_le_mul' le_rfl (lintegral_mono hpt)
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal ((2 * (sphereArea d ^ 2 * B / ((d : ℝ) - s) ^ 2 +
          sphereArea d / (2 * s - (d : ℝ)))) * ε ^ (3 - 2 * s / d)) :=
        mul_le_mul' le_rfl hcore
    _ = _ := by
        rw [← ENNReal.ofReal_mul hM0]
        congr 1
        ring


theorem measurable_conv {s : ℝ} {f : Euc d → ℝ} (hf : Measurable f) :
    Measurable (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) := by
  have hsm : StronglyMeasurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * f p.2) :=
    (((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).mul
      (hf.comp measurable_snd)).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable

theorem l2_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hds : (d : ℝ) < 2 * s)
    (B M : ℝ) :
    ∃ CBM : ℝ, ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
          MemLp (fun x : Euc d => ∫ y, ‖x - y‖ ^ (-s) * f y) 2 (withDensityReal ρ) ∧
          Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(withDensityReal ρ)) ≤
            CBM * ε ^ (3 / 2 - s / d) := by
  have hsA := sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have h2s : 0 < 2 * s - (d : ℝ) := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨Real.sqrt (|M| * (2 * (sphereArea d ^ 2 * |B| / ((d : ℝ) - s) ^ 2 +
    sphereArea d / (2 * s - (d : ℝ))))), ?_⟩
  intro f hf hB hfi ε hε1 hε ρ hρ hM
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  haveI := isProbabilityMeasure_nu hρ
  rw [abs_of_nonneg hB0, abs_of_nonneg hM0]
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 ≤ ε := hint0.trans hε
  have hTm := measurable_conv (s := s) hf
  have hexp : 0 < 3 / 2 - s / (d : ℝ) := by
    have : s / (d : ℝ) < 1 := by rw [div_lt_one hdpos]; exact hsd
    linarith
  rcases hε0.eq_or_lt with hε' | hεpos
  · -- `ε = 0`
    subst hε'
    have hz : ∫ y, |f y| = 0 := le_antisymm hε hint0
    have hae : (fun y => |f y|) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg _) hfi.abs).1 hz
    have hT0 : ∀ x : Euc d, ∫ y, ‖x - y‖ ^ (-s) * f y = 0 := by
      intro x
      have hae2 : (fun y => ‖x - y‖ ^ (-s) * f y) =ᵐ[volume] 0 := by
        filter_upwards [hae] with y hy
        have : f y = 0 := abs_eq_zero.1 hy
        simp [this]
      rw [integral_congr_ae hae2]
      simp
    simp only [hT0]
    refine ⟨MemLp.zero, ?_⟩
    simp [Real.zero_rpow hexp.ne']
  · set K : ℝ := 2 * (sphereArea d ^ 2 * B / ((d : ℝ) - s) ^ 2 +
      sphereArea d / (2 * s - (d : ℝ))) with hK
    have hK0 : 0 ≤ K := by positivity
    have hE0 : 0 ≤ M * K * ε ^ (3 - 2 * s / d) := by
      have := Real.rpow_nonneg hεpos.le (3 - 2 * s / d)
      positivity
    have hL := l2_chain hd hs0 hsd hds hf hB hfi hεpos hε hρ hM
    have hT2m : Measurable (fun x : Euc d => (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2) := hTm.pow_const 2
    obtain ⟨hI, hV⟩ := integrable_of_lintegral_le (μ := withDensityReal ρ) hT2m
      (fun x => sq_nonneg _) hE0 (by simpa [hK, mul_assoc] using hL)
    refine ⟨(memLp_two_iff_integrable_sq hTm.aestronglyMeasurable).2 hI, ?_⟩
    calc Real.sqrt (∫ x, (∫ y, ‖x - y‖ ^ (-s) * f y) ^ 2 ∂(withDensityReal ρ))
        ≤ Real.sqrt (M * K * ε ^ (3 - 2 * s / d)) := Real.sqrt_le_sqrt hV
      _ = Real.sqrt (M * K) * ε ^ (3 / 2 - s / d) := by
          rw [Real.sqrt_mul (mul_nonneg hM0 hK0)]
          congr 1
          have h1 : ε ^ (3 - 2 * s / (d : ℝ)) = (ε ^ (3 / 2 - s / (d : ℝ))) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hεpos.le]
            congr 1; push_cast; ring
          rw [h1, Real.sqrt_sq (Real.rpow_nonneg hεpos.le _)]

end HRS.Whole.Q34
