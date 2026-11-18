import HRS.MS.CritForceMom15

/-!
# S8.2 NormalForm packet R04, part 2: `weighted_pin_product`

Pro packet `S82.R04` (`weighted_pin_product`, `S8.2-Moments.lean`) with the `s82n_`-renamed definitions.
Mechanism (shorter than the packet's two-anchor split): `pole y z ≤ 2^s pole x y` on the half-space `|x-z| ≤ |y-z|`,
so `triplePole ≤ (1+2^s) pole(x,y) (pole(x,z) + pole(y,z))`; the capped factor is dominated by the
capped single-anchor profile `ψ_N`, and the single-anchor row is `s82p_anchor` (Mom15).
The estimate actually proved has the factor `log(eN)` in place of `log(eN) + 1 + |log r_xy|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82P

open HRS HRS.Whole HRS.MS.S82N

variable {d : ℕ}

/-- Pro `triplePole`. -/
def s82p_triplePole {d : ℕ} (x y z : Euc d) : ℝ :=
  s82n_pole x y * s82n_pole x z + s82n_pole x y * s82n_pole y z + s82n_pole x z * s82n_pole y z

/-- Pro `pairWeight`. -/
def s82p_pairWeight {d : ℕ} (M : ℝ) (x y : Euc d) : ℝ := jbracket x ^ M * jbracket y ^ M

lemma s82p_smallRadius_nonneg (x y : Euc d) : 0 ≤ s82n_smallRadius x y :=
  le_min zero_le_one (norm_nonneg _)

lemma s82p_pole_ge_one (x z : Euc d) : 1 ≤ s82n_pole x z := by
  have : 0 ≤ s82n_smallRadius x z ^ (-s82n_critS d) :=
    Real.rpow_nonneg (s82p_smallRadius_nonneg x z) _
  unfold s82n_pole; linarith

lemma s82p_smallRadius_symm (x y : Euc d) : s82n_smallRadius y x = s82n_smallRadius x y := by
  unfold s82n_smallRadius; rw [norm_sub_rev]

lemma s82p_pole_symm (x y : Euc d) : s82n_pole y x = s82n_pole x y := by
  unfold s82n_pole; rw [s82p_smallRadius_symm]

/-- Cross-bound for poles: if `z` is closer to `u` than to `v`, then `pole v z ≤ 2^s pole u v`. -/
lemma s82p_pole_cross (hd : 1 ≤ d) (u v z : Euc d) (huv : u ≠ v) (h : ‖u - z‖ ≤ ‖v - z‖) :
    s82n_pole v z ≤ 2 ^ s82n_critS d * s82n_pole u v := by
  have hs := s82n_critS_pos hd
  set r := s82n_smallRadius u v with hr
  set m := s82n_smallRadius v z with hm
  have hrpos : 0 < r := lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 huv))
  have hrm : r ≤ 2 * m := by
    have h1 : ‖u - v‖ ≤ 2 * ‖v - z‖ := by
      have : u - v = (u - z) - (v - z) := by abel
      calc ‖u - v‖ = ‖(u - z) - (v - z)‖ := by rw [this]
        _ ≤ ‖u - z‖ + ‖v - z‖ := norm_sub_le _ _
        _ ≤ 2 * ‖v - z‖ := by linarith
    by_cases hvz : 1 ≤ ‖v - z‖
    · have : m = 1 := min_eq_left hvz
      rw [this]; exact (min_le_left _ _).trans (by norm_num)
    · push Not at hvz
      have : m = ‖v - z‖ := min_eq_right hvz.le
      rw [this]; exact (min_le_right _ _).trans h1
  have hmpos : r / 2 ≤ m := by linarith
  have h2 : m ^ (-s82n_critS d) ≤ (r / 2) ^ (-s82n_critS d) :=
    s82n_rpow_neg_anti _ (r / 2) _ hs.le (by positivity) hmpos
  have h3 : (r / 2) ^ (-s82n_critS d) = 2 ^ s82n_critS d * r ^ (-s82n_critS d) := by
    rw [Real.div_rpow hrpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg hrpos.le]
    field_simp
  have h4 : (1 : ℝ) ≤ 2 ^ s82n_critS d := Real.one_le_rpow (by norm_num) hs.le
  have h5 : 0 ≤ r ^ (-s82n_critS d) := Real.rpow_nonneg hrpos.le _
  unfold s82n_pole
  calc 1 + m ^ (-s82n_critS d) ≤ 1 + 2 ^ s82n_critS d * r ^ (-s82n_critS d) := by linarith
    _ ≤ 2 ^ s82n_critS d * (1 + r ^ (-s82n_critS d)) := by nlinarith

lemma s82p_triplePole_le (hd : 1 ≤ d) (x y z : Euc d) (hxy : x ≠ y) :
    s82p_triplePole x y z ≤
      (1 + 2 ^ s82n_critS d) * s82n_pole x y * (s82n_pole x z + s82n_pole y z) := by
  have ha := s82p_pole_ge_one x z
  have hb := s82p_pole_ge_one y z
  have hP := s82p_pole_ge_one x y
  have h2 : (1 : ℝ) ≤ 2 ^ s82n_critS d := Real.one_le_rpow (by norm_num) (s82n_critS_pos hd).le
  have key : s82n_pole x z * s82n_pole y z ≤
      2 ^ s82n_critS d * s82n_pole x y * (s82n_pole x z + s82n_pole y z) := by
    rcases le_total ‖x - z‖ ‖y - z‖ with h | h
    · have := s82p_pole_cross hd x y z hxy h
      calc s82n_pole x z * s82n_pole y z ≤ s82n_pole x z * (2 ^ s82n_critS d * s82n_pole x y) := by
            gcongr
        _ ≤ 2 ^ s82n_critS d * s82n_pole x y * (s82n_pole x z + s82n_pole y z) := by
            have : 0 ≤ 2 ^ s82n_critS d * s82n_pole x y := by positivity
            nlinarith
    · have := s82p_pole_cross hd y x z hxy.symm h
      rw [s82p_pole_symm x y] at this
      calc s82n_pole x z * s82n_pole y z ≤ (2 ^ s82n_critS d * s82n_pole x y) * s82n_pole y z := by
            gcongr
        _ ≤ 2 ^ s82n_critS d * s82n_pole x y * (s82n_pole x z + s82n_pole y z) := by
            have : 0 ≤ 2 ^ s82n_critS d * s82n_pole x y := by positivity
            nlinarith
  unfold s82p_triplePole
  nlinarith

/-- A bound `q(w) ≤ K1 · (1 + min(1,|w|)^{-s})` for `w ≠ 0`. -/
lemma s82p_q_le {q : Euc d → ℝ} (hq : S82nShortRangePole d q) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ ∀ w : Euc d, w ≠ 0 →
      q w ≤ K1 * (1 + (min 1 ‖w‖) ^ (-s82n_critS d)) := by
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  obtain ⟨r1, c1, C1, hr1p, hc1, hfar⟩ := hq.far
  have hcomp : IsCompact {w : Euc d | r0 ≤ ‖w‖ ∧ ‖w‖ ≤ r1} := by
    have : {w : Euc d | r0 ≤ ‖w‖ ∧ ‖w‖ ≤ r1} = Metric.closedBall (0 : Euc d) r1 ∩ {w | r0 ≤ ‖w‖} := by
      ext w; simp [and_comm]
    rw [this]
    exact (isCompact_closedBall 0 r1).inter_right (isClosed_le continuous_const continuous_norm)
  have hcont : ContinuousOn q {w : Euc d | r0 ≤ ‖w‖ ∧ ‖w‖ ≤ r1} :=
    hq.smooth.continuousOn.mono fun w hw => by
      have : 0 < ‖w‖ := lt_of_lt_of_le hr0 hw.1
      exact norm_pos_iff.1 this
  obtain ⟨Cb, hCb⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max C0 0 + max C1 0 + max Cb 0, by positivity, ?_⟩
  intro w hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hP : 1 ≤ 1 + (min 1 ‖w‖) ^ (-s82n_critS d) := by
    have : 0 ≤ (min 1 ‖w‖) ^ (-s82n_critS d) := Real.rpow_nonneg (le_min zero_le_one hwpos.le) _
    linarith
  have hA : 0 ≤ max C0 0 := le_max_right _ _
  have hB : 0 ≤ max C1 0 := le_max_right _ _
  have hC : 0 ≤ max Cb 0 := le_max_right _ _
  by_cases h0 : ‖w‖ ≤ r0
  · have h1 := (hnear w hwpos h0).2
    have hm : min 1 ‖w‖ = ‖w‖ := min_eq_right (h0.trans hr1)
    rw [hm]
    have h2 : 0 ≤ ‖w‖ ^ (-s82n_critS d) := Real.rpow_nonneg hwpos.le _
    calc q w ≤ C0 * ‖w‖ ^ (-s82n_critS d) := h1
      _ ≤ max C0 0 * ‖w‖ ^ (-s82n_critS d) := by gcongr; exact le_max_left _ _
      _ ≤ (max C0 0 + max C1 0 + max Cb 0) * (1 + ‖w‖ ^ (-s82n_critS d)) := by
          have : 0 ≤ ‖w‖ ^ (-s82n_critS d) := h2
          nlinarith
  · push Not at h0
    have hq0 := hq.nonneg w
    have hb : q w ≤ max C1 0 + max Cb 0 := by
      by_cases h1 : r1 ≤ ‖w‖
      · have := hfar w h1
        have he : Real.exp (-c1 * ‖w‖ ^ 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖w‖]
        have : C1 * Real.exp (-c1 * ‖w‖ ^ 2) ≤ max C1 0 := by
          have hep := Real.exp_pos (-c1 * ‖w‖ ^ 2)
          rcases le_total C1 0 with hC1 | hC1
          · nlinarith [le_max_right C1 0]
          · calc C1 * Real.exp (-c1 * ‖w‖ ^ 2) ≤ C1 * 1 := by gcongr
              _ = C1 := mul_one _
              _ ≤ max C1 0 := le_max_left _ _
        linarith
      · push Not at h1
        have := hCb w ⟨h0.le, h1.le⟩
        rw [Real.norm_eq_abs] at this
        have := (le_abs_self (q w)).trans this
        have := this.trans (le_max_left Cb 0)
        linarith
    calc q w ≤ max C1 0 + max Cb 0 := hb
      _ ≤ (max C0 0 + max C1 0 + max Cb 0) * 1 := by linarith
      _ ≤ (max C0 0 + max C1 0 + max Cb 0) * (1 + (min 1 ‖w‖) ^ (-s82n_critS d)) := by
          gcongr

/-- Pure algebra of the pointwise domination. -/
lemma s82p_alg (K1 σ : ℝ) (hK1 : 0 ≤ K1) (hσ : 0 ≤ σ) (N : ℕ) (hN : 0 < N)
    (a b P T q1 q2 : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hP : 1 ≤ P)
    (hq1 : q1 ≤ K1 * a) (hq2 : q2 ≤ K1 * b) (hq1' : 0 ≤ q1) (hq2' : 0 ≤ q2)
    (hT : T ≤ σ * P * (a + b)) (hT0 : 0 ≤ T) :
    T * min 1 ((1 + q1 + q2) / N) ≤
      2 * σ * P * (s82p_psi (2 * (1 + K1)) N a + s82p_psi (2 * (1 + K1)) N b) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hK : 0 ≤ 2 * (1 + K1) := by positivity
  have hpa := s82p_psi_nonneg _ hK N (by linarith : 0 ≤ a)
  have hpb := s82p_psi_nonneg _ hK N (by linarith : 0 ≤ b)
  have hcap0 : 0 ≤ min 1 ((1 + q1 + q2) / (N : ℝ)) := le_min zero_le_one (by positivity)
  have hσP : 0 ≤ σ * P := mul_nonneg hσ (by linarith)
  -- generic step with the larger of the two
  have step : ∀ m : ℝ, 1 ≤ m → a ≤ m → b ≤ m →
      T * min 1 ((1 + q1 + q2) / N) ≤ 2 * σ * P * s82p_psi (2 * (1 + K1)) N m := by
    intro m hm ham hbm
    have h1 : (1 + q1 + q2) / N ≤ 2 * (1 + K1) * m / N := by
      gcongr
      nlinarith
    have h2 : min 1 ((1 + q1 + q2) / N) ≤ min 1 (2 * (1 + K1) * m / N) := min_le_min_left _ h1
    have h3 : T ≤ 2 * σ * P * m := by
      calc T ≤ σ * P * (a + b) := hT
        _ ≤ σ * P * (2 * m) := by gcongr; linarith
        _ = 2 * σ * P * m := by ring
    unfold s82p_psi
    calc T * min 1 ((1 + q1 + q2) / N) ≤ (2 * σ * P * m) * min 1 (2 * (1 + K1) * m / N) := by
          apply mul_le_mul h3 h2 hcap0 (by positivity)
      _ = 2 * σ * P * (m * min 1 (2 * (1 + K1) * m / N)) := by ring
  rcases le_total a b with h | h
  · have := step b hb h le_rfl
    nlinarith [mul_nonneg hσP hpa]
  · have := step a ha le_rfl h
    nlinarith [mul_nonneg hσP hpb]


lemma s82p_measurable_jb_psi (K : ℝ) (N : ℕ) (M : ℝ) (a : Euc d) :
    Measurable (fun z : Euc d => jbracket z ^ M * s82p_psi K N (s82n_pole a z)) := by
  refine Measurable.mul ?_ (s82p_measurable_psi_pole K N a)
  exact Measurable.pow_const (by unfold jbracket; fun_prop) _

/-- R04, `weighted_pin_product` (Pro `S82.R04`), with `M' = M`. -/
theorem s82p_weighted_pin_product (hd : 2 ≤ d) (M G c : ℝ) (hM : 0 ≤ M) (hG : 0 < G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : S82nShortRangePole d q) :
    ∃ C M' : ℝ, 0 ≤ C ∧ M ≤ M' ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ x y : Euc d, x ≠ y →
        (∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (C * s82p_pairWeight M' x y * s82n_pole x y *
            (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) / N) := by
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  obtain ⟨K1, hK1, hqK⟩ := s82p_q_le hq
  have hK : 1 ≤ 2 * (1 + K1) := by linarith
  obtain ⟨C3, hC3, hanch⟩ := s82p_anchor hd M G c (2 * (1 + K1)) hM hG.le hc hK
  have hσ : 0 ≤ 1 + (2 : ℝ) ^ s82n_critS d := by positivity
  refine ⟨4 * (1 + (2 : ℝ) ^ s82n_critS d) * C3, M, by positivity, le_rfl, ?_⟩
  intro ρ hρ hρG N hN x y hxy
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hL1 : 1 ≤ s82n_logN N := by
    rw [s82n_logN_eq N (by omega)]; have := Real.log_nonneg hN1r; linarith
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  haveI : NullSingletonClass μ := by rw [hμ]; unfold HRS.Whole.withDensityReal; infer_instance
  set σ : ℝ := 1 + (2 : ℝ) ^ s82n_critS d with hσdef
  set P : ℝ := s82n_pole x y with hPdef
  have hP := s82p_pole_ge_one x y
  have hc2 : 0 ≤ 2 * σ * P := by positivity
  have hae : ∀ᵐ z ∂μ, z ≠ x ∧ z ≠ y :=
    (Measure.ae_ne μ x).and (Measure.ae_ne μ y)
  set Kc : ℝ := 2 * (1 + K1) with hKc
  have hpt : ∀ᵐ z ∂μ, ENNReal.ofReal (jbracket z ^ M * s82p_triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ≤
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole x z)) +
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole y z)) := by
    filter_upwards [hae] with z ⟨hzx, hzy⟩
    have hJ : 0 ≤ jbracket z ^ M := Real.rpow_nonneg (s82n_jb_pos z).le _
    have hxz : x - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzx)
    have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hq1 : q (x - z) ≤ K1 * s82n_pole x z := hqK _ hxz
    have hq2 : q (y - z) ≤ K1 * s82n_pole y z := hqK _ hyz
    have hT := s82p_triplePole_le (by omega) x y z hxy
    have hT0 : 0 ≤ s82p_triplePole x y z := by
      have := s82p_pole_ge_one x z; have := s82p_pole_ge_one y z
      unfold s82p_triplePole; positivity
    have halg := s82p_alg K1 σ hK1 hσ N (by omega) (s82n_pole x z) (s82n_pole y z) P
      (s82p_triplePole x y z) (q (x - z)) (q (y - z)) (s82p_pole_ge_one x z) (s82p_pole_ge_one y z)
      hP hq1 hq2 (hq.nonneg _) (hq.nonneg _) hT hT0
    rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add
      (mul_nonneg hc2 (mul_nonneg hJ (s82p_psi_nonneg _ (by positivity) N (by linarith [s82p_pole_ge_one x z]))))
      (mul_nonneg hc2 (mul_nonneg hJ (s82p_psi_nonneg _ (by positivity) N (by linarith [s82p_pole_ge_one y z]))))]
    refine ENNReal.ofReal_le_ofReal ?_
    calc jbracket z ^ M * s82p_triplePole x y z * min 1 ((1 + q (x - z) + q (y - z)) / N)
        = jbracket z ^ M * (s82p_triplePole x y z * min 1 ((1 + q (x - z) + q (y - z)) / N)) := by ring
      _ ≤ jbracket z ^ M * (2 * σ * P * (s82p_psi Kc N (s82n_pole x z) + s82p_psi Kc N (s82n_pole y z))) :=
          mul_le_mul_of_nonneg_left halg hJ
      _ = _ := by ring
  have hIx := (hanch ρ hρ hρG N hN x)
  have hIy := (hanch ρ hρ hρG N hN y)
  calc (∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂μ)
      ≤ ∫⁻ z, (ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole x z)) +
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole y z))) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * σ * P) * ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole x z)) ∂μ +
        ENNReal.ofReal (2 * σ * P) * ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole y z)) ∂μ := by
        rw [lintegral_add_left, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (ENNReal.measurable_ofReal.comp (s82p_measurable_jb_psi Kc N M x)).const_mul _
    _ ≤ ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (C3 * jbracket x ^ M * s82n_logN N / N) +
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (C3 * jbracket y ^ M * s82n_logN N / N) := by
        gcongr
    _ = ENNReal.ofReal (2 * σ * P * (C3 * jbracket x ^ M * s82n_logN N / N) +
        2 * σ * P * (C3 * jbracket y ^ M * s82n_logN N / N)) := by
        rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add]
        · exact mul_nonneg hc2 (by have := Real.rpow_nonneg (s82n_jb_pos x).le M; positivity)
        · exact mul_nonneg hc2 (by have := Real.rpow_nonneg (s82n_jb_pos y).le M; positivity)
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hjx : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s82n_jb_one_le x) hM
        have hjy : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s82n_jb_one_le y) hM
        have hlog : 0 ≤ |Real.log (s82n_smallRadius x y)| := abs_nonneg _
        unfold s82p_pairWeight
        have e : 2 * σ * P * (C3 * jbracket x ^ M * s82n_logN N / N) +
            2 * σ * P * (C3 * jbracket y ^ M * s82n_logN N / N) =
            (2 * σ * P * C3 * s82n_logN N / N) * (jbracket x ^ M + jbracket y ^ M) := by ring
        rw [e]
        have e2 : 4 * σ * C3 * (jbracket x ^ M * jbracket y ^ M) * P *
            (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) / N =
            (2 * σ * P * C3 * (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) / N) *
              (2 * (jbracket x ^ M * jbracket y ^ M)) := by ring
        have h4 : 4 * (1 + (2 : ℝ) ^ s82n_critS d) * C3 = 4 * σ * C3 := by rw [hσdef]
        rw [h4, e2]
        have hA : 0 ≤ 2 * σ * P * C3 / N := by positivity
        have hB : s82n_logN N ≤ s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)| := by linarith
        have hC : jbracket x ^ M + jbracket y ^ M ≤ 2 * (jbracket x ^ M * jbracket y ^ M) := by
          nlinarith
        have hD : 0 ≤ jbracket x ^ M + jbracket y ^ M := by linarith
        calc 2 * σ * P * C3 * s82n_logN N / N * (jbracket x ^ M + jbracket y ^ M)
            = (2 * σ * P * C3 / N) * s82n_logN N * (jbracket x ^ M + jbracket y ^ M) := by ring
          _ ≤ (2 * σ * P * C3 / N) * (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) *
              (2 * (jbracket x ^ M * jbracket y ^ M)) := by
              gcongr
          _ = _ := by ring

end HRS.MS.S82P
