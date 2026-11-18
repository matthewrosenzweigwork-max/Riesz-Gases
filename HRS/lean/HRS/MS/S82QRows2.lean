import HRS.MS.S82QRows

/-!
# S8.2 (S82Q): weighted rows used by the nested triple moment, in the frozen `Phase2S82` vocabulary
For `triplePole x y z <= (1 + 2^s) pole x y (pole x z + pole y z)` (`s82p_triplePole_le`) and the frozen
R03 rows, with an arbitrary polynomial exponent `a`:
* `s82q_row_pole`: `int <z>^a pole x z dmu <= C <x>^a`;
* `s82q_row_triple`: `int <z>^a triplePole x y z dmu <= C (<x>^a + <y>^a) pole x y`;
* `s82q_row_triple_sq`: with the two-pin cutoff, the second moment is `C (<x>^a + <y>^a) pole x y ^ 2 logN N`;
* `s82q_row_triple_cap`: the capped row is `C (<x>^a + <y>^a) pole x y logN N / N` (sharp form of R04).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

lemma s82q_pole_ge_one {d : ℕ} (x z : Euc d) : 1 ≤ pole x z := by
  unfold pole smallRadius
  have : 0 ≤ (min 1 ‖x - z‖) ^ (-criticalS d) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
  linarith

lemma s82q_jb_rpow_nonneg {d : ℕ} (a : ℝ) (x : Euc d) : 0 ≤ jbracket x ^ a :=
  Real.rpow_nonneg (HRS.MS.S82N.s82n_jb_pos x).le _

lemma s82q_triple_le {d : ℕ} (hd : 2 ≤ d) (x y z : Euc d) (hxy : x ≠ y) :
    triplePole x y z ≤ (1 + 2 ^ criticalS d) * pole x y * (pole x z + pole y z) :=
  HRS.MS.S82P.s82p_triplePole_le (by omega) x y z hxy

lemma s82q_measurable_pole {d : ℕ} (x : Euc d) : Measurable (fun z : Euc d => pole x z) := by
  unfold pole smallRadius
  have : Measurable (fun z : Euc d => min 1 ‖x - z‖) :=
    measurable_const.min (measurable_const.sub measurable_id).norm
  exact measurable_const.add (this.pow_const _)

lemma s82q_measurable_jb {d : ℕ} (a : ℝ) : Measurable (fun z : Euc d => jbracket z ^ a) := by
  have : Measurable (fun x : Euc d => jbracket x) := by unfold jbracket; fun_prop
  exact this.pow_const _

lemma s82q_measurable_triplePole {d : ℕ} (x y : Euc d) :
    Measurable (fun z : Euc d => triplePole x y z) := by
  unfold triplePole
  have hx := s82q_measurable_pole x
  have hy := s82q_measurable_pole y
  exact ((measurable_const.mul hx).add (measurable_const.mul hy)).add (hx.mul hy)

theorem s82q_row_pole (d : ℕ) (hd : 2 ≤ d) (a G c : ℝ) (ha : 0 ≤ a) (hG : 0 < G) (hc : 0 < c)
    (beta : ℝ) (hbeta : 0 < beta) (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ x : Euc d, ∫⁻ z, ENNReal.ofReal (jbracket z ^ a * pole x z) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (C * jbracket x ^ a) := by
  obtain ⟨C, hC, h⟩ := weighted_radial_rows d hd beta a G c hbeta ha hG hc q hq
  refine ⟨C, hC, fun rho hρ hρG x => ?_⟩
  have h2 := (h rho hρ hρG 2 le_rfl x).2.1
  refine le_trans (lintegral_mono fun z => ?_) h2
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 ≤ 1 + smallRadius x z ^ (1 - criticalS d) := by
    have : 0 ≤ smallRadius x z ^ (1 - criticalS d) :=
      Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    linarith
  have hp := s82q_pole_ge_one x z
  have hj := s82q_jb_rpow_nonneg a z
  nlinarith [mul_nonneg hj (sub_nonneg.2 h1), mul_nonneg (mul_nonneg hj (sub_nonneg.2 h1)) (by linarith : (0 : ℝ) ≤ pole x z)]

lemma s82q_split2 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g h : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hg : Measurable g) (hh : Measurable h) (hg0 : ∀ z, 0 ≤ g z) (hh0 : ∀ z, 0 ≤ h z)
    (hf : ∀ᵐ z ∂μ, f z ≤ c * (g z + h z)) (B1 B2 : ℝ) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (h1 : ∫⁻ z, ENNReal.ofReal (g z) ∂μ ≤ ENNReal.ofReal B1)
    (h2 : ∫⁻ z, ENNReal.ofReal (h z) ∂μ ≤ ENNReal.ofReal B2) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂μ ≤ ENNReal.ofReal (c * (B1 + B2)) := by
  calc ∫⁻ z, ENNReal.ofReal (f z) ∂μ
      ≤ ∫⁻ z, (ENNReal.ofReal c * ENNReal.ofReal (g z) + ENNReal.ofReal c * ENNReal.ofReal (h z)) ∂μ := by
        refine lintegral_mono_ae (hf.mono fun z hz => ?_)
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hc,
          ← ENNReal.ofReal_add (mul_nonneg hc (hg0 z)) (mul_nonneg hc (hh0 z))]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (g z) ∂μ +
          ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (h z) ∂μ := by
        have hm : Measurable (fun z => ENNReal.ofReal c * ENNReal.ofReal (g z)) :=
          (ENNReal.measurable_ofReal.comp hg).const_mul _
        rw [lintegral_add_left hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal B1 + ENNReal.ofReal c * ENNReal.ofReal B2 := by gcongr
    _ = ENNReal.ofReal (c * (B1 + B2)) := by
        rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hc,
          ← ENNReal.ofReal_add (mul_nonneg hc hB1) (mul_nonneg hc hB2), mul_add]

theorem s82q_row_triple (d : ℕ) (hd : 2 ≤ d) (a G c : ℝ) (ha : 0 ≤ a) (hG : 0 < G) (hc : 0 < c)
    (beta : ℝ) (hbeta : 0 < beta) (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ x y : Euc d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal (jbracket z ^ a * triplePole x y z) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (C * (jbracket x ^ a + jbracket y ^ a) * pole x y) := by
  obtain ⟨C, hC, h⟩ := s82q_row_pole d hd a G c ha hG hc beta hbeta q hq
  have hσ : 0 ≤ 1 + (2 : ℝ) ^ criticalS d := by positivity
  refine ⟨(1 + 2 ^ criticalS d) * C, by positivity, fun rho hρ hρG x y hxy => ?_⟩
  have hP := s82q_pole_ge_one x y
  refine le_trans (s82q_split2 _ _ (fun z => jbracket z ^ a * pole x z)
    (fun z => jbracket z ^ a * pole y z) ((1 + 2 ^ criticalS d) * pole x y) (by positivity)
    ((s82q_measurable_jb a).mul (s82q_measurable_pole x))
    ((s82q_measurable_jb a).mul (s82q_measurable_pole y))
    (fun z => mul_nonneg (s82q_jb_rpow_nonneg a z) (by linarith [s82q_pole_ge_one x z]))
    (fun z => mul_nonneg (s82q_jb_rpow_nonneg a z) (by linarith [s82q_pole_ge_one y z]))
    (ae_of_all _ fun z => ?_) (C * jbracket x ^ a) (C * jbracket y ^ a)
    (mul_nonneg hC (s82q_jb_rpow_nonneg a x)) (mul_nonneg hC (s82q_jb_rpow_nonneg a y))
    (h rho hρ hρG x) (h rho hρ hρG y)) (le_of_eq ?_)
  · have := s82q_triple_le hd x y z hxy
    have hj := s82q_jb_rpow_nonneg a z
    calc jbracket z ^ a * triplePole x y z
        ≤ jbracket z ^ a * ((1 + 2 ^ criticalS d) * pole x y * (pole x z + pole y z)) :=
          mul_le_mul_of_nonneg_left this hj
      _ = _ := by ring
  · congr 1
    ring

theorem s82q_row_triple_sq (d : ℕ) (hd : 2 ≤ d) (a G c : ℝ) (ha : 0 ≤ a) (hG : 0 < G) (hc : 0 < c)
    (beta : ℝ) (hbeta : 0 < beta) (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ N : ℕ, 2 ≤ N → ∀ x y : Euc d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal (jbracket z ^ a * triplePole x y z ^ 2 *
          Real.exp (-(beta / N) * (q (z - y) + q (z - x)))) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (C * (jbracket x ^ a + jbracket y ^ a) * pole x y ^ 2 * logN N) := by
  obtain ⟨C, hC, h⟩ := weighted_radial_rows d hd beta a G c hbeta ha hG hc q hq
  have hσ : 0 ≤ 1 + (2 : ℝ) ^ criticalS d := by positivity
  refine ⟨2 * (1 + 2 ^ criticalS d) ^ 2 * C, by positivity, fun rho hρ hρG N hN x y hxy => ?_⟩
  have hP := s82q_pole_ge_one x y
  have hNr : (0 : ℝ) ≤ beta / N := div_nonneg hbeta.le (Nat.cast_nonneg _)
  have hq0 := hq.nonneg
  have hqe := hq.even
  have hL : 0 ≤ logN N := by
    unfold logN
    have : (1 : ℝ) ≤ Real.exp 1 * N := by
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact Real.log_nonneg this
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := h rho hρ hρG N hN x
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := h rho hρ hρG N hN y
  have cutx : ∀ z : Euc d, Real.exp (-(beta / N) * q (x - z)) = Real.exp (-(beta / N) * q (z - x)) := by
    intro z
    rw [show x - z = -(z - x) by abel, hqe]
  have cuty : ∀ z : Euc d, Real.exp (-(beta / N) * q (y - z)) = Real.exp (-(beta / N) * q (z - y)) := by
    intro z
    rw [show y - z = -(z - y) by abel, hqe]
  refine le_trans (s82q_split2 _ _
    (fun z => jbracket z ^ a * pole x z ^ 2 * Real.exp (-(beta / N) * q (x - z)))
    (fun z => jbracket z ^ a * pole y z ^ 2 * Real.exp (-(beta / N) * q (y - z)))
    (2 * (1 + 2 ^ criticalS d) ^ 2 * pole x y ^ 2) (by positivity) ?_ ?_ ?_ ?_
    (ae_of_all _ fun z => ?_) (C * jbracket x ^ a * logN N) (C * jbracket y ^ a * logN N)
    (mul_nonneg (mul_nonneg hC (s82q_jb_rpow_nonneg a x)) hL)
    (mul_nonneg (mul_nonneg hC (s82q_jb_rpow_nonneg a y)) hL) hx3 hy3) (le_of_eq ?_)
  · exact ((s82q_measurable_jb a).mul ((s82q_measurable_pole x).pow_const 2)).mul
      (Real.measurable_exp.comp (measurable_const.mul (hq.measurable.comp
        (measurable_const.sub measurable_id))))
  · exact ((s82q_measurable_jb a).mul ((s82q_measurable_pole y).pow_const 2)).mul
      (Real.measurable_exp.comp (measurable_const.mul (hq.measurable.comp
        (measurable_const.sub measurable_id))))
  · intro z
    exact mul_nonneg (mul_nonneg (s82q_jb_rpow_nonneg a z) (sq_nonneg _)) (Real.exp_pos _).le
  · intro z
    exact mul_nonneg (mul_nonneg (s82q_jb_rpow_nonneg a z) (sq_nonneg _)) (Real.exp_pos _).le
  · have hT := s82q_triple_le hd x y z hxy
    have hT0 : 0 ≤ triplePole x y z := by
      have := s82q_pole_ge_one x z; have := s82q_pole_ge_one y z
      unfold triplePole; positivity
    have hj := s82q_jb_rpow_nonneg a z
    have hxz := s82q_pole_ge_one x z
    have hyz := s82q_pole_ge_one y z
    set σ := 1 + (2 : ℝ) ^ criticalS d with hσdef
    have hT2 : triplePole x y z ^ 2 ≤ 2 * σ ^ 2 * pole x y ^ 2 * (pole x z ^ 2 + pole y z ^ 2) := by
      calc triplePole x y z ^ 2 ≤ (σ * pole x y * (pole x z + pole y z)) ^ 2 :=
            pow_le_pow_left₀ hT0 hT 2
        _ ≤ _ := by nlinarith [sq_nonneg (pole x z - pole y z), sq_nonneg (σ * pole x y)]
    have hcut : Real.exp (-(beta / N) * (q (z - y) + q (z - x))) ≤
        Real.exp (-(beta / N) * q (x - z)) ∧
        Real.exp (-(beta / N) * (q (z - y) + q (z - x))) ≤ Real.exp (-(beta / N) * q (y - z)) := by
      rw [cutx, cuty]
      constructor
      · refine Real.exp_le_exp.2 ?_
        nlinarith [mul_nonneg hNr (hq0 (z - y))]
      · refine Real.exp_le_exp.2 ?_
        nlinarith [mul_nonneg hNr (hq0 (z - x))]
    have hex := (Real.exp_pos (-(beta / N) * (q (z - y) + q (z - x)))).le
    calc jbracket z ^ a * triplePole x y z ^ 2 * Real.exp (-(beta / N) * (q (z - y) + q (z - x)))
        ≤ jbracket z ^ a * (2 * σ ^ 2 * pole x y ^ 2 * (pole x z ^ 2 + pole y z ^ 2)) *
            Real.exp (-(beta / N) * (q (z - y) + q (z - x))) := by gcongr
      _ = 2 * σ ^ 2 * pole x y ^ 2 * ((jbracket z ^ a * pole x z ^ 2 *
            Real.exp (-(beta / N) * (q (z - y) + q (z - x)))) +
            (jbracket z ^ a * pole y z ^ 2 * Real.exp (-(beta / N) * (q (z - y) + q (z - x))))) := by
          ring
      _ ≤ 2 * σ ^ 2 * pole x y ^ 2 * ((jbracket z ^ a * pole x z ^ 2 * Real.exp (-(beta / N) * q (x - z))) +
            (jbracket z ^ a * pole y z ^ 2 * Real.exp (-(beta / N) * q (y - z)))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
          · exact mul_le_mul_of_nonneg_left hcut.1 (mul_nonneg hj (sq_nonneg _))
          · exact mul_le_mul_of_nonneg_left hcut.2 (mul_nonneg hj (sq_nonneg _))
  · congr 1
    ring

theorem s82q_row_triple_cap (d : ℕ) (hd : 2 ≤ d) (a G c : ℝ) (ha : 0 ≤ a) (hG : 0 < G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ N : ℕ, 2 ≤ N → ∀ x y : Euc d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal (jbracket z ^ a * triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (C * (jbracket x ^ a + jbracket y ^ a) * pole x y * logN N / N) := by
  obtain ⟨C, hC, h⟩ := HRS.MS.S82P.s82q_pin_product_L hd a G c ha hG hc q (s82q_pole_bridge hq)
  exact ⟨C, hC, fun rho hρ hρG N hN x y hxy => h rho hρ hρG N hN x y hxy⟩

end HRS.MS.Phase2S82
