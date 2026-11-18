import HRS.MS.WadAux55

/-!
# S8.3, packet S8D-2, part 2: `s8d_force_decay`

For `ρ` with Gaussian bounds, the force `D = convGradConvW (∇g_{d/2}) ρ` satisfies `D(x) → 0` as `‖x‖ → ∞`.
Pointwise bound of the integrand after the substitution `y = x - z`, in three regions:
`‖z‖ ≤ 1/4` (Lipschitz bound of `ρ` near `x`, size `e^{-c(‖x‖-1/4)²}`), `1/4 < ‖z‖ ≤ ‖x‖/2`
(then `‖x-z‖ ≥ ‖x‖/2`: tail of `ρ`), `‖z‖ > ‖x‖/2` (kernel `≤ (‖x‖/2)^{-s-1}`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s8d_force_decay (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ →
      ‖convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x‖ ≤ η := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hρd, C, c, hC0, hc, hρb⟩ := hρ
  set s : ℝ := (d : ℝ) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsd : s < (d : ℝ) := by rw [hs]; linarith
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := (d : ℝ) + 1) (c := c) (by positivity) hc
  set W : Euc d → ℝ := fun y => (1 + ‖y‖) ^ (-((d : ℝ) + 1)) with hW
  have hW0 : ∀ y, 0 ≤ W y := fun y => Real.rpow_nonneg (by positivity) _
  have hρA : ∀ y, |ρ y| ≤ (C * KB) * W y := fun y => by
    refine ((hρb y).1).trans ?_
    have h1 := hKB y
    have hp : 0 < 1 + ‖y‖ := by positivity
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hp _
    have h2 : Real.exp (-c * ‖y‖ ^ 2) ≤ KB * W y := by
      rw [hW]; simp only
      rw [Real.rpow_neg hp.le, ← div_eq_mul_inv, le_div_iff₀ hq]
      linarith [mul_comm (Real.exp (-c * ‖y‖ ^ 2)) ((1 + ‖y‖) ^ ((d : ℝ) + 1))]
    calc C * Real.exp (-c * ‖y‖ ^ 2) ≤ C * (KB * W y) := mul_le_mul_of_nonneg_left h2 hC0
      _ = _ := by ring
  set A : ℝ := C * KB with hA
  have hA0 : 0 ≤ A := mul_nonneg hC0 hKB0
  set I₀ : ℝ := ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-s) with hI₀
  have hint0 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (ball (0 : Euc d) 1) volume :=
    ult_ball_int hd1 hs0.le hsd
  have hI₀0 : 0 ≤ I₀ := setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
  set IW : ℝ := ∫ y : Euc d, W y with hIW
  have hIW0 : 0 ≤ IW := integral_nonneg hW0
  have hWi : Integrable W volume := s84_int_far d
  -- the three vanishing terms, as functions of `r = ‖x‖`
  set T : ℝ → ℝ := fun r => s * (C * Real.exp (-c * (r - 1 / 4) ^ 2)) * I₀ +
    s * 4 ^ (s + 1) * A * (∫ y : Euc d, (if r / 2 ≤ ‖y‖ then W y else 0)) +
    s * (r / 2) ^ (-s - 1) * A * IW with hT
  have hT0 : Tendsto T atTop (𝓝 0) := by
    have e1 : Tendsto (fun r : ℝ => s * (C * Real.exp (-c * (r - 1 / 4) ^ 2)) * I₀) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => -c * (r - 1 / 4) ^ 2) atTop atBot := by
        refine tendsto_atBot.2 fun b => ?_
        filter_upwards [eventually_ge_atTop (1 / 4 + Real.sqrt (|b| / c + 1))] with r hr
        have h2 : Real.sqrt (|b| / c + 1) ≤ r - 1 / 4 := by linarith
        have h3 : |b| / c + 1 ≤ (r - 1 / 4) ^ 2 := by
          have := Real.sq_sqrt (show 0 ≤ |b| / c + 1 by positivity)
          nlinarith [Real.sqrt_nonneg (|b| / c + 1)]
        have h4 : |b| ≤ c * (r - 1 / 4) ^ 2 := by
          have := (div_le_iff₀ hc).1 (by linarith : |b| / c ≤ (r - 1 / 4) ^ 2)
          linarith
        nlinarith [neg_abs_le b]
      have h2 := Real.tendsto_exp_atBot.comp h1
      simpa using ((h2.const_mul C).const_mul s).mul_const I₀
    have e2 : Tendsto (fun r : ℝ => s * 4 ^ (s + 1) * A * (∫ y : Euc d, (if r / 2 ≤ ‖y‖ then W y else 0)))
        atTop (𝓝 0) := by
      have h := (s8d_tail_tendsto d).comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
      have h' := h.const_mul (s * 4 ^ (s + 1) * A)
      rw [mul_zero] at h'
      exact h'
    have e3 : Tendsto (fun r : ℝ => s * (r / 2) ^ (-s - 1) * A * IW) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => (r / 2) ^ (-s - 1)) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (show 0 < s + 1 by linarith)).comp
          (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
        refine this.congr fun r => ?_
        simp only [Function.comp, id]
        congr 1; ring
      have h3 := ((h1.const_mul s).mul_const A).mul_const IW
      rw [mul_zero, zero_mul, zero_mul] at h3
      exact h3
    simpa [hT] using (e1.add e2).add e3
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (hT0.eventually (gt_mem_nhds hη))
  refine ⟨max R₀ 1, fun x hx => ?_⟩
  have hxR : R₀ ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ ‖x‖ := (le_max_right _ _).trans hx
  refine le_of_lt (lt_of_le_of_lt ?_ (hR₀ ‖x‖ hxR))
  set Hx : ℝ := C * Real.exp (-c * (‖x‖ - 1 / 4) ^ 2) with hHx
  have hHx0 : 0 ≤ Hx := by positivity
  -- Lipschitz bound of `ρ` near `x`
  have hLip : ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → |ρ (x - z) - ρ x| ≤ Hx * ‖z‖ := by
    intro z hz
    have hbd : ∀ w ∈ closedBall x (1 / 4), ‖fderiv ℝ ρ w‖ ≤ Hx := by
      intro w hw
      rw [mem_closedBall_iff_norm'] at hw
      refine ((hρb w).2).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0
      have h1 : ‖x‖ - 1 / 4 ≤ ‖w‖ := by
        have := norm_sub_norm_le x w
        linarith
      have h2 : 0 ≤ ‖x‖ - 1 / 4 := by linarith
      nlinarith [mul_le_mul h1 h1 h2 (norm_nonneg w)]
    have hmv := (convex_closedBall x (1 / 4)).norm_image_sub_le_of_norm_fderiv_le
      (f := ρ) (C := Hx) (fun w _ => hρd w) hbd
      (mem_closedBall_self (by norm_num)) (show x - z ∈ closedBall x (1 / 4) by
        rw [mem_closedBall_iff_norm]; rw [sub_sub_cancel_left x z, norm_neg]; exact hz)
    rw [Real.norm_eq_abs, sub_sub_cancel_left x z, norm_neg] at hmv
    exact hmv
  -- the dominating function (in the variable `z = x - y`)
  set g1 : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (fun z => s * Hx * ‖z‖ ^ (-s)) with hg1
  set g2 : Euc d → ℝ := fun z => s * 4 ^ (s + 1) * A * (if ‖x‖ / 2 ≤ ‖x - z‖ then W (x - z) else 0) with hg2
  set g3 : Euc d → ℝ := fun z => s * (‖x‖ / 2) ^ (-s - 1) * A * W (x - z) with hg3
  have hg1i : Integrable g1 volume :=
    (integrable_indicator_iff measurableSet_ball).2 (hint0.const_mul (s * Hx))
  have hg2i : Integrable g2 volume := by
    have h0 : Integrable (fun y : Euc d => if ‖x‖ / 2 ≤ ‖y‖ then W y else 0) volume := by
      refine hWi.mono' ?_ (Eventually.of_forall fun y => ?_)
      · refine Measurable.aestronglyMeasurable ?_
        refine Measurable.ite (measurableSet_le measurable_const measurable_norm) ?_ measurable_const
        exact (by fun_prop : Measurable fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
      · by_cases h : ‖x‖ / 2 ≤ ‖y‖
        · simp only [h, ↓reduceIte, Real.norm_eq_abs]; exact le_of_eq (abs_of_nonneg (hW0 y))
        · simp only [h, ↓reduceIte, norm_zero]; exact hW0 y
    exact (h0.comp_sub_left x).const_mul _
  have hg3i : Integrable g3 volume := ((hWi.comp_sub_left x).const_mul _)
  have hg10 : ∀ z, 0 ≤ g1 z := fun z => by
    rw [hg1]
    refine Set.indicator_nonneg (fun z _ => ?_) z
    exact mul_nonneg (mul_nonneg hs0.le hHx0) (Real.rpow_nonneg (norm_nonneg _) _)
  have hg20 : ∀ z, 0 ≤ g2 z := fun z => by
    rw [hg2]; simp only
    split_ifs
    · exact mul_nonneg (by positivity) (hW0 _)
    · simp
  have hg30 : ∀ z, 0 ≤ g3 z := fun z => by
    rw [hg3]; exact mul_nonneg (by positivity) (hW0 _)
  have hnorm : ‖convGradConvW (rieszKernelGrad d s) ρ x‖ ≤ ∫ z, (g1 z + g2 z + g3 z) := by
    unfold convGradConvW
    rw [← integral_sub_left_eq_self _ volume x]
    refine norm_integral_le_of_norm_le ((hg1i.add hg2i).add hg3i) ?_
    filter_upwards [u2_ae_ne_zero hd1] with z hz
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hGn : ‖rieszKernelGrad d s z‖ = s * ‖z‖ ^ (-s - 1) := by
      rw [movtr_rieszKernelGrad_norm s hs0.le hz]
      unfold movtr_sigma
      simp [hs0.ne']
    simp only [sub_sub_cancel]
    by_cases hzn : ‖z‖ ≤ 1 / 4
    · rw [if_pos hzn, norm_smul, hGn, Real.norm_eq_abs]
      have hn : g1 z = s * Hx * ‖z‖ ^ (-s) := by
        rw [hg1, Set.indicator_of_mem]
        rw [mem_ball_zero_iff]; linarith
      have h1 : |ρ (x - z) - ρ x| * (s * ‖z‖ ^ (-s - 1)) ≤ s * Hx * ‖z‖ ^ (-s) := by
        calc |ρ (x - z) - ρ x| * (s * ‖z‖ ^ (-s - 1)) ≤ (Hx * ‖z‖) * (s * ‖z‖ ^ (-s - 1)) :=
              mul_le_mul_of_nonneg_right (hLip z hzn) (by positivity)
          _ = s * Hx * (‖z‖ * ‖z‖ ^ (-s - 1)) := by ring
          _ = s * Hx * ‖z‖ ^ (-s) := by
              congr 1
              calc ‖z‖ * ‖z‖ ^ (-s - 1) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (-s - 1) := by rw [Real.rpow_one]
                _ = ‖z‖ ^ (1 + (-s - 1)) := (Real.rpow_add hzp _ _).symm
                _ = ‖z‖ ^ (-s) := by congr 1; ring
      have := hg20 z
      have := hg30 z
      linarith
    · push Not at hzn
      rw [if_neg (not_le.2 hzn), norm_smul, hGn, Real.norm_eq_abs]
      have hg1n := hg10 z
      by_cases hzx : ‖z‖ ≤ ‖x‖ / 2
      · -- middle region: `‖x - z‖ ≥ ‖x‖/2`
        have hyz : ‖x‖ / 2 ≤ ‖x - z‖ := by
          have := norm_sub_norm_le x z
          linarith
        have h2 : ‖z‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
          have : ‖z‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hzn.le (by linarith)
          refine this.trans (le_of_eq ?_)
          rw [show (-s - 1) = -(s + 1) by ring, Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num),
            inv_inv]
        have hg2z : g2 z = s * 4 ^ (s + 1) * A * W (x - z) := by
          rw [hg2]; simp only [if_pos hyz]
        have := hg30 z
        calc |ρ (x - z)| * (s * ‖z‖ ^ (-s - 1)) ≤ (A * W (x - z)) * (s * 4 ^ (s + 1)) :=
              mul_le_mul (hρA (x - z)) (mul_le_mul_of_nonneg_left h2 hs0.le) (by positivity)
                (mul_nonneg hA0 (hW0 _))
          _ = g2 z := by rw [hg2z]; ring
          _ ≤ g1 z + g2 z + g3 z := by linarith
      · push Not at hzx
        have hxp : 0 < ‖x‖ / 2 := by linarith
        have h2 : ‖z‖ ^ (-s - 1) ≤ (‖x‖ / 2) ^ (-s - 1) :=
          Real.rpow_le_rpow_of_nonpos hxp hzx.le (by linarith)
        have := hg20 z
        calc |ρ (x - z)| * (s * ‖z‖ ^ (-s - 1)) ≤ (A * W (x - z)) * (s * (‖x‖ / 2) ^ (-s - 1)) :=
              mul_le_mul (hρA (x - z)) (mul_le_mul_of_nonneg_left h2 hs0.le) (by positivity)
                (mul_nonneg hA0 (hW0 _))
          _ = g3 z := by rw [hg3]; ring
          _ ≤ g1 z + g2 z + g3 z := by linarith
  refine hnorm.trans ?_
  rw [integral_add (f := fun z => g1 z + g2 z) (g := g3) (hg1i.add hg2i) hg3i, integral_add hg1i hg2i]
  have e1 : ∫ z, g1 z = s * Hx * I₀ := by
    rw [hg1, integral_indicator measurableSet_ball, integral_const_mul]
  have e2 : ∫ z, g2 z = s * 4 ^ (s + 1) * A * (∫ y : Euc d, (if ‖x‖ / 2 ≤ ‖y‖ then W y else 0)) := by
    rw [hg2, integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun y : Euc d => if ‖x‖ / 2 ≤ ‖y‖ then W y else 0) volume x
  have e3 : ∫ z, g3 z = s * (‖x‖ / 2) ^ (-s - 1) * A * IW := by
    rw [hg3, integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self W volume x
  rw [e1, e2, e3, hT]

end HRS.MS.Wad
