import HRS.MS.CritForceMom1
import HRS.Whole.Round2

/-!
# S8.2 NormalForm packet R03, part 2: weights, Gaussian moments, polar coordinates

* `jbracket` comparison (Peetre type) `⟨y⟩ ≤ 2⟨x⟩⟨x-y⟩`;
* finiteness of the Gaussian-weighted polynomial moment `∫ G e^{-c|y|²} ⟨y⟩^M`;
* the polar-coordinate upper bound for a radial integrand on a ball.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

lemma s82n_jb_pos (x : Euc d) : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)

lemma s82n_jb_sq (x : Euc d) : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma s82n_jb_one_le (x : Euc d) : 1 ≤ jbracket x := by
  have h := s82n_jb_pos x
  nlinarith [s82n_jb_sq x, sq_nonneg ‖x‖]

lemma s82n_jb_peetre (x y : Euc d) : jbracket y ≤ 2 * jbracket x * jbracket (x - y) := by
  have hx := s82n_jb_pos x
  have hxy := s82n_jb_pos (x - y)
  have h1 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have := norm_sub_le x (x - y)
    simpa using this
  have h2 : ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖x - y‖), norm_nonneg y, norm_nonneg x, norm_nonneg (x - y)]
  have h3 : jbracket y ^ 2 ≤ (2 * jbracket x * jbracket (x - y)) ^ 2 := by
    rw [s82n_jb_sq, mul_pow, mul_pow, s82n_jb_sq, s82n_jb_sq]
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖x - y‖, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖x - y‖)]
  exact le_of_sq_le_sq h3 (by positivity)

lemma s82n_jb_near (x y : Euc d) (h : ‖x - y‖ ≤ 1) : jbracket y ≤ 4 * jbracket x := by
  have h1 := s82n_jb_peetre x y
  have h2 : jbracket (x - y) ≤ 2 := by
    have := s82n_jb_sq (x - y)
    have hp := s82n_jb_pos (x - y)
    nlinarith [norm_nonneg (x - y)]
  have hx := s82n_jb_pos x
  nlinarith

lemma s82n_jb_rpow_near (M : ℝ) (hM : 0 ≤ M) (x y : Euc d) (h : ‖x - y‖ ≤ 1) :
    jbracket y ^ M ≤ 4 ^ M * jbracket x ^ M := by
  rw [← Real.mul_rpow (by norm_num) (s82n_jb_pos x).le]
  exact Real.rpow_le_rpow (s82n_jb_pos y).le (s82n_jb_near x y h) hM

lemma s82n_one_add_rpow_le (M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ M ≤ 2 ^ M * (1 + r ^ M) := by
  have h2 : (0 : ℝ) ≤ 2 ^ M := Real.rpow_nonneg (by norm_num) _
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ M ≤ (2 : ℝ) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = 2 ^ M * 1 := by ring
      _ ≤ 2 ^ M * (1 + r ^ M) := by
        gcongr; linarith [Real.rpow_nonneg hr M]
  · calc (1 + r) ^ M ≤ (2 * r) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = 2 ^ M * r ^ M := Real.mul_rpow (by norm_num) hr
      _ ≤ 2 ^ M * (1 + r ^ M) := by gcongr; linarith

/-- The Gaussian-weighted polynomial moment is finite. -/
lemma s82n_gauss_moment (hd : 1 ≤ d) (M c : ℝ) (hM : 0 ≤ M) (hc : 0 < c) :
    Integrable (fun y : Euc d => Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have key := (integrable_fun_norm_addHaar (volume : Measure (Euc d))
    (f := fun r : ℝ => Real.exp (-c * r ^ 2) * (Real.sqrt (1 + r ^ 2)) ^ M)).2
  refine key ?_
  rw [finrank_euclideanSpace_fin]
  have hd1 : (-1 : ℝ) < ((d - 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hd2 : (-1 : ℝ) < ((d - 1 : ℕ) : ℝ) + M := by
    have : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have i1 := integrableOn_rpow_mul_exp_neg_mul_sq hc hd1
  have i2 := integrableOn_rpow_mul_exp_neg_mul_sq hc hd2
  have ig : IntegrableOn (fun r : ℝ => 2 ^ M * (r ^ ((d - 1 : ℕ) : ℝ) * Real.exp (-c * r ^ 2) +
      r ^ (((d - 1 : ℕ) : ℝ) + M) * Real.exp (-c * r ^ 2))) (Ioi 0) :=
    (i1.add i2).const_mul _
  refine ig.mono' ?_ ?_
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun r hr => ?_
    have hr' : 0 < r := hr
    have hs : Real.sqrt (1 + r ^ 2) ≤ 1 + r := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hs0 : 0 ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_nonneg _
    have h1 : (Real.sqrt (1 + r ^ 2)) ^ M ≤ 2 ^ M * (1 + r ^ M) :=
      (Real.rpow_le_rpow hs0 hs hM).trans (s82n_one_add_rpow_le M hM r hr'.le)
    have he : 0 ≤ Real.exp (-c * r ^ 2) := (Real.exp_pos _).le
    simp only [smul_eq_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have hp : r ^ (d - 1) = r ^ ((d - 1 : ℕ) : ℝ) := (Real.rpow_natCast r (d - 1)).symm
    have hq : r ^ (((d - 1 : ℕ) : ℝ) + M) = r ^ ((d - 1 : ℕ) : ℝ) * r ^ M :=
      Real.rpow_add hr' _ _
    rw [hp, hq]
    have hrp : 0 ≤ r ^ ((d - 1 : ℕ) : ℝ) := (Real.rpow_pos_of_pos hr' _).le
    calc r ^ ((d - 1 : ℕ) : ℝ) * (Real.exp (-c * r ^ 2) * Real.sqrt (1 + r ^ 2) ^ M)
        ≤ r ^ ((d - 1 : ℕ) : ℝ) * (Real.exp (-c * r ^ 2) * (2 ^ M * (1 + r ^ M))) := by gcongr
      _ = 2 ^ M * (r ^ ((d - 1 : ℕ) : ℝ) * Real.exp (-c * r ^ 2) +
          r ^ ((d - 1 : ℕ) : ℝ) * r ^ M * Real.exp (-c * r ^ 2)) := by ring

/-- Polar coordinates, upper bound: a radial nonnegative integrand on a ball whose radial profile
`r^{d-1} Ψ(r)` is dominated by an interval-integrable `g`. -/
lemma s82n_polar_ub (hd : 1 ≤ d) (r0 : ℝ) (hr0 : 0 < r0) (Ψ g : ℝ → ℝ)
    (hΨ0 : ∀ r, 0 ≤ r → 0 ≤ Ψ r) (hΨm : Measurable Ψ)
    (hg : IntervalIntegrable g volume 0 r0)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r0, r ^ (d - 1) * Ψ r ≤ g r) :
    ∫⁻ u in Metric.ball (0 : Euc d) r0, ENNReal.ofReal (Ψ ‖u‖) ≤
      ENNReal.ofReal ((d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) *
        ∫ r in (0 : ℝ)..r0, g r) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hgI : IntegrableOn g (Ioo 0 r0) := by
    have := hg.1
    exact this.mono_set (Ioo_subset_Ioc_self)
  have hint1 : IntegrableOn (fun r : ℝ => r ^ (d - 1) * Ψ r) (Ioo 0 r0) := by
    refine hgI.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun r : ℝ => r ^ (d - 1) * Ψ r).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun r hr => ?_
      have hr' : 0 < r := hr.1
      have h0 : 0 ≤ r ^ (d - 1) * Ψ r := mul_nonneg (by positivity) (hΨ0 r hr'.le)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle r hr
  have hint2 : IntegrableOn (fun x : Euc d => Ψ ‖x‖) (Metric.ball (0 : Euc d) r0) := by
    refine (integrableOn_fun_norm_addHaar (volume : Measure (Euc d)) (f := Ψ) (r := r0)).2 ?_
    rw [finrank_euclideanSpace_fin]
    simpa [smul_eq_mul] using hint1
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall fun u => hΨ0 _ (norm_nonneg u))]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcalc : ∫ x in Metric.ball (0 : Euc d) r0, Ψ ‖x‖ =
      (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) *
        ∫ r in Ioo (0 : ℝ) r0, r ^ (d - 1) * Ψ r := by
    have h := integral_fun_norm_addHaar (volume : Measure (Euc d)) ((Iio r0).indicator Ψ)
    rw [finrank_euclideanSpace_fin] at h
    have e1 : (fun x : Euc d => (Iio r0).indicator Ψ ‖x‖) =
        (Metric.ball (0 : Euc d) r0).indicator (fun x => Ψ ‖x‖) := by
      funext x
      by_cases hx : ‖x‖ < r0
      · rw [Set.indicator_of_mem (show ‖x‖ ∈ Iio r0 from hx),
          Set.indicator_of_mem (show x ∈ Metric.ball (0 : Euc d) r0 by simpa using hx)]
      · rw [Set.indicator_of_notMem (show ‖x‖ ∉ Iio r0 from hx),
          Set.indicator_of_notMem (show x ∉ Metric.ball (0 : Euc d) r0 by simpa using hx)]
    have e2 : ∀ y : ℝ, y ^ (d - 1) • (Iio r0).indicator Ψ y =
        (Iio r0).indicator (fun y => y ^ (d - 1) * Ψ y) y := by
      intro y
      by_cases hy : y < r0
      · rw [Set.indicator_of_mem (show y ∈ Iio r0 from hy),
          Set.indicator_of_mem (show y ∈ Iio r0 from hy), smul_eq_mul]
      · rw [Set.indicator_of_notMem (show y ∉ Iio r0 from hy),
          Set.indicator_of_notMem (show y ∉ Iio r0 from hy), smul_zero]
    rw [e1, integral_indicator Metric.isOpen_ball.measurableSet] at h
    simp only [e2] at h
    rw [h, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, nsmul_eq_mul, smul_eq_mul]
    ring
  rw [hcalc]
  have hκ : 0 ≤ (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) := by
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hκ
  have e : ∫ r in (0 : ℝ)..r0, g r = ∫ r in Ioo (0 : ℝ) r0, g r := by
    rw [intervalIntegral.integral_of_le hr0.le, integral_Ioc_eq_integral_Ioo]
  rw [e]
  exact setIntegral_mono_on hint1 hgI measurableSet_Ioo hle

end HRS.MS.S82N
