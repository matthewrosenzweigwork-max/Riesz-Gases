import HRS.MS.QprepAux2

/-!
# S4.6 packet A3: ingredients of the tilted Gibbs integration by parts

* `s46_theta`: smooth cutoff `θ = 1` on `(-∞,1]`, `θ = 0` on `[2,∞)`, with a bound on its derivative;
* `s46_w0_le`, `s46_pair_w0`: the weight `e^{-γ H_{a'}}` and the weighted pair term at the TRUE kernel (`ε = 0`), off the
  collision set, as limits of the uniform-in-`ε` bounds `s45_w_le`, `s45_pair_w_le`;
* `s46_dom_integrable`: `(1+‖X‖) e^{L‖X‖} e^{-c‖X‖²}` is integrable.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-! ### The cutoff -/

/-- `θ(t) = 1` for `t ≤ 1`, `θ(t) = 0` for `t ≥ 2`. -/
def s46_theta (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem s46_theta_contDiff : ContDiff ℝ ∞ s46_theta :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem s46_theta_one {t : ℝ} (h : t ≤ 1) : s46_theta t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem s46_theta_zero {t : ℝ} (h : 2 ≤ t) : s46_theta t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem s46_theta_nonneg (t : ℝ) : 0 ≤ s46_theta t := Real.smoothTransition.nonneg _

theorem s46_theta_le_one (t : ℝ) : s46_theta t ≤ 1 := Real.smoothTransition.le_one _

theorem s46_deriv_theta_zero {t : ℝ} (h : 2 < t) : deriv s46_theta t = 0 := by
  have : s46_theta =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds h] with u hu
    exact s46_theta_zero (le_of_lt hu)
  rw [this.deriv_eq]; simp

theorem s46_deriv_theta_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ t, |deriv s46_theta t| ≤ D := by
  have hc : Continuous (deriv s46_theta) := by
    have := s46_theta_contDiff.continuous_deriv (by simp)
    exact this
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ≤ 2
  · by_cases ht0 : 0 ≤ t
    · have := hD t ⟨ht0, ht⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · push Not at ht0
      have : s46_theta =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds ht0] with u hu
        have hu' : u < 0 := hu
        exact s46_theta_one (by linarith)
      rw [this.deriv_eq]; simp
  · push Not at ht
    rw [s46_deriv_theta_zero ht]; simp

/-! ### The weight and the pair term at `ε = 0` -/

theorem s46_cont_gEps {s : ℝ} (X : EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) (i j : Fin N)
    (hij : i ≠ j) : Continuous fun ε : ℝ => movtr_gEps d s ε (X i - X j) := by
  have hz : X i - X j ≠ 0 := sub_ne_zero.2 (hX i j hij)
  have hz0 : 0 < ‖X i - X j‖ := norm_pos_iff.2 hz
  unfold movtr_gEps
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    have hb : Continuous fun ε : ℝ => ‖X i - X j‖ ^ 2 + ε ^ 2 := by fun_prop
    refine continuous_const.mul (hb.log fun ε => ?_)
    positivity
  · simp only [hs, ite_false]
    have hb : Continuous fun ε : ℝ => ‖X i - X j‖ ^ 2 + ε ^ 2 := by fun_prop
    exact hb.rpow_const fun ε => Or.inl (by positivity)

theorem s46_cont_w {s a β : ℝ} (X : EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    Continuous fun ε : ℝ => S45.s45_w s a β ε X := by
  unfold S45.s45_w S45.s45_H
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_const.add (continuous_const.mul ?_)))
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j hj => ?_
  have : i < j := by simpa using hj
  exact s46_cont_gEps X hX i j this.ne

theorem s46_cont_F {s : ℝ} (X : EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) (i j : Fin N)
    (hij : i ≠ j) : Continuous fun ε : ℝ => S45.s45_F s ε (X i - X j) := by
  have hz : X i - X j ≠ 0 := sub_ne_zero.2 (hX i j hij)
  have hz0 : 0 < ‖X i - X j‖ := norm_pos_iff.2 hz
  unfold S45.s45_F
  refine Continuous.smul (f := fun ε : ℝ => -(movtr_sigma s * (‖X i - X j‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)))
    (g := fun _ => X i - X j) ?_ continuous_const
  refine (continuous_const.mul ?_).neg
  have hb : Continuous fun ε : ℝ => ‖X i - X j‖ ^ 2 + ε ^ 2 := by fun_prop
  exact hb.rpow_const fun ε => Or.inl (by positivity)

/-- The weight at the true kernel. -/
theorem s46_w0_le {s : ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ X : EucConfig d N, (∀ i j, i ≠ j → X i ≠ X j) →
      Real.exp (-β * canonicalHamiltonian (rieszKernel d s) (confinement a) X) ≤
        Cw * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by
  obtain ⟨Cw, hCw0, hCw⟩ := S45.s45_w_le (d := d) (N := N) (s := s) ha hβ hN
  refine ⟨Cw, hCw0, fun X hX => ?_⟩
  rw [← S45.s45_w_zero]
  have hc := s46_cont_w (s := s) (a := a) (β := β) X hX
  have hlim : Tendsto (fun ε : ℝ => S45.s45_w s a β ε X) (𝓝[>] 0) (𝓝 (S45.s45_w s a β 0 X)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  exact hCw ε hε.1 hε.2 X

/-- The weighted pair term at the true kernel. -/
theorem s46_pair_w0 {s : ℝ} (hs0 : 0 ≤ s) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N)
    {L : ℝ} (hL0 : 0 ≤ L) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ X : EucConfig d N, (∀ i j, i ≠ j → X i ≠ X j) → ∀ i j : Fin N, i < j →
      ∀ w : Euc d, ‖w‖ ≤ L * ‖X i - X j‖ →
        Real.exp (-β * canonicalHamiltonian (rieszKernel d s) (confinement a) X) *
          |⟪rieszKernelGrad d s (X i - X j), w⟫| ≤ CP * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by
  obtain ⟨CP, hCP0, hCP⟩ := S45.s45_pair_w_le (d := d) (N := N) hs0 ha hβ hN hL0
  refine ⟨CP, hCP0, fun X hX i j hij w hw => ?_⟩
  have hz : X i - X j ≠ 0 := sub_ne_zero.2 (hX i j hij.ne)
  rw [← S45.s45_w_zero, ← S45.s45_F_zero hz]
  have hc : Continuous fun ε : ℝ => S45.s45_w s a β ε X * |⟪S45.s45_F s ε (X i - X j), w⟫| :=
    (s46_cont_w X hX).mul ((((s46_cont_F X hX i j hij.ne).inner continuous_const)).abs)
  have hlim := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (a := 0))
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  exact hCP ε hε.1 hε.2 X i j hij w hw

/-! ### An integrable majorant -/

theorem s46_dom_integrable {c₁ : ℝ} (hc : 0 < c₁) (L K : ℝ) (hK : 0 ≤ K) :
    Integrable (fun X : EucConfig d N =>
      K * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-(c₁ * ‖X‖ ^ 2))) := by
  have hL : 0 ≤ |L| := abs_nonneg _
  refine S45.s45_integrable_of_dom (c := c₁ / 2) (half_pos hc) (K := K * Real.exp (|L| ^ 2 / (2 * c₁)))
    ?_ (by positivity) fun X => ?_
  · have : Continuous fun X : EucConfig d N =>
        K * (1 + ‖X‖) * Real.exp (L * ‖X‖) * Real.exp (-(c₁ * ‖X‖ ^ 2)) := by fun_prop
    exact this.aestronglyMeasurable
  · set t := ‖X‖ with ht
    have ht0 : 0 ≤ t := norm_nonneg _
    have h1 : L * t - c₁ * t ^ 2 ≤ |L| ^ 2 / (2 * c₁) - (c₁ / 2) * t ^ 2 := by
      have : L * t ≤ |L| * t := mul_le_mul_of_nonneg_right (le_abs_self L) ht0
      have h2 : |L| * t ≤ |L| ^ 2 / (2 * c₁) + (c₁ / 2) * t ^ 2 := by
        have : 0 ≤ (|L| - c₁ * t) ^ 2 := sq_nonneg _
        have e : (|L| - c₁ * t) ^ 2 = |L| ^ 2 - 2 * c₁ * (|L| * t) + c₁ ^ 2 * t ^ 2 := by ring
        have hc2 : 0 < 2 * c₁ := by positivity
        rw [div_add' _ _ _ hc2.ne', le_div_iff₀ hc2]
        nlinarith
      linarith
    have h3 : Real.exp (L * t) * Real.exp (-(c₁ * t ^ 2)) ≤
        Real.exp (|L| ^ 2 / (2 * c₁)) * Real.exp (-((c₁ / 2) * t ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hKn : 0 ≤ K * (1 + t) := by positivity
    rw [abs_of_nonneg (by positivity)]
    calc K * (1 + t) * Real.exp (L * t) * Real.exp (-(c₁ * t ^ 2))
        = K * (1 + t) * (Real.exp (L * t) * Real.exp (-(c₁ * t ^ 2))) := by ring
      _ ≤ K * (1 + t) * (Real.exp (|L| ^ 2 / (2 * c₁)) * Real.exp (-((c₁ / 2) * t ^ 2))) :=
          mul_le_mul_of_nonneg_left h3 hKn
      _ = K * Real.exp (|L| ^ 2 / (2 * c₁)) * (1 + t) * Real.exp (-((c₁ / 2) * t ^ 2)) := by ring

end S46

end
