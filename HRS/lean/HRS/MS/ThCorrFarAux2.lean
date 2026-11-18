import HRS.MS.ThCorrFarAux1
import HRS.MS.ThCorrSobAux2

/-!
# TC-4 (part 2): splitting of `K` and the far convolution

Namespace `HRS.MS.TcF`.  `μ = HRS.Whole.withDensityReal ρ`, `g = rieszKernel d s`, `θ` a cutoff (`TcCutoff`).

* `farK d s θ μ f x = ∫ (1 - θ (x - y)) g (x - y) f y ∂μ`,
  `locK d s θ ρ f = convFun (θ g) (ρ f)`.
* `tc4_split_pt`: the pointwise identity `∫ g(x-y) f y dμ = locK f x + farK f x` for every `x` at which the
  integrand is `μ`-integrable (no hypothesis is needed beyond this; a bounded multiplier `θ` keeps both parts
  integrable).  `tc4_split`: for `f ∈ L²(μ)` (so `ρ f ∈ L¹`), the formula
  `Kop g μ f x = locK f x + farK f x - pair μ (locK f + farK f)` holds for Lebesgue-a.e. `x` (hence `μ`-a.e.).
  The "for every x" of the TeX sketch is false with the Bochner junk value `0` on the null set where the
  local part is not integrable; the a.e. form is what the a.e. response equation uses.
  (Adjustment: `ρ f ∈ L¹` is replaced by `f ∈ L²(μ)`, which is needed for the far part at `s = 0`.)
* `tc4_far`: `f ∈ L²_0(μ)` gives `farK f ∈ C_b^m` with `cbNorm m (farK f) ≤ C * ‖f‖_{L²(μ)}`,
  `C = C(d, s, θ, m, M₀, c)` independent of `ρ` and `S`.
* `tc4_loc_cb`: derivatives of `convFun (θ g) u` fall on `u ∈ C_b^J`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace HRS.MS.TcF

open HRS.Whole HRS.MS.TcDefs

variable {d : ℕ}

section Density

variable {ρ : Euc d → ℝ}

theorem tc4_integral_wd (hm : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x) (F : Euc d → ℝ) :
    ∫ y, F y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * F y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hm).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (h0 y)]

theorem tc4_isProb (h : HRS.Whole.IsProbDensity ρ) : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := by
  have hint : Integrable ρ := by
    by_contra hn
    have := h.integral_one
    rw [integral_undef hn] at this
    norm_num at this
  constructor
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall h.nonneg), h.integral_one]
  simp

theorem tc4_integrable_iff (h : HRS.Whole.IsProbDensity ρ) {F : Euc d → ℝ} :
    Integrable F (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun y => ρ y * F y) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp h.measurable)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (h.nonneg _), mul_comm (F _)]

theorem tc4_integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Euc d => Real.exp (-b * ‖v‖ ^ 2)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  have : 0 < Real.pi / b := by positivity
  exact (Real.rpow_pos_of_pos this _).ne'

theorem tc4_integrable_sq_gauss {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Euc d => ‖y‖ ^ 2 * Real.exp (-c * ‖y‖ ^ 2)) := by
  refine ((tc4_integrable_gauss (d := d) (half_pos hc)).const_mul (2 / c)).mono' ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · exact ((measurable_norm.pow_const 2).mul
      (Real.measurable_exp.comp (measurable_norm.pow_const 2 |>.const_mul (-c)))).aestronglyMeasurable
  · set r := ‖y‖ ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hu : c / 2 * r ≤ Real.exp (c / 2 * r) := by
      linarith [Real.add_one_le_exp (c / 2 * r)]
    have h1 : r * Real.exp (-(c / 2) * r) ≤ 2 / c := by
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have : r = 2 / c * (c / 2 * r) := by field_simp
      calc r = 2 / c * (c / 2 * r) := this
        _ ≤ 2 / c * Real.exp (c / 2 * r) := mul_le_mul_of_nonneg_left hu (by positivity)
    have h2 : Real.exp (-c * r) = Real.exp (-(c / 2) * r) * Real.exp (-(c / 2) * r) := by
      rw [← Real.exp_add]; ring_nf
    rw [Real.norm_of_nonneg (by positivity), h2, ← mul_assoc]
    calc r * Real.exp (-(c / 2) * r) * Real.exp (-(c / 2) * r)
        ≤ 2 / c * Real.exp (-(c / 2) * r) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = _ := by ring_nf

/-- The explicit bound `M₀ ∫ ‖y‖² e^{-c‖y‖²}` for the second moment of `ρ`. -/
def tc4_m2 (d : ℕ) (M₀ c : ℝ) : ℝ := M₀ * ∫ y : Euc d, ‖y‖ ^ 2 * Real.exp (-c * ‖y‖ ^ 2)

theorem tc4_sq_integrable {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) :
    Integrable (fun y : Euc d => ‖y‖ ^ 2) (HRS.Whole.withDensityReal ρ) := by
  rw [tc4_integrable_iff hρ.prob]
  refine ((tc4_integrable_sq_gauss (d := d) hc).const_mul M₀).mono' ?_
    (Filter.Eventually.of_forall fun y => ?_)
  · exact (hρ.prob.measurable.mul (measurable_norm.pow_const 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (hρ.prob.nonneg y) (by positivity))]
    calc ρ y * ‖y‖ ^ 2 ≤ (M₀ * Real.exp (-c * ‖y‖ ^ 2)) * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hρ.gauss y) (by positivity)
      _ = M₀ * (‖y‖ ^ 2 * Real.exp (-c * ‖y‖ ^ 2)) := by ring

theorem tc4_second_moment_le {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c) :
    ∫ y, ‖y‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ tc4_m2 d M₀ c := by
  rw [tc4_integral_wd hρ.prob.measurable hρ.prob.nonneg, tc4_m2, ← integral_const_mul]
  have hint := (tc4_integrable_iff hρ.prob).1 (tc4_sq_integrable hρ hc)
  refine integral_mono hint ((tc4_integrable_sq_gauss (d := d) hc).const_mul M₀) fun y => ?_
  calc ρ y * ‖y‖ ^ 2 ≤ (M₀ * Real.exp (-c * ‖y‖ ^ 2)) * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hρ.gauss y) (by positivity)
    _ = M₀ * (‖y‖ ^ 2 * Real.exp (-c * ‖y‖ ^ 2)) := by ring

end Density

section Far

variable {θ : Euc d → ℝ} {s : ℝ}

theorem tc4_cs {μ : Measure (Euc d)} {u v : Euc d → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∫ x, u x * v x ∂μ ≤ Real.sqrt (∫ x, u x ^ 2 ∂μ) * Real.sqrt (∫ x, v x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hu0) (Filter.Eventually.of_forall hv0)
    (by simpa using hu) (by simpa using hv)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h

theorem tc4_G_zero {θ : Euc d → ℝ} (h : TcCutoff θ) (s : ℝ) : tc4_G d s θ 0 = 0 := by
  simp [tc4_G, h.one_inside 0 (by simp)]

theorem tc4_memLp_norm {μ : Measure (Euc d)} (hm2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ) :
    MemLp (fun y : Euc d => ‖y‖) 2 μ :=
  (memLp_two_iff_integrable_sq measurable_norm.aestronglyMeasurable).2 hm2

theorem tc4_far_integrable (h : TcCutoff θ) {A : ℝ} (hA : ∀ z : Euc d, ‖fderiv ℝ (tc4_G d s θ) z‖ ≤ A)
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (hm2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ)
    {f : Euc d → ℝ} (hf : MemLp f 2 μ) (x : Euc d) :
    Integrable (fun y => f y • tc4_G d s θ (x - y)) μ := by
  have hGc : Continuous (tc4_G d s θ) := (tc4_G_contDiff h s).continuous
  have hk : AEStronglyMeasurable (fun y => tc4_G d s θ (x - y)) μ :=
    (hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hb : MemLp (fun y : Euc d => |A| * (‖x‖ + ‖y‖)) 2 μ :=
    ((memLp_const (‖x‖)).add (tc4_memLp_norm hm2)).const_mul _
  have hk2 : MemLp (fun y => tc4_G d s θ (x - y)) 2 μ := by
    refine hb.mono' hk (Filter.Eventually.of_forall fun y => ?_)
    have := tc4_G_lipschitz h hA (x - y) 0
    rw [tc4_G_zero h, sub_zero, sub_zero] at this
    rw [Real.norm_eq_abs]
    calc |tc4_G d s θ (x - y)| ≤ A * ‖x - y‖ := this
      _ ≤ |A| * ‖x - y‖ := mul_le_mul_of_nonneg_right (le_abs_self A) (norm_nonneg _)
      _ ≤ |A| * (‖x‖ + ‖y‖) := mul_le_mul_of_nonneg_left (norm_sub_le x y) (abs_nonneg A)
  exact (hf.integrable_mul hk2).congr (Filter.Eventually.of_forall fun y => by simp)

/-- Zero-mass subtraction: `‖H x‖ ≤ A ‖ |y| ‖_{L²(μ)} ‖f‖_{L²(μ)}`. -/
theorem tc4_far_abs_le (h : TcCutoff θ) {A : ℝ} (hA : ∀ z : Euc d, ‖fderiv ℝ (tc4_G d s θ) z‖ ≤ A)
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (hm2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) μ)
    {f : Euc d → ℝ} (hf : MemL2Zero μ f) (x : Euc d) :
    |tc4_conv μ f (tc4_G d s θ) x| ≤ A * Real.sqrt (∫ y, ‖y‖ ^ 2 ∂μ) * l2Norm μ f := by
  have hint := tc4_far_integrable h hA hm2 hf.1 x
  have hfi : Integrable f μ := hf.1.integrable (by norm_num)
  have h0 : ∫ y, f y * tc4_G d s θ x ∂μ = 0 := by
    rw [integral_mul_const, hf.2, zero_mul]
  have hH : tc4_conv μ f (tc4_G d s θ) x = ∫ y, f y * (tc4_G d s θ (x - y) - tc4_G d s θ x) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub (hint.congr (Filter.Eventually.of_forall fun y => by simp)) (hfi.mul_const _), h0,
      sub_zero]
    rfl
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hint2 : Integrable (fun y => ‖y‖ * ‖f y‖) μ :=
    ((tc4_memLp_norm hm2).integrable_mul hf.1.norm).congr (Filter.Eventually.of_forall fun y => by simp)
  rw [hH, ← Real.norm_eq_abs]
  calc ‖∫ y, f y * (tc4_G d s θ (x - y) - tc4_G d s θ x) ∂μ‖
      ≤ ∫ y, ‖f y * (tc4_G d s θ (x - y) - tc4_G d s θ x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, A * (‖y‖ * ‖f y‖) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hint2.const_mul A) (Filter.Eventually.of_forall fun y => ?_)
        show ‖f y * (tc4_G d s θ (x - y) - tc4_G d s θ x)‖ ≤ A * (‖y‖ * ‖f y‖)
        have := tc4_G_lipschitz h hA (x - y) x
        rw [sub_sub_cancel_left, norm_neg] at this
        rw [norm_mul, Real.norm_eq_abs (tc4_G d s θ (x - y) - tc4_G d s θ x)]
        calc ‖f y‖ * |tc4_G d s θ (x - y) - tc4_G d s θ x| ≤ ‖f y‖ * (A * ‖y‖) :=
              mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = _ := by ring
    _ = A * ∫ y, ‖y‖ * ‖f y‖ ∂μ := integral_const_mul _ _
    _ ≤ A * (Real.sqrt (∫ y, ‖y‖ ^ 2 ∂μ) * Real.sqrt (∫ y, ‖f y‖ ^ 2 ∂μ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hA0
        exact tc4_cs (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (tc4_memLp_norm hm2) hf.1.norm
    _ = _ := by
        unfold l2Norm
        simp only [norm_pow, norm_norm, sq_abs, Real.norm_eq_abs]
        ring_nf

theorem tc4_l1_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ} (hf : MemLp f 2 μ) :
    ∫ y, ‖f y‖ ∂μ ≤ l2Norm μ f := by
  have := tc4_cs (μ := μ) (u := fun _ => (1 : ℝ)) (v := fun y => ‖f y‖) (fun _ => zero_le_one)
    (fun _ => norm_nonneg _) (memLp_const 1) hf.norm
  simp only [one_mul, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one, Real.sqrt_one,
    one_mul] at this
  refine this.trans (le_of_eq ?_)
  unfold l2Norm
  simp [sq_abs]

theorem tc4_G_bound_upto (h : TcCutoff θ) (hs0 : 0 ≤ s) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ z : Euc d, ‖fderiv ℝ (tc4_G d s θ) z‖ ≤ A) ∧
      ∀ j, 1 ≤ j → j ≤ m → ∀ z : Euc d, ‖iteratedFDeriv ℝ j (tc4_G d s θ) z‖ ≤ A := by
  induction m with
  | zero =>
    obtain ⟨A, hA0, hA⟩ := tc4_G_fderiv_bound h hs0
    exact ⟨A, hA0, hA, fun j hj hjm => by omega⟩
  | succ m ih =>
    obtain ⟨A, hA0, hA1, hA⟩ := ih
    obtain ⟨A', hA'⟩ := tc4_G_bound h hs0 (j := m + 1) (by omega)
    refine ⟨max A A', hA0.trans (le_max_left _ _), fun z => (hA1 z).trans (le_max_left _ _),
      fun j hj hjm z => ?_⟩
    by_cases hjm' : j ≤ m
    · exact (hA j hj hjm' z).trans (le_max_left _ _)
    · have : j = m + 1 := by omega
      subst this
      exact (hA' z).trans (le_max_right _ _)

/-- The far convolution as a bounded `C_b^m` function (core, for an arbitrary probability measure with a
second-moment bound `M2`). -/
theorem tc4_far_core (h : TcCutoff θ) (hs0 : 0 ≤ s) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ],
      Integrable (fun y : Euc d => ‖y‖ ^ 2) μ → ∀ M2 : ℝ, ∫ y, ‖y‖ ^ 2 ∂μ ≤ M2 →
      ∀ f : Euc d → ℝ, MemL2Zero μ f →
      HRS.MemCb m (tc4_conv μ f (tc4_G d s θ)) ∧
      HRS.cbNorm m (tc4_conv μ f (tc4_G d s θ)) ≤ A * (Real.sqrt M2 + m) * l2Norm μ f := by
  obtain ⟨A, hA0, hA1, hAj⟩ := tc4_G_bound_upto h hs0 m
  refine ⟨A, hA0, fun μ _ hm2 M2 hM2 f hf => ?_⟩
  have hl2 : 0 ≤ l2Norm μ f := Real.sqrt_nonneg _
  have hfi : Integrable f μ := hf.1.integrable (by norm_num)
  have hG := tc4_G_contDiff h s
  have hint := tc4_far_integrable h hA1 hm2 hf.1
  have hb0 : ∀ x, ‖iteratedFDeriv ℝ 0 (tc4_conv μ f (tc4_G d s θ)) x‖ ≤ A * Real.sqrt M2 * l2Norm μ f := by
    intro x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    refine (tc4_far_abs_le h hA1 hm2 hf x).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hM2) hA0) hl2
  have hbj : ∀ j, 1 ≤ j → j ≤ m → ∀ x,
      ‖iteratedFDeriv ℝ j (tc4_conv μ f (tc4_G d s θ)) x‖ ≤ A * l2Norm μ f := by
    intro j hj hjm x
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have := tc4_norm_iteratedFDeriv_conv_le hfi i ℝ (tc4_G d s θ) (hG.of_le (by exact_mod_cast le_top))
      (fun k hk1 hk2 => by
        obtain ⟨A', hA'⟩ := tc4_G_bound h hs0 hk1
        exact ⟨A', hA'⟩) hint A (hAj (i + 1) hj hjm) x
    exact this.trans (mul_le_mul_of_nonneg_left (tc4_l1_le hf.1) hA0)
  have hcd : ContDiff ℝ m (tc4_conv μ f (tc4_G d s θ)) := by
    have := tc4_contDiff_conv_succ hfi m (G := tc4_G d s θ) (hG.of_le (by exact_mod_cast le_top))
      (fun k hk1 hk2 => by
        obtain ⟨A', hA'⟩ := tc4_G_bound h hs0 hk1
        exact ⟨A', hA'⟩) hint
    exact this.of_le (by exact_mod_cast Nat.le_succ m)
  refine ⟨⟨hcd, fun j hj => ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact ⟨_, by rintro _ ⟨x, rfl⟩; exact hb0 x⟩
    · exact ⟨_, by rintro _ ⟨x, rfl⟩; exact hbj j hj0 hj x⟩
  · unfold HRS.cbNorm
    have hsum : ∀ j ∈ Finset.range (m + 1),
        (⨆ x : Euc d, ‖iteratedFDeriv ℝ j (tc4_conv μ f (tc4_G d s θ)) x‖) ≤
          (if j = 0 then A * Real.sqrt M2 * l2Norm μ f else A * l2Norm μ f) := by
      intro j hj
      refine ciSup_le fun x => ?_
      by_cases hj0 : j = 0
      · subst hj0; simpa using hb0 x
      · rw [if_neg hj0]
        exact hbj j (Nat.pos_of_ne_zero hj0) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
    refine (Finset.sum_le_sum hsum).trans (le_of_eq ?_)
    rw [Finset.sum_range_succ']
    simp only [if_true, Nat.succ_ne_zero, if_false, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring

end Far

section FarK

/-- `farK θ f x = ∫ (1 - θ(x - y)) g(x - y) f(y) dμ(y)`. -/
def farK (d : ℕ) (s : ℝ) (θ : Euc d → ℝ) (μ : Measure (Euc d)) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, (1 - θ (x - y)) * rieszKernel d s (x - y) * f y ∂μ

/-- `locK θ f = (θ g) * (ρ f)`. -/
def locK (d : ℕ) (s : ℝ) (θ : Euc d → ℝ) (ρ f : Euc d → ℝ) (x : Euc d) : ℝ :=
  HRS.Whole.convFun (fun z => θ z * rieszKernel d s z) (fun y => ρ y * f y) x

theorem farK_eq_conv (d : ℕ) (s : ℝ) (θ : Euc d → ℝ) (μ : Measure (Euc d)) (f : Euc d → ℝ) :
    farK d s θ μ f = tc4_conv μ f (tc4_G d s θ) := by
  funext x
  unfold farK tc4_conv tc4_G
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]
  ring

/-- **TC-4, step 5 (far convolution).**  `f ∈ L²_0(μ)` gives `farK θ f ∈ C_b^m` with
`cbNorm m (farK θ f) ≤ C ‖f‖_{L²(μ)}`, `C = C(d, s, θ, m, M₀, c)` (independent of `ρ`, `S`). -/
theorem tc4_far {θ : Euc d → ℝ} (h : TcCutoff θ) {s : ℝ} (hs0 : 0 ≤ s) (m : ℕ) (M₀ c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Euc d → ℝ) (S : ℝ), TcRef d ρ M₀ c S 0 →
      ∀ f : Euc d → ℝ, MemL2Zero (HRS.Whole.withDensityReal ρ) f →
        HRS.MemCb m (farK d s θ (HRS.Whole.withDensityReal ρ) f) ∧
        HRS.cbNorm m (farK d s θ (HRS.Whole.withDensityReal ρ) f) ≤
          C * l2Norm (HRS.Whole.withDensityReal ρ) f := by
  obtain ⟨A, hA0, hA⟩ := tc4_far_core (d := d) (θ := θ) h hs0 m
  refine ⟨A * (Real.sqrt (tc4_m2 d M₀ c) + m), ?_, fun ρ S hρ f hf => ?_⟩
  · exact mul_nonneg hA0 (add_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg m))
  · have := tc4_isProb hρ.prob
    rw [farK_eq_conv]
    exact hA _ (tc4_sq_integrable hρ hc) _ (tc4_second_moment_le hρ hc) f hf

end FarK
section Split

variable {θ : Euc d → ℝ} {s : ℝ}

theorem tc4_cutoff_bound (h : TcCutoff θ) : ∃ B : ℝ, ∀ z, ‖θ z‖ ≤ B :=
  h.hasCompactSupport.exists_bound_of_continuous h.smooth.continuous

/-- **TC-4, step 4, pointwise form.**  At every `x` where `y ↦ g(x-y) f(y)` is `μ`-integrable. -/
theorem tc4_split_pt {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (h : TcCutoff θ)
    {f : Euc d → ℝ} {x : Euc d}
    (hx : Integrable (fun y => rieszKernel d s (x - y) * f y) (HRS.Whole.withDensityReal ρ)) :
    ∫ y, rieszKernel d s (x - y) * f y ∂(HRS.Whole.withDensityReal ρ) =
      locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x := by
  obtain ⟨B, hB⟩ := tc4_cutoff_bound h
  have hθm : Continuous fun y : Euc d => θ (x - y) := h.smooth.continuous.comp (continuous_const.sub continuous_id)
  have h1 : Integrable (fun y => θ (x - y) * (rieszKernel d s (x - y) * f y))
      (HRS.Whole.withDensityReal ρ) :=
    hx.bdd_mul (c := B) hθm.aestronglyMeasurable (Filter.Eventually.of_forall fun y => hB _)
  have h2 : Integrable (fun y => (1 - θ (x - y)) * (rieszKernel d s (x - y) * f y))
      (HRS.Whole.withDensityReal ρ) :=
    hx.bdd_mul (c := 1 + B) (continuous_const.sub hθm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        calc ‖1 - θ (x - y)‖ ≤ ‖(1 : ℝ)‖ + ‖θ (x - y)‖ := norm_sub_le _ _
          _ ≤ 1 + B := by simpa using hB _)
  have hsum : ∫ y, rieszKernel d s (x - y) * f y ∂(HRS.Whole.withDensityReal ρ) =
      ∫ y, θ (x - y) * (rieszKernel d s (x - y) * f y) ∂(HRS.Whole.withDensityReal ρ) +
        ∫ y, (1 - θ (x - y)) * (rieszKernel d s (x - y) * f y) ∂(HRS.Whole.withDensityReal ρ) := by
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [hsum]
  congr 1
  · rw [tc4_integral_wd hρ.measurable hρ.nonneg]
    unfold locK HRS.Whole.convFun
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  · unfold farK
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring

/-- For `f ∈ L²(μ)`, the integrand `y ↦ g(x-y) f(y)` is `μ`-integrable for a.e. `x`. -/
theorem tc4_ae_integrable {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    (h : TcCutoff θ) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      Integrable (fun y => rieszKernel d s (x - y) * f y) (HRS.Whole.withDensityReal ρ) := by
  have := tc4_isProb hρ.prob
  have hfi : Integrable f (HRS.Whole.withDensityReal ρ) := hf.integrable (by norm_num)
  have hρf : Integrable (fun y => ρ y * f y) := (tc4_integrable_iff hρ.prob).1 hfi
  have hG := HRS.MS.Tc3.tc3_Gloc_integrable h.smooth.continuous h.hasCompactSupport hs0 hsd
  have hae := Integrable.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hρf hG
  obtain ⟨A, hA0, hA1, -⟩ := tc4_G_bound_upto h hs0 0
  filter_upwards [hae] with x hx
  have hloc : Integrable (fun y => θ (x - y) * (rieszKernel d s (x - y) * f y))
      (HRS.Whole.withDensityReal ρ) := by
    rw [tc4_integrable_iff hρ.prob]
    refine hx.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.mul_apply', HRS.MS.Tc3.tc3_Gloc]
    ring
  have hfar := tc4_far_integrable h hA1 (tc4_sq_integrable hρ hc) hf x
  have : Integrable (fun y => θ (x - y) * (rieszKernel d s (x - y) * f y) +
      f y • tc4_G d s θ (x - y)) (HRS.Whole.withDensityReal ρ) := hloc.add hfar
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [tc4_G, smul_eq_mul]
  ring

/-- **TC-4, step 4 (splitting of `K`).**  For `f ∈ L²(μ)` (so `ρ f ∈ L¹`), for Lebesgue-a.e. `x`:
`K_μ f (x) = locK f x + farK f x - μ(locK f + farK f)`. -/
theorem tc4_split {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    (h : TcCutoff θ) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) f x =
        (locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x) -
          HRS.Whole.pair (HRS.Whole.withDensityReal ρ)
            (fun x => locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x) := by
  have hae := tc4_ae_integrable hρ hc h hs0 hsd hf
  have hac : HRS.Whole.withDensityReal ρ ≪ (volume : Measure (Euc d)) :=
    withDensity_absolutelyContinuous _ _
  have hpt : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ∫ y, rieszKernel d s (x - y) * f y ∂(HRS.Whole.withDensityReal ρ) =
        locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x := by
    filter_upwards [hae] with x hx using tc4_split_pt hρ.prob h hx
  have hpair : HRS.Whole.pair (HRS.Whole.withDensityReal ρ)
      (fun x => ∫ y, rieszKernel d s (x - y) * f y ∂(HRS.Whole.withDensityReal ρ)) =
      HRS.Whole.pair (HRS.Whole.withDensityReal ρ)
        (fun x => locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x) :=
    integral_congr_ae (hac.ae_le hpt)
  filter_upwards [hpt] with x hx
  unfold HRS.Whole.Kop HRS.Whole.projMean
  beta_reduce
  rw [hpair, hx]

/-- The same formula `μ`-almost everywhere. -/
theorem tc4_split_mu {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : TcRef d ρ M₀ c S N) (hc : 0 < c)
    (h : TcCutoff θ) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : MemLp f 2 (HRS.Whole.withDensityReal ρ)) :
    ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
      HRS.Whole.Kop (rieszKernel d s) (HRS.Whole.withDensityReal ρ) f x =
        (locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x) -
          HRS.Whole.pair (HRS.Whole.withDensityReal ρ)
            (fun x => locK d s θ ρ f x + farK d s θ (HRS.Whole.withDensityReal ρ) f x) :=
  (withDensity_absolutelyContinuous _ _).ae_le (tc4_split hρ hc h hs0 hsd hf)

end Split
section Loc

variable {θ : Euc d → ℝ} {s : ℝ}

/-- Derivatives of a convolution `K ⋆ u` with `K ∈ L¹`, `u ∈ C_b^J` fall on `u`. -/
theorem tc4_conv_cb (J : ℕ) {K : Euc d → ℝ} (hK : Integrable K) {u : Euc d → ℝ}
    (hu : HRS.MemCb J u) :
    HRS.MemCb J (tc4_conv volume K u) ∧
      HRS.cbNorm J (tc4_conv volume K u) ≤ (∫ y, ‖K y‖) * HRS.cbNorm J u := by
  set a : ℕ → ℝ := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j u z‖ with ha
  have hale : ∀ j ≤ J, ∀ z, ‖iteratedFDeriv ℝ j u z‖ ≤ a j := fun j hj z =>
    le_ciSup (hu.2 j hj) z
  have hK0 : 0 ≤ ∫ y, ‖K y‖ := integral_nonneg fun _ => norm_nonneg _
  have hint : ∀ x, Integrable (fun y => K y • u (x - y)) volume :=
    tc4_integrable_of_bdd hK hu.1.continuous (A := a 0) (fun z => by
      simpa using hale 0 (Nat.zero_le _) z)
  have hb : ∀ j ≤ J, ∃ A, ∀ z, ‖iteratedFDeriv ℝ j u z‖ ≤ A := fun j hj => ⟨a j, hale j hj⟩
  have hcd := tc4_contDiff_conv hK J ℝ u hu.1 hb
  have hbd : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (tc4_conv volume K u) x‖ ≤ a j * ∫ y, ‖K y‖ := by
    intro j hj x
    rcases j with _ | i
    · rw [norm_iteratedFDeriv_zero]
      exact tc4_norm_conv_le hK (fun z => by simpa using hale 0 hj z) x
    · exact tc4_norm_iteratedFDeriv_conv_le hK i ℝ u (hu.1.of_le (by exact_mod_cast hj))
        (fun k _ hk2 => hb k (by omega)) hint (a (i + 1)) (hale (i + 1) hj) x
  refine ⟨⟨hcd, fun j hj => ⟨a j * ∫ y, ‖K y‖, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hbd j hj x
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (J + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (tc4_conv volume K u) x‖
        ≤ ∑ j ∈ Finset.range (J + 1), a j * ∫ y, ‖K y‖ :=
          Finset.sum_le_sum fun j hj => ciSup_le fun x =>
            hbd j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
      _ = (∫ y, ‖K y‖) * ∑ j ∈ Finset.range (J + 1), a j := by rw [← Finset.sum_mul, mul_comm]

theorem tc4_convFun_flip (K u : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.convFun K u x = tc4_conv volume K u x := by
  unfold HRS.Whole.convFun tc4_conv
  have := integral_sub_left_eq_self (fun y => K y * u (x - y)) (volume : Measure (Euc d)) x
  simpa [sub_sub_cancel, smul_eq_mul] using this

/-- **TC-4, local part in `C_b^J`.**  If `ρ h ∈ C_b^J` then `locK θ h = (θ g) ⋆ (ρ h) ∈ C_b^J` and
`cbNorm J (locK θ h) ≤ ‖θ g‖_{L¹} cbNorm J (ρ h)`. -/
theorem tc4_loc_cb (J : ℕ) (h : TcCutoff θ) (hs0 : 0 ≤ s) (hsd : s < d) {ρ f : Euc d → ℝ}
    (hu : HRS.MemCb J (fun y => ρ y * f y)) :
    HRS.MemCb J (locK d s θ ρ f) ∧
      HRS.cbNorm J (locK d s θ ρ f) ≤
        (∫ z, ‖θ z * rieszKernel d s z‖) * HRS.cbNorm J (fun y => ρ y * f y) := by
  have hK := HRS.MS.Tc3.tc3_Gloc_integrable h.smooth.continuous h.hasCompactSupport hs0 hsd
  have hlk : locK d s θ ρ f = tc4_conv volume (HRS.MS.Tc3.tc3_Gloc d s θ) (fun y => ρ y * f y) := by
    funext x
    exact tc4_convFun_flip _ _ x
  rw [hlk]
  exact tc4_conv_cb J hK hu

theorem tc4_cb_mul (J : ℕ) {φ ψ : Euc d → ℝ} (hφ : HRS.MemCb J φ) (hψ : HRS.MemCb J ψ) :
    HRS.MemCb J (fun y => φ y * ψ y) ∧
      HRS.cbNorm J (fun y => φ y * ψ y) ≤
        ((J + 1 : ℝ) ^ 2 * 2 ^ J) * HRS.cbNorm J φ * HRS.cbNorm J ψ := by
  set a : ℕ → ℝ := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j φ z‖ with ha
  set b : ℕ → ℝ := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j ψ z‖ with hb
  have ha0 : ∀ j, 0 ≤ a j := fun j => Real.iSup_nonneg fun _ => norm_nonneg _
  have hb0 : ∀ j, 0 ≤ b j := fun j => Real.iSup_nonneg fun _ => norm_nonneg _
  have hale : ∀ j ≤ J, ∀ z, ‖iteratedFDeriv ℝ j φ z‖ ≤ a j := fun j hj z => le_ciSup (hφ.2 j hj) z
  have hble : ∀ j ≤ J, ∀ z, ‖iteratedFDeriv ℝ j ψ z‖ ≤ b j := fun j hj z => le_ciSup (hψ.2 j hj) z
  set Sa : ℝ := ∑ j ∈ Finset.range (J + 1), a j with hSa
  set Sb : ℝ := ∑ j ∈ Finset.range (J + 1), b j with hSb
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg fun i _ => ha0 i
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun i _ => hb0 i
  have hSa' : ∀ j ≤ J, a j ≤ Sa := fun j hj =>
    Finset.single_le_sum (f := a) (fun i _ => ha0 i) (Finset.mem_range.2 (by omega))
  have hSb' : ∀ j ≤ J, b j ≤ Sb := fun j hj =>
    Finset.single_le_sum (f := b) (fun i _ => hb0 i) (Finset.mem_range.2 (by omega))
  have key : ∀ n ≤ J, ∀ x, ‖iteratedFDeriv ℝ n (fun y => φ y * ψ y) x‖ ≤
      (J + 1 : ℝ) * (2 ^ J * Sa * Sb) := by
    intro n hn x
    refine (norm_iteratedFDeriv_mul_le hφ.1 hψ.1 x (by exact_mod_cast hn)).trans ?_
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ *
          ‖iteratedFDeriv ℝ (n - i) ψ x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (2 ^ J * Sa * Sb : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have hc : (n.choose i : ℝ) ≤ 2 ^ J := by
            calc (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
              _ ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hn
          have h1 := (hale i (by omega) x).trans (hSa' i (by omega))
          have h2 := (hble (n - i) (by omega) x).trans (hSb' (n - i) (by omega))
          have h3 : 0 ≤ ‖iteratedFDeriv ℝ i φ x‖ := norm_nonneg _
          have h4 : 0 ≤ ‖iteratedFDeriv ℝ (n - i) ψ x‖ := norm_nonneg _
          have h5 : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
          have key2 : (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ * ‖iteratedFDeriv ℝ (n - i) ψ x‖
              ≤ 2 ^ J * Sa * Sb := by gcongr
          exact key2
      _ = ((n : ℝ) + 1) * (2 ^ J * Sa * Sb) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (J + 1 : ℝ) * (2 ^ J * Sa * Sb) := by
          have : (n : ℝ) ≤ J := by exact_mod_cast hn
          have h0 : 0 ≤ (2 : ℝ) ^ J * Sa * Sb := by positivity
          nlinarith
  refine ⟨⟨hφ.1.mul hψ.1, fun j hj => ⟨(J + 1 : ℝ) * (2 ^ J * Sa * Sb), ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact key j hj x
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (J + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (fun y => φ y * ψ y) x‖
        ≤ ∑ j ∈ Finset.range (J + 1), ((J + 1 : ℝ) * (2 ^ J * Sa * Sb)) :=
          Finset.sum_le_sum fun j hj => ciSup_le fun x =>
            key j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
      _ = ((J + 1 : ℝ) ^ 2 * 2 ^ J) * Sa * Sb := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

theorem tc4_cb_rho (J : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Euc d → ℝ) (M₀ S : ℝ), TcRef d ρ M₀ c S J →
      HRS.MemCb J ρ ∧ HRS.cbNorm J ρ ≤ C * S := by
  set K : ℕ → ℝ := fun k => (k.factorial : ℝ) * Real.exp (1 + 1 / (4 * c)) with hK
  have hK0 : ∀ k, 0 ≤ K k := fun k => by positivity
  have hpoly : ∀ (k : ℕ) (r : ℝ), 0 ≤ r → (1 + r) ^ k * Real.exp (-c * r ^ 2) ≤ K k := by
    intro k r hr
    have h1 : (1 + r) ^ k ≤ k.factorial * Real.exp (1 + r) := by
      have := Real.pow_div_factorial_le_exp (x := 1 + r) (by linarith) k
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h2 : 1 + r + -c * r ^ 2 ≤ 1 + 1 / (4 * c) := by
      have : r - c * r ^ 2 ≤ 1 / (4 * c) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (2 * c * r - 1)]
      linarith
    calc (1 + r) ^ k * Real.exp (-c * r ^ 2)
        ≤ (k.factorial * Real.exp (1 + r)) * Real.exp (-c * r ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = k.factorial * Real.exp (1 + r + -c * r ^ 2) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ K k := by
          rw [hK]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity)
  refine ⟨∑ k ∈ Finset.range (J + 1), K k, Finset.sum_nonneg fun k _ => hK0 k, fun ρ M₀ S hρ => ?_⟩
  have hS : 0 ≤ S := by
    have := hρ.deriv 0 (Nat.zero_le _) 0
    simp only [norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, neg_zero,
      Real.exp_zero, mul_one, pow_zero] at this
    exact (norm_nonneg _).trans this
  have hb : ∀ k ≤ J, ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ S * K k := fun k hk x =>
    (hρ.deriv k hk x).trans (by
      calc S * (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2) = S * ((1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by ring
        _ ≤ S * K k := mul_le_mul_of_nonneg_left (hpoly k ‖x‖ (norm_nonneg _)) hS)
  refine ⟨⟨hρ.smooth.of_le (by exact_mod_cast le_top), fun j hj => ⟨S * K j, ?_⟩⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hb j hj x
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (J + 1), ⨆ x : Euc d, ‖iteratedFDeriv ℝ j ρ x‖
        ≤ ∑ j ∈ Finset.range (J + 1), S * K j :=
          Finset.sum_le_sum fun j hj => ciSup_le fun x =>
            hb j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) x
      _ = (∑ k ∈ Finset.range (J + 1), K k) * S := by rw [← Finset.mul_sum, mul_comm]

/-- `tc4_loc_cb` for `h ∈ C_b^J` and a reference density: `cbNorm J (ρ h) ≤ C S cbNorm J h`. -/
theorem tc4_loc_cb_rho (J : ℕ) (h : TcCutoff θ) (hs0 : 0 ≤ s) (hsd : s < d) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : Euc d → ℝ) (M₀ S : ℝ), TcRef d ρ M₀ c S J → ∀ f : Euc d → ℝ,
      HRS.MemCb J f → HRS.MemCb J (locK d s θ ρ f) ∧
        HRS.cbNorm J (locK d s θ ρ f) ≤
          C * S * (∫ z, ‖θ z * rieszKernel d s z‖) * HRS.cbNorm J f := by
  obtain ⟨Cr, hCr0, hCr⟩ := tc4_cb_rho (d := d) J c hc
  refine ⟨((J + 1 : ℝ) ^ 2 * 2 ^ J) * Cr, by positivity, fun ρ M₀ S hρ f hf => ?_⟩
  obtain ⟨hρcb, hρn⟩ := hCr ρ M₀ S hρ
  obtain ⟨hmul, hmuln⟩ := tc4_cb_mul J hρcb hf
  obtain ⟨hloc, hlocn⟩ := tc4_loc_cb J h hs0 hsd hmul
  refine ⟨hloc, hlocn.trans ?_⟩
  have hI : 0 ≤ ∫ z, ‖θ z * rieszKernel d s z‖ := integral_nonneg fun _ => norm_nonneg _
  have hcf : 0 ≤ HRS.cbNorm J f :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcρ : 0 ≤ HRS.cbNorm J ρ :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hP : (0 : ℝ) ≤ (J + 1 : ℝ) ^ 2 * 2 ^ J := by positivity
  calc (∫ z, ‖θ z * rieszKernel d s z‖) * HRS.cbNorm J (fun y => ρ y * f y)
      ≤ (∫ z, ‖θ z * rieszKernel d s z‖) *
          (((J + 1 : ℝ) ^ 2 * 2 ^ J) * HRS.cbNorm J ρ * HRS.cbNorm J f) :=
        mul_le_mul_of_nonneg_left hmuln hI
    _ ≤ (∫ z, ‖θ z * rieszKernel d s z‖) *
          (((J + 1 : ℝ) ^ 2 * 2 ^ J) * (Cr * S) * HRS.cbNorm J f) := by
        refine mul_le_mul_of_nonneg_left ?_ hI
        refine mul_le_mul_of_nonneg_right ?_ hcf
        exact mul_le_mul_of_nonneg_left hρn hP
    _ = (((J + 1 : ℝ) ^ 2 * 2 ^ J) * Cr) * S * (∫ z, ‖θ z * rieszKernel d s z‖) * HRS.cbNorm J f := by
        ring

end Loc




end HRS.MS.TcF

end
