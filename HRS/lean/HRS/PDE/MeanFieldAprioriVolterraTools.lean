import HRS.PDE.MeanFieldDefs
import HRS.PDE.MeanFieldAprioriHeat
import HRS.PDE.MeanFieldAprioriClassical

/-!
# (I3) AP5c1: parabolic toolbox for the Volterra bootstrap (package MF-01)

Heat smoothing `H^a → H^{a+β}`, Minkowski's inequality for coefficientwise interval integrals in
`H^m` with a singular (only integrable) weight, the modewise Duhamel formula for a solution of
`IsMFSolutionHK`, and a singular Gronwall inequality on `[0,1]` (exponential-weight trick).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-! ### Heat smoothing -/

theorem heat_pointwise (β : ℝ) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) {L x : ℝ} (hL : 0 ≤ L) (hx : 0 < x) :
    (1 + L) ^ β * Real.exp (-(2 * L * x)) ≤ 4 * (1 + x ^ (-β)) := by
  have h2β : (2 : ℝ) ^ β ≤ 4 := by
    calc (2 : ℝ) ^ β ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ2
      _ = 4 := by norm_num
  have h1 : (1 + L) ^ β ≤ 4 * (1 + L ^ β) := by
    have hLb : 0 ≤ L ^ β := Real.rpow_nonneg hL _
    rcases le_total L 1 with hL1 | hL1
    · have : (1 + L) ^ β ≤ (2 : ℝ) ^ β := Real.rpow_le_rpow (by linarith) (by linarith) hβ0
      nlinarith
    · have : (1 + L) ^ β ≤ (2 * L) ^ β := Real.rpow_le_rpow (by linarith) (by linarith) hβ0
      rw [Real.mul_rpow (by norm_num) hL] at this
      nlinarith
  have h2 : L ^ β * Real.exp (-(2 * L * x)) ≤ x ^ (-β) := by
    set y := L * x with hy
    have hy0 : 0 ≤ y := by positivity
    have hyβ : y ^ β ≤ 1 + y ^ 2 := by
      rcases le_total y 1 with h | h
      · have := Real.rpow_le_one hy0 h hβ0
        nlinarith [sq_nonneg y]
      · have : y ^ β ≤ y ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hβ2
        rw [Real.rpow_two] at this
        linarith
    have hexp : 1 + 2 * y + 2 * y ^ 2 ≤ Real.exp (2 * y) := by
      have := Real.quadratic_le_exp_of_nonneg (x := 2 * y) (by positivity)
      nlinarith
    have hE : Real.exp (-(2 * L * x)) = (Real.exp (2 * y))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; rw [hy]; ring
    have h3 : y ^ β * Real.exp (-(2 * L * x)) ≤ 1 := by
      rw [hE, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      nlinarith [sq_nonneg y]
    have hLx : L ^ β = y ^ β * x ^ (-β) := by
      rw [hy, Real.mul_rpow hL hx.le, mul_assoc, ← Real.rpow_add hx]
      simp
    calc L ^ β * Real.exp (-(2 * L * x)) = (y ^ β * Real.exp (-(2 * L * x))) * x ^ (-β) := by
          rw [hLx]; ring
      _ ≤ 1 * x ^ (-β) := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hx.le _)
      _ = x ^ (-β) := one_mul _
  have hexp1 : Real.exp (-(2 * L * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hL hx.le])
  calc (1 + L) ^ β * Real.exp (-(2 * L * x)) ≤ 4 * (1 + L ^ β) * Real.exp (-(2 * L * x)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 4 * (Real.exp (-(2 * L * x)) + L ^ β * Real.exp (-(2 * L * x))) := by ring
    _ ≤ 4 * (1 + x ^ (-β)) := by gcongr

theorem hsNorm_nonneg' (m : ℝ) (c : Coeff d) : 0 ≤ hsNorm m c := Real.sqrt_nonneg _

/-- Heat smoothing `H^a → H^{a+β}` with constant `C (1 + (ντ)^{-β/2})`, `0 ≤ β ≤ 2`. -/
theorem exists_heat_smoothing (a β : ℝ) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν τ : ℝ), 0 < ν → 0 < τ → ∀ c : Coeff d, MemHs a c →
      MemHs (a + β) (fun k => (heatMult (ν * τ) k : ℂ) * c k) ∧
      hsNorm (a + β) (fun k => (heatMult (ν * τ) k : ℂ) * c k) ≤
        C * (1 + (ν * τ) ^ (-(β / 2))) * hsNorm a c := by
  refine ⟨2, by norm_num, fun ν τ hν hτ c hc => ?_⟩
  set x := ν * τ with hx
  have hx0 : 0 < x := mul_pos hν hτ
  set M : ℝ := 2 * (1 + x ^ (-(β / 2))) with hM
  have hu : (x ^ (-(β / 2))) ^ 2 = x ^ (-β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hM2 : 4 * (1 + x ^ (-β)) ≤ M ^ 2 := by
    have : 0 ≤ x ^ (-(β / 2)) := Real.rpow_nonneg hx0.le _
    rw [hM, ← hu]; nlinarith
  have hpt : ∀ k : Lattice d, sobWeight (a + β) k * ‖(heatMult x k : ℂ) * c k‖ ^ 2 ≤
      M ^ 2 * (sobWeight a k * ‖c k‖ ^ 2) := by
    intro k
    set L : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hL
    have hL0 : 0 ≤ L := by positivity
    have hsw : sobWeight β k = (1 + L) ^ β := rfl
    have hhm : heatMult x k = Real.exp (-L * x) := rfl
    have hnorm : ‖(heatMult x k : ℂ) * c k‖ ^ 2 = Real.exp (-(2 * L * x)) * ‖c k‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatMult_pos x k).le, hhm, mul_pow,
        ← Real.exp_nat_mul]
      congr 2; push_cast; ring
    rw [hnorm, sobWeight_add, hsw]
    have := heat_pointwise β hβ0 hβ2 hL0 hx0
    have h' : (1 + L) ^ β * Real.exp (-(2 * L * x)) ≤ M ^ 2 := this.trans hM2
    have hsa := (sobWeight_pos a k).le
    calc sobWeight a k * (1 + L) ^ β * (Real.exp (-(2 * L * x)) * ‖c k‖ ^ 2)
        = ((1 + L) ^ β * Real.exp (-(2 * L * x))) * (sobWeight a k * ‖c k‖ ^ 2) := by ring
      _ ≤ M ^ 2 * (sobWeight a k * ‖c k‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h' (mul_nonneg hsa (sq_nonneg _))
  have hsum : MemHs (a + β) (fun k => (heatMult x k : ℂ) * c k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _)) hpt
      (hc.mul_left (M ^ 2))
  refine ⟨hsum, ?_⟩
  have hle : hsNormSq (a + β) (fun k => (heatMult x k : ℂ) * c k) ≤ M ^ 2 * hsNormSq a c := by
    unfold hsNormSq
    rw [← tsum_mul_left]
    exact hsum.tsum_le_tsum hpt (hc.mul_left _)
  have hM0 : 0 ≤ M := by rw [hM]; have : 0 ≤ x ^ (-(β / 2)) := Real.rpow_nonneg hx0.le _; positivity
  unfold hsNorm
  calc Real.sqrt (hsNormSq (a + β) fun k => (heatMult x k : ℂ) * c k)
      ≤ Real.sqrt (M ^ 2 * hsNormSq a c) := Real.sqrt_le_sqrt hle
    _ = M * Real.sqrt (hsNormSq a c) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM0]
    _ = 2 * (1 + x ^ (-(β / 2))) * Real.sqrt (hsNormSq a c) := rfl

/-! ### Minkowski for `H^m`-valued interval integrals -/

theorem norm_coeff_le_hsNorm (m : ℝ) {c : Coeff d} (hc : MemHs m c) (k : Lattice d) :
    ‖c k‖ * Real.sqrt (sobWeight m k) ≤ hsNorm m c := by
  have h1 : sobWeight m k * ‖c k‖ ^ 2 ≤ hsNormSq m c := sobWeight_mul_sq_le_hsNormSq hc k
  calc ‖c k‖ * Real.sqrt (sobWeight m k)
      = Real.sqrt (sobWeight m k * ‖c k‖ ^ 2) := by
        rw [Real.sqrt_mul (sobWeight_pos m k).le, Real.sqrt_sq (norm_nonneg _), mul_comm]
    _ ≤ hsNorm m c := Real.sqrt_le_sqrt h1

/-- Minkowski for coefficientwise interval integrals in `H^m` (integrable singular weight). -/
theorem hsNorm_intervalIntegral_le (m : ℝ) (F : ℝ → Coeff d) (a b : ℝ) (hab : a ≤ b)
    (hmeas : ∀ k, AEStronglyMeasurable (fun σ => F σ k) (volume.restrict (Set.Ioc a b)))
    (hmem : ∀ σ ∈ Set.Ioo a b, MemHs m (F σ))
    (hint : IntegrableOn (fun σ => hsNorm m (F σ)) (Set.Ioc a b)) :
    MemHs m (fun k => ∫ σ in a..b, F σ k) ∧
      hsNorm m (fun k => ∫ σ in a..b, F σ k) ≤ ∫ σ in a..b, hsNorm m (F σ) := by
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Ioc a b)), σ ∈ Set.Ioo a b := by
    have h1 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({b} : Set ℝ) :=
      (Set.countable_singleton b).ae_notMem volume
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h1] with σ hσ hσ'
    exact ⟨hσ'.1, lt_of_le_of_ne hσ'.2 (by simpa using hσ)⟩
  have hw0 : ∀ k : Lattice d, 0 ≤ sobWeight m k := fun k => (sobWeight_pos m k).le
  have hmode : ∀ k, IntervalIntegrable (fun σ => F σ k) volume a b := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hwk : 0 < Real.sqrt (sobWeight m k) := Real.sqrt_pos.mpr (sobWeight_pos m k)
    refine Integrable.mono' (hint.div_const (Real.sqrt (sobWeight m k))) (hmeas k) ?_
    filter_upwards [hae] with σ hσ
    rw [le_div_iff₀ hwk]
    exact norm_coeff_le_hsNorm m (hmem σ hσ) k
  have hnorm : IntervalIntegrable (fun σ => hsNorm m (F σ)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hint
  set A : Lattice d → ℂ := fun k => ∫ σ in a..b, F σ k with hA
  set B : ℝ := ∫ σ in a..b, hsNorm m (F σ) with hB
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg hab fun σ _ => hsNorm_nonneg' _ _
  have key : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight m k * ‖A k‖ ^ 2 ≤ B ^ 2 := by
    intro S
    set N : ℝ := ∑ k ∈ S, sobWeight m k * ‖A k‖ ^ 2 with hN
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (sq_nonneg _)
    rcases hN0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    set H : ℝ → ℂ := fun σ => ∑ k ∈ S, ((sobWeight m k : ℝ) : ℂ) * conj (A k) * F σ k with hH
    have hHint : IntervalIntegrable H volume a b := by
      have := IntervalIntegrable.sum S fun k _ =>
        (hmode k).const_mul (((sobWeight m k : ℝ) : ℂ) * conj (A k))
      convert this using 1
      funext σ
      simp [hH, Finset.sum_apply, mul_assoc]
    have hI : ∫ σ in a..b, H σ = (N : ℂ) := by
      simp only [hH]
      rw [intervalIntegral.integral_finsetSum fun k _ => (hmode k).const_mul _]
      simp_rw [intervalIntegral.integral_const_mul]
      simp only [hN]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (conj (A k)) * A k = ((‖A k‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hA]
      simp only at this ⊢
      rw [mul_assoc, this]
      push_cast; ring
    have hpt : ∀ σ ∈ Set.Ioo a b, ‖H σ‖ ≤ Real.sqrt N * hsNorm m (F σ) := by
      intro σ hσ
      have h1 : ‖H σ‖ ≤ ∑ k ∈ S, (Real.sqrt (sobWeight m k) * ‖A k‖) *
          (Real.sqrt (sobWeight m k) * ‖F σ k‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 k),
          RCLike.norm_conj]
        have := Real.mul_self_sqrt (hw0 k)
        linear_combination (-(‖A k‖ * ‖F σ k‖)) * this
      refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt S _ _).trans ?_)
      refine mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      · refine le_of_eq (congrArg Real.sqrt (Finset.sum_congr rfl fun k _ => ?_))
        rw [mul_pow, Real.sq_sqrt (hw0 k)]
      · unfold hsNorm hsNormSq
        refine Real.sqrt_le_sqrt ?_
        have hs := hmem σ hσ
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
          (hs.sum_le_tsum S fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))
        rw [mul_pow, Real.sq_sqrt (hw0 k)]
    have hmono : ∫ σ in a..b, ‖H σ‖ ≤ ∫ σ in a..b, Real.sqrt N * hsNorm m (F σ) := by
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      refine integral_mono_ae hHint.norm.1 (hnorm.const_mul _).1 ?_
      filter_upwards [hae] with σ hσ using hpt σ hσ
    have h2 : N ≤ Real.sqrt N * B := by
      calc N = ‖(N : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
        _ = ‖∫ σ in a..b, H σ‖ := by rw [hI]
        _ ≤ ∫ σ in a..b, ‖H σ‖ := intervalIntegral.norm_integral_le_integral_norm hab
        _ ≤ ∫ σ in a..b, Real.sqrt N * hsNorm m (F σ) := hmono
        _ = Real.sqrt N * B := intervalIntegral.integral_const_mul _ _
    have h3 : Real.sqrt N ≤ B := by
      have hs := Real.sqrt_pos.mpr hpos
      have : Real.sqrt N * Real.sqrt N ≤ Real.sqrt N * B := by
        rwa [Real.mul_self_sqrt hN0]
      exact le_of_mul_le_mul_left this hs
    calc N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN0).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2
  have hnn : ∀ k : Lattice d, 0 ≤ sobWeight m k * ‖A k‖ ^ 2 := fun k => mul_nonneg (hw0 k) (sq_nonneg _)
  have hsum : MemHs m A := summable_of_sum_le hnn key
  refine ⟨hsum, ?_⟩
  unfold hsNorm hsNormSq
  exact Real.sqrt_le_iff.mpr ⟨hB0, Real.tsum_le_of_sum_le hnn key⟩

/-! ### Singular Gronwall -/

theorem integral_rpow_neg_zero (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, r ^ (-b) = t ^ (1 - b) / (1 - b) := by
  rw [integral_rpow (Or.inl (by linarith))]
  have : (0 : ℝ) ^ (-b + 1) = 0 := Real.zero_rpow (by linarith)
  rw [this]
  have h : -b + 1 = 1 - b := by ring
  rw [h]; simp only [sub_zero]

theorem intervalIntegrable_rpow_neg (b : ℝ) (hb1 : b < 1) (t : ℝ) :
    IntervalIntegrable (fun r : ℝ => r ^ (-b)) volume 0 t :=
  intervalIntegral.intervalIntegrable_rpow' (by linarith)

theorem intervalIntegrable_sub_rpow_neg (b : ℝ) (hb1 : b < 1) (t : ℝ) :
    IntervalIntegrable (fun r : ℝ => (t - r) ^ (-b)) volume 0 t := by
  have := (intervalIntegrable_rpow_neg b hb1 t).comp_sub_left t
  simpa using this.symm

theorem integral_sub_rpow_neg (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, (t - r) ^ (-b) = t ^ (1 - b) / (1 - b) := by
  have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-b)) (a := 0) (b := t) t
  simp only [sub_self, sub_zero] at this
  rw [this]
  exact integral_rpow_neg_zero b hb0 hb1 ht


theorem kernel_pointwise (a : ℝ) (ha0 : 0 ≤ a) {t : ℝ} (ht0 : 0 < t) :
    ∀ r ∈ Set.Ioo 0 t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ)) ≤
      (t / 2) ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-a) + (t / 2) ^ (-a) * r ^ (-(1 / 2 : ℝ)) := by
  have hu : 0 < t / 2 := by positivity
  intro r hr
  have h1 : 0 ≤ (t - r) ^ (-a) := Real.rpow_nonneg (by linarith [hr.2]) _
  have h2 : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr.1.le _
  have h3 : 0 ≤ (t / 2) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu.le _
  have h4 : 0 ≤ (t / 2) ^ (-a) := Real.rpow_nonneg hu.le _
  rcases le_or_gt (t / 2) r with h | h
  · have : r ^ (-(1 / 2 : ℝ)) ≤ (t / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hu h (by norm_num)
    nlinarith [mul_nonneg h4 h2]
  · have : (t - r) ^ (-a) ≤ (t / 2) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
    nlinarith [mul_nonneg h3 h1]

theorem kernel_integrableOn (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) {t : ℝ} (ht0 : 0 < t) :
    IntegrableOn (fun r : ℝ => (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 t) := by
  have hpt := kernel_pointwise a ha0 ht0
  have hg1 := (intervalIntegrable_sub_rpow_neg a ha1 t).const_mul ((t / 2) ^ (-(1 / 2 : ℝ)))
  have hg2 := (intervalIntegrable_rpow_neg (1 / 2) (by norm_num) t).const_mul ((t / 2) ^ (-a))
  have hg := hg1.add hg2
  have hgI : IntegrableOn (fun r : ℝ => (t / 2) ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-a) +
      (t / 2) ^ (-a) * r ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 t) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).mp hg
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hfm : Measurable (fun r : ℝ => (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) :=
    ((measurable_const.sub measurable_id).pow_const _).mul (measurable_id.pow_const _)
  refine Integrable.mono' hgI hfm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun r hr => ?_)
  have h1 : 0 ≤ (t - r) ^ (-a) := Real.rpow_nonneg (by linarith [hr.2]) _
  have h2 : 0 ≤ r ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hr.1.le _
  rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
  exact hpt r hr


theorem kernel_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ)) ≤ 2 / (1 - a) + 4 := by
  have hu : 0 < t / 2 := by positivity
  have hpt := kernel_pointwise a ha0.le ht0
  have hI1 := integral_sub_rpow_neg a ha0 ha1 ht0.le
  have hI2 := integral_rpow_neg_zero (1 / 2) (by norm_num) (by norm_num) ht0.le
  have hg1 := (intervalIntegrable_sub_rpow_neg a ha1 t).const_mul ((t / 2) ^ (-(1 / 2 : ℝ)))
  have hg2 := (intervalIntegrable_rpow_neg (1 / 2) (by norm_num) t).const_mul ((t / 2) ^ (-a))
  have hg := hg1.add hg2
  have hgI : IntegrableOn (fun r : ℝ => (t / 2) ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-a) +
      (t / 2) ^ (-a) * r ^ (-(1 / 2 : ℝ))) (Set.Ioo 0 t) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).mp hg
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hfI := kernel_integrableOn a ha0.le ha1 ht0
  have hmono : ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ)) ≤
      ∫ r in (0 : ℝ)..t, ((t / 2) ^ (-(1 / 2 : ℝ)) * (t - r) ^ (-a) +
        (t / 2) ^ (-a) * r ^ (-(1 / 2 : ℝ))) := by
    rw [intervalIntegral.integral_of_le ht0.le, intervalIntegral.integral_of_le ht0.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_mono_on hfI hgI measurableSet_Ioo hpt
  rw [intervalIntegral.integral_add hg1 hg2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hI1, hI2] at hmono
  refine (mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg ht0.le _)).trans ?_
  have e1 : t ^ (1 / 2 : ℝ) * (t / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 := by
    have ht2 : t ^ (1 / 2 : ℝ) = 2 ^ (1 / 2 : ℝ) * (t / 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) hu.le]; congr 1; ring
    rw [ht2, mul_assoc, ← Real.rpow_add hu]
    simp only [add_neg_cancel, Real.rpow_zero, mul_one]
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have e2 : t ^ (1 - a) ≤ 1 := Real.rpow_le_one ht0.le ht1 (by linarith)
  have e3 : t ^ (1 / 2 : ℝ) * ((t / 2) ^ (-a) * (t ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2))) ≤ 4 := by
    have h12 : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [h12]
    have hsq : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
      rw [← Real.rpow_add ht0]; norm_num
    have h3 : t * (t / 2) ^ (-a) = 2 * (t / 2) ^ (1 - a) := by
      have e : t * (t / 2) ^ (-a) = 2 * ((t / 2) * (t / 2) ^ (-a)) := by ring
      rw [e, show (1 - a) = 1 + (-a) by ring, Real.rpow_add hu, Real.rpow_one]
    have h4 : (t / 2) ^ (1 - a) ≤ 1 := Real.rpow_le_one hu.le (by linarith) (by linarith)
    calc t ^ (1 / 2 : ℝ) * ((t / 2) ^ (-a) * (t ^ (1 / 2 : ℝ) / (1 / 2)))
        = 2 * ((t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ)) * (t / 2) ^ (-a)) := by ring
      _ = 4 * (t / 2) ^ (1 - a) := by rw [hsq, h3]; ring
      _ ≤ 4 := by linarith
  have h1a : 0 < 1 - a := by linarith
  calc t ^ (1 / 2 : ℝ) * ((t / 2) ^ (-(1 / 2 : ℝ)) * (t ^ (1 - a) / (1 - a)) +
        (t / 2) ^ (-a) * (t ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2)))
      = (t ^ (1 / 2 : ℝ) * (t / 2) ^ (-(1 / 2 : ℝ))) * (t ^ (1 - a) / (1 - a)) +
        t ^ (1 / 2 : ℝ) * ((t / 2) ^ (-a) * (t ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2))) := by ring
    _ ≤ 2 * (1 / (1 - a)) + 4 := by
        have h5 : t ^ (1 - a) / (1 - a) ≤ 1 / (1 - a) := by gcongr
        have := mul_le_mul e1 h5 (by positivity) (by norm_num)
        linarith
    _ = 2 / (1 - a) + 4 := by ring

theorem exp_rpow_bound {l ε γ u : ℝ} (hl : 0 < l) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hu : 0 < u) :
    u ^ (-γ) * Real.exp (-(l * u)) ≤ l ^ (-ε) * u ^ (-(γ + ε)) := by
  have hlu : 0 < l * u := mul_pos hl hu
  have h1 : (l * u) ^ ε ≤ 1 + l * u := by
    rcases le_total (l * u) 1 with h | h
    · have := Real.rpow_le_one hlu.le h hε0.le
      linarith
    · have : (l * u) ^ ε ≤ (l * u) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hε1
      rw [Real.rpow_one] at this
      linarith
  have h2 : (l * u) ^ ε * Real.exp (-(l * u)) ≤ 1 := by
    have : 1 + l * u ≤ Real.exp (l * u) := by linarith [Real.add_one_le_exp (l * u)]
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  rw [Real.mul_rpow hl.le hu.le] at h2
  have hlε : 0 < l ^ ε := Real.rpow_pos_of_pos hl _
  have h3 : u ^ ε * Real.exp (-(l * u)) ≤ l ^ (-ε) := by
    rw [Real.rpow_neg hl.le, ← one_div, le_div_iff₀ hlε]
    linarith
  have h4 : u ^ (-γ) = u ^ (-(γ + ε)) * u ^ ε := by
    rw [← Real.rpow_add hu]; congr 1; ring
  rw [h4, mul_assoc, mul_comm (l ^ (-ε))]
  exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hu.le _)



/-- Singular Gronwall on `[0,1]`: `ψ(t) ≤ A t^{-1/2} + C ∫_0^t (t-r)^{-γ} ψ(r) dr` with
`γ < 1` and `ψ` bounded gives `ψ(1) ≤ C' A`. -/
theorem singular_gronwall (γ C : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (ψ : ℝ → ℝ) (A B : ℝ), 0 ≤ A → ContinuousOn ψ (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc 0 1, 0 ≤ ψ t ∧ ψ t ≤ B) →
      (∀ t ∈ Set.Ioc 0 1, ψ t ≤ A * t ^ (-(1 / 2 : ℝ)) +
        C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) →
      ψ 1 ≤ C' * A := by
  set ε : ℝ := (1 - γ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  set a : ℝ := γ + ε with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha, hε]; linarith
  set K : ℝ := 2 / (1 - a) + 4 with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - a := by linarith
    rw [hK]; positivity
  set l : ℝ := max 1 ((2 * C * K) ^ (1 / ε)) with hl
  have hl1 : 1 ≤ l := le_max_left _ _
  have hl0 : 0 < l := by linarith
  have hlε : 2 * C * K ≤ l ^ ε := by
    have h1 : (2 * C * K) ^ (1 / ε) ≤ l := le_max_right _ _
    have h2 : ((2 * C * K) ^ (1 / ε)) ^ ε ≤ l ^ ε :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hε0.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hε0.ne', Real.rpow_one] at h2
  refine ⟨2 * Real.exp l, by positivity, ?_⟩
  intro ψ A B hA hcont hbd hineq
  set φ : ℝ → ℝ := fun t => t ^ (1 / 2 : ℝ) * Real.exp (-(l * t)) * ψ t with hφ
  have hB0 : 0 ≤ B := (hbd 0 ⟨le_rfl, zero_le_one⟩).1.trans (hbd 0 ⟨le_rfl, zero_le_one⟩).2
  have hφle0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, φ t ≤ B := by
    intro t ht
    have h1 : t ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one ht.1.le ht.2 (by norm_num)
    have h2 : Real.exp (-(l * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have h3 := hbd t ⟨ht.1.le, ht.2⟩
    have h4 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht.1.le _
    have h5 := Real.exp_pos (-(l * t))
    calc φ t = (t ^ (1 / 2 : ℝ) * Real.exp (-(l * t))) * ψ t := rfl
      _ ≤ 1 * B := by
        apply mul_le_mul _ h3.2 h3.1 zero_le_one
        calc t ^ (1 / 2 : ℝ) * Real.exp (-(l * t)) ≤ 1 * 1 :=
              mul_le_mul h1 h2 h5.le zero_le_one
          _ = 1 := one_mul 1
      _ = B := one_mul B
  haveI : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, by norm_num, le_rfl⟩⟩
  set Ψ : ℝ := ⨆ t : Set.Ioc (0 : ℝ) 1, φ t with hΨ
  have hbdd : BddAbove (Set.range fun t : Set.Ioc (0 : ℝ) 1 => φ t) :=
    ⟨B, by rintro _ ⟨t, rfl⟩; exact hφle0 t.1 t.2⟩
  have hφΨ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, φ t ≤ Ψ := fun t ht =>
    le_ciSup hbdd (⟨t, ht⟩ : Set.Ioc (0 : ℝ) 1)
  have hφ_nonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ φ t := by
    intro t ht
    have := (hbd t ⟨ht.1.le, ht.2⟩).1
    have h4 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht.1.le _
    have h5 := Real.exp_pos (-(l * t))
    exact mul_nonneg (mul_nonneg h4 h5.le) this
  have hΨ0 : 0 ≤ Ψ := (hφ_nonneg 1 ⟨by norm_num, le_rfl⟩).trans (hφΨ 1 ⟨by norm_num, le_rfl⟩)
  -- the key estimate
  have key : ∀ t ∈ Set.Ioc (0 : ℝ) 1, φ t ≤ A + (C * K * l ^ (-ε)) * Ψ := by
    intro t ht
    have ht0 := ht.1
    have ht1 := ht.2
    have hψt := hineq t ht
    -- integrability of the singular integrand
    have hcont' : ContinuousOn ψ (Set.uIcc 0 t) := by
      rw [Set.uIcc_of_le ht0.le]
      exact hcont.mono (Set.Icc_subset_Icc le_rfl ht1)
    have hI : IntervalIntegrable (fun r : ℝ => (t - r) ^ (-γ) * ψ r) volume 0 t :=
      (intervalIntegrable_sub_rpow_neg γ hγ1 t).mul_continuousOn hcont'
    set J : ℝ := ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * (Real.exp (-(l * t)) * ψ r) with hJ
    have hJ' : Real.exp (-(l * t)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r = J := by
      rw [hJ, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      ring
    -- pointwise bound
    have hpt : ∀ r ∈ Set.Ioo 0 t, (t - r) ^ (-γ) * (Real.exp (-(l * t)) * ψ r) ≤
        (Ψ * l ^ (-ε)) * ((t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) := by
      intro r hr
      have hr0 := hr.1
      have hr1 : r ≤ 1 := hr.2.le.trans ht1
      have hu : 0 < t - r := by linarith [hr.2]
      have h1 : φ r ≤ Ψ := hφΨ r ⟨hr0, hr1⟩
      have h2 : Real.exp (-(l * r)) * ψ r ≤ Ψ * r ^ (-(1 / 2 : ℝ)) := by
        have hrp : 0 < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
        have : r ^ (-(1 / 2 : ℝ)) * r ^ (1 / 2 : ℝ) = 1 := by
          rw [← Real.rpow_add hr0]; norm_num
        calc Real.exp (-(l * r)) * ψ r
            = r ^ (-(1 / 2 : ℝ)) * (r ^ (1 / 2 : ℝ) * Real.exp (-(l * r)) * ψ r) := by
              rw [← mul_assoc, ← mul_assoc]
              nlinarith [this, mul_nonneg (Real.exp_pos (-(l * r))).le (hbd r ⟨hr0.le, hr1⟩).1]
          _ ≤ r ^ (-(1 / 2 : ℝ)) * Ψ := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hr0.le _)
          _ = Ψ * r ^ (-(1 / 2 : ℝ)) := mul_comm _ _
      have h3 : Real.exp (-(l * t)) * ψ r ≤ Real.exp (-(l * (t - r))) * (Ψ * r ^ (-(1 / 2 : ℝ))) := by
        have : Real.exp (-(l * t)) = Real.exp (-(l * (t - r))) * Real.exp (-(l * r)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      have h4 := exp_rpow_bound (γ := γ) hl0 hε0 hε1 hu
      have h5 : 0 ≤ (t - r) ^ (-γ) := Real.rpow_nonneg hu.le _
      calc (t - r) ^ (-γ) * (Real.exp (-(l * t)) * ψ r)
          ≤ (t - r) ^ (-γ) * (Real.exp (-(l * (t - r))) * (Ψ * r ^ (-(1 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left h3 h5
        _ = ((t - r) ^ (-γ) * Real.exp (-(l * (t - r)))) * (Ψ * r ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ (l ^ (-ε) * (t - r) ^ (-a)) * (Ψ * r ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_right h4 (mul_nonneg hΨ0 (Real.rpow_nonneg hr0.le _))
        _ = (Ψ * l ^ (-ε)) * ((t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) := by ring
    have hkI := kernel_integrableOn a ha0.le ha1 ht0
    have hJmono : J ≤ ∫ r in (0 : ℝ)..t, (Ψ * l ^ (-ε)) * ((t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) := by
      rw [hJ, intervalIntegral.integral_of_le ht0.le, intervalIntegral.integral_of_le ht0.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_mono_on ?_ (hkI.const_mul _) measurableSet_Ioo hpt
      have := (hI.const_mul (Real.exp (-(l * t)))).1.mono_set Set.Ioo_subset_Ioc_self
      refine this.congr_fun (fun r _ => ?_) measurableSet_Ioo
      ring
    rw [intervalIntegral.integral_const_mul] at hJmono
    have hkb := kernel_bound a ha0 ha1 ht0 ht1
    have hst : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    have hex := Real.exp_pos (-(l * t))
    have hex1 : Real.exp (-(l * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have htt : t ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add ht0]; norm_num
    -- assemble
    have hφt : φ t ≤ t ^ (1 / 2 : ℝ) * Real.exp (-(l * t)) *
        (A * t ^ (-(1 / 2 : ℝ)) + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) :=
      mul_le_mul_of_nonneg_left hψt (mul_nonneg hst hex.le)
    have e1 : t ^ (1 / 2 : ℝ) * Real.exp (-(l * t)) *
        (A * t ^ (-(1 / 2 : ℝ)) + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r)
        = A * Real.exp (-(l * t)) * (t ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ))) +
          C * t ^ (1 / 2 : ℝ) * (Real.exp (-(l * t)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) := by
      ring
    rw [e1, htt, hJ'] at hφt
    have e2 : C * t ^ (1 / 2 : ℝ) * J ≤ C * (Ψ * l ^ (-ε)) * K := by
      have h6 : t ^ (1 / 2 : ℝ) * J ≤ t ^ (1 / 2 : ℝ) *
          ((Ψ * l ^ (-ε)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hJmono hst
      have h7 : t ^ (1 / 2 : ℝ) *
          ((Ψ * l ^ (-ε)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) ≤
          (Ψ * l ^ (-ε)) * K := by
        have hc : 0 ≤ Ψ * l ^ (-ε) := mul_nonneg hΨ0 (Real.rpow_nonneg hl0.le _)
        calc t ^ (1 / 2 : ℝ) *
            ((Ψ * l ^ (-ε)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ)))
            = (Ψ * l ^ (-ε)) * (t ^ (1 / 2 : ℝ) *
              ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-(1 / 2 : ℝ))) := by ring
          _ ≤ (Ψ * l ^ (-ε)) * K := mul_le_mul_of_nonneg_left hkb hc
      calc C * t ^ (1 / 2 : ℝ) * J = C * (t ^ (1 / 2 : ℝ) * J) := by ring
        _ ≤ C * ((Ψ * l ^ (-ε)) * K) := mul_le_mul_of_nonneg_left (h6.trans h7) hC
        _ = C * (Ψ * l ^ (-ε)) * K := by ring
    have e3 : A * Real.exp (-(l * t)) * 1 ≤ A := by
      calc A * Real.exp (-(l * t)) * 1 = A * Real.exp (-(l * t)) := mul_one _
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hex1 hA
        _ = A := mul_one A
    calc φ t ≤ A * Real.exp (-(l * t)) * 1 + C * t ^ (1 / 2 : ℝ) * J := hφt
      _ ≤ A + C * (Ψ * l ^ (-ε)) * K := add_le_add e3 e2
      _ = A + (C * K * l ^ (-ε)) * Ψ := by ring
  -- contraction
  have hcoef : C * K * l ^ (-ε) ≤ 1 / 2 := by
    have hlε0 : 0 < l ^ ε := Real.rpow_pos_of_pos hl0 _
    rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, div_le_iff₀ hlε0]
    linarith
  have hΨle : Ψ ≤ A + (1 / 2) * Ψ := by
    refine ciSup_le fun t => (key t.1 t.2).trans ?_
    have := mul_le_mul_of_nonneg_right hcoef hΨ0
    linarith
  have hΨ2 : Ψ ≤ 2 * A := by linarith
  have h1 := hφΨ 1 ⟨by norm_num, le_rfl⟩
  have hφ1 : φ 1 = Real.exp (-l) * ψ 1 := by
    simp only [hφ, Real.one_rpow, mul_one, one_mul]
  rw [hφ1] at h1
  have hexl : Real.exp l * Real.exp (-l) = 1 := by rw [← Real.exp_add]; simp
  calc ψ 1 = Real.exp l * (Real.exp (-l) * ψ 1) := by rw [← mul_assoc, hexl, one_mul]
    _ ≤ Real.exp l * (2 * A) :=
        mul_le_mul_of_nonneg_left (h1.trans hΨ2) (Real.exp_pos _).le
    _ = 2 * Real.exp l * A := by ring


/-! ### The modewise Duhamel formula -/

/-- Modewise Duhamel formula for a solution (variation of constants). -/
theorem mild_eq (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (hν : 0 < ν) (ρc : ℝ → Coeff d) (H : IsMFSolutionHK d s V ν K ρ₀ ρc) (k : Lattice d)
    {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    ρc (v + t) k = (heatMult (ν * t) k : ℂ) * ρc v k +
      ∫ σ in (0 : ℝ)..t, (heatMult (ν * (t - σ)) k : ℂ) *
        (mfRhsCoeff d s V ν (ρc (v + σ)) k - (ν : ℂ) * laplaceCoeff (ρc (v + σ)) k) := by
  set L : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hL
  set c : ℝ := ν * L with hc
  have hR : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Ici 0) :=
    rhs_mode_continuousOn hd s hs0 hsd K hK V ρ₀ hV ν ρc H k
  have hy : ContinuousOn (fun σ => ρc σ k) (Set.Ici 0) := Aux.continuousOn_mode H.cont k
  have hshift : ∀ σ ∈ Set.Ici (0 : ℝ), v + σ ∈ Set.Ici (0 : ℝ) := fun σ hσ =>
    Set.mem_Ici.mpr (add_nonneg hv hσ)
  have hRs : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k) (Set.Ici 0) :=
    hR.comp (continuous_const.add continuous_id).continuousOn hshift
  have hys : ContinuousOn (fun σ => ρc (v + σ) k) (Set.Ici 0) :=
    hy.comp (continuous_const.add continuous_id).continuousOn hshift
  -- the forcing
  set F : ℝ → ℂ := fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k -
    (ν : ℂ) * laplaceCoeff (ρc (v + σ)) k with hF
  have hlap : ∀ w : ℝ, (ν : ℂ) * laplaceCoeff (ρc w) k = -((c : ℝ) : ℂ) * ρc w k := by
    intro w
    simp only [laplaceCoeff, hc, hL]
    push_cast; ring
  have hFeq : ∀ σ, F σ = mfRhsCoeff d s V ν (ρc (v + σ)) k + ((c : ℝ) : ℂ) * ρc (v + σ) k := by
    intro σ; simp only [hF, hlap]; ring
  have hFc : ContinuousOn F (Set.Ici 0) := by
    have : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k +
        ((c : ℝ) : ℂ) * ρc (v + σ) k) (Set.Ici 0) := hRs.add (continuousOn_const.mul hys)
    exact this.congr (fun σ _ => hFeq σ)
  -- the weighted solution
  set z : ℝ → ℂ := fun τ => ((Real.exp (c * τ) : ℝ) : ℂ) * ρc (v + τ) k with hz
  have hzc : ContinuousOn z (Set.Icc 0 t) := by
    refine ContinuousOn.mul ?_ (hys.mono Set.Icc_subset_Ici_self)
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn
  have hzd : ∀ τ ∈ Set.Ioo 0 t, HasDerivAt z (((Real.exp (c * τ) : ℝ) : ℂ) * F τ) τ := by
    intro τ hτ
    have hτ0 : 0 < v + τ := by linarith [hτ.1]
    have h1 : HasDerivAt (fun τ' => ρc (v + τ') k) (mfRhsCoeff d s V ν (ρc (v + τ)) k) τ :=
      (hasDerivAt_coeff hd s hs0 hsd K hK V ρ₀ hV ν ρc H k hτ0).comp_const_add v τ
    have h2 : HasDerivAt (fun τ' : ℝ => ((Real.exp (c * τ') : ℝ) : ℂ))
        (((c * Real.exp (c * τ) : ℝ) : ℂ)) τ := by
      have h3 : HasDerivAt (fun y : ℝ => c * y) c τ := by
        simpa using (hasDerivAt_id τ).const_mul c
      exact (h3.exp.congr_deriv (by ring)).ofReal_comp
    refine (h2.mul h1).congr_deriv ?_
    rw [hFeq]; push_cast; ring
  have hFI : IntervalIntegrable (fun σ => ((Real.exp (c * σ) : ℝ) : ℂ) * F σ) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht]
    refine ContinuousOn.mul ?_ (hFc.mono Set.Icc_subset_Ici_self)
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hzc hzd hFI
  have hz0 : z 0 = ρc v k := by simp [hz]
  have hzt : z t = ((Real.exp (c * t) : ℝ) : ℂ) * ρc (v + t) k := rfl
  rw [hz0, hzt] at hftc
  -- conclusion
  have hheat : ∀ τ : ℝ, (heatMult (ν * τ) k : ℂ) = ((Real.exp (-(c * τ)) : ℝ) : ℂ) := by
    intro τ
    simp only [heatMult, hc, hL]
    congr 2; ring
  have hint : ∫ σ in (0 : ℝ)..t, (heatMult (ν * (t - σ)) k : ℂ) * F σ =
      ((Real.exp (-(c * t)) : ℝ) : ℂ) *
        ∫ σ in (0 : ℝ)..t, ((Real.exp (c * σ) : ℝ) : ℂ) * F σ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [hheat]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring
  rw [hint, hheat, hftc]
  have h1 : ((Real.exp (-(c * t)) : ℝ) : ℂ) * ((Real.exp (c * t) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  calc ρc (v + t) k = (((Real.exp (-(c * t)) : ℝ) : ℂ) * ((Real.exp (c * t) : ℝ) : ℂ)) * ρc (v + t) k := by
        rw [h1, one_mul]
    _ = _ := by ring

end HRS.PDE.MFApriori
