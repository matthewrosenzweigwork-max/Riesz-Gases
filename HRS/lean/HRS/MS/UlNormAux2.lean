import HRS.MS.UlNormAux1

/-!
# UL-0, part 2: the Sobolev norm through derivatives; lower semicontinuity; closure facts

* `ul0_sobE_sq_derivs` / `sobolevNormE_le_derivs`: for `g ∈ C_c^m` the identity
  `‖g‖²_{H^m} = ∑_{n ≤ m} C(m,n) ∑_{i : Fin n → Fin d} ‖∂^i g‖²_{L²}` (the symbol identity
  `(1 + 4π²|ξ|²)^m = ∑_n C(m,n) ∑_i ∏_t (2π ξ_{i_t})²`), hence the converse of `um_deriv_le`.
* `ulocNormE_lsc`: lower semicontinuity of `ulocNormE` under pointwise convergence.  *Adjustment of the
  sketch (harmless, documented)*: the sequence is assumed uniformly bounded, `|u_n x| ≤ B`; then
  `χ(·-z) u_n → χ(·-z) u` in `L²` by dominated convergence, hence `fourierL2` converges in `L²` and
  Fatou on the Fourier side applies along an a.e. convergent subsequence.
* closure facts: `ulClosure_cb`, `ulClosure_mono`, `ulClosure_of_op`, `ulClosure_of_decay`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform

namespace HRS.MS.Ul
open HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW

variable {d : ℕ}

/-! ### The Fourier transform of `∂^i g` -/

theorem ul0_fourier_partial_eq {m : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ m g) (hc : HasCompactSupport g)
    {n : ℕ} (hn : n ≤ m) (i : Fin n → Fin d) (w : Euc d) :
    ‖𝓕 (fun x : Euc d => ((partialDeriv i g x : ℝ) : ℂ)) w‖ =
      (2 * Real.pi) ^ n * (∏ t, |w (i t)|) * ‖𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) w‖ := by
  set f : Euc d → ℂ := fun x => ((g x : ℝ) : ℂ) with hf
  have hfc : HasCompactSupport f := hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hfd : ContDiff ℝ (m : ℕ∞) f := by
    have := Complex.ofRealCLM.contDiff.comp hg
    exact_mod_cast this
  have hint : ∀ k : ℕ, k ≤ (m : ℕ∞) → Integrable (iteratedFDeriv ℝ k f) volume := by
    intro k hk
    have hk' : (k : WithTop ℕ∞) ≤ (m : ℕ∞) := by exact_mod_cast hk
    exact (hfd.continuous_iteratedFDeriv hk').integrable_of_hasCompactSupport (hfc.iteratedFDeriv k)
  have key := Real.fourier_iteratedFDeriv hfd hint (n := n) (by exact_mod_cast hn)
  have h1 := congrFun key w
  have h2 := congrArg (fun T => T (fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))) h1
  rw [Real.fourier_continuousMultilinearMap_apply (hint n (by exact_mod_cast hn))] at h2
  have hfun : (fun x : Euc d => (iteratedFDeriv ℝ n f x) fun t => (EuclideanSpace.single (i t) (1:ℝ) : Euc d)) =
      fun x : Euc d => ((partialDeriv i g x : ℝ) : ℂ) := by
    ext x
    have hx : f = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ g := rfl
    have hgx : ContDiffAt ℝ (n : ℕ∞) g x := (hg.of_le (by exact_mod_cast hn)).contDiffAt
    rw [hx, ContinuousLinearMap.iteratedFDeriv_comp_left _ hgx le_rfl]
    rfl
  rw [hfun] at h2
  rw [h2, VectorFourier.fourierPowSMulRight_apply]
  rw [norm_smul, norm_smul, norm_pow, norm_neg]
  have hb : ∀ t : Fin n, ‖((-(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w)
      (EuclideanSpace.single (i t) (1:ℝ))‖ = |w (i t)| := by
    intro t
    simp only [neg_apply, innerSL_apply_apply, norm_neg]
    rw [real_inner_comm, EuclideanSpace.inner_single_left]
    simp
  have hprod : ‖∏ t : Fin n, ((-(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) w)
      (EuclideanSpace.single (i t) (1:ℝ))‖ = ∏ t, |w (i t)| := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun t _ => hb t
  have hI : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [hI, hprod, mul_assoc]

/-- the symbol identity -/
theorem ul0_poly_id (m : ℕ) (ξ : Euc d) :
    ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ) *
      ∑ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 =
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m := by
  have hinner : ∀ n : ℕ, ∑ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 =
      (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ n := by
    intro n
    have h1 : ∀ i : Fin n → Fin d, ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 =
        (4 * Real.pi ^ 2) ^ n * ∏ t, (ξ (i t)) ^ 2 := by
      intro i
      rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, mul_pow, ← Finset.prod_pow]
      simp only [sq_abs]
      norm_num
    simp_rw [h1]
    rw [← Finset.mul_sum]
    have h2 : ∑ i : Fin n → Fin d, ∏ t, (ξ (i t)) ^ 2 = (∑ j : Fin d, (ξ j) ^ 2) ^ n := by
      have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin d)))
        (fun _ j => (ξ j) ^ 2)
      rw [Fintype.piFinset_univ] at this
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this.symm
    have hn2 : ‖ξ‖ ^ 2 = ∑ j, (ξ j) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [h2, ← hn2, ← mul_pow]
  simp_rw [hinner]
  rw [add_comm (1 : ℝ), add_pow]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [mul_comm]

theorem ul0_sobE_sq_derivs {m : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ m g) (hc : HasCompactSupport g) :
    sobolevNormE (m : ℝ) g ^ 2 = ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ≥0∞) *
      ∑ i : Fin n → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2) := by
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hc
  have hg1 : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have hFm : AEMeasurable (fun ξ : Euc d => ‖fourierL2 g ξ‖ ^ 2) volume :=
    (aesm_sq (aestronglyMeasurable_fourierL2 hg2)).aemeasurable
  -- each derivative term as a Fourier-side integral
  have hterm : ∀ n : ℕ, n ≤ m → ∀ i : Fin n → Fin d,
      ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2) := by
    intro n hn i
    set p : Euc d → ℝ := partialDeriv i g with hp
    have hpc : Continuous p := by
      have h1 : Continuous (iteratedFDeriv ℝ n g) := hg.continuous_iteratedFDeriv (by exact_mod_cast hn)
      exact (continuous_eval_const (fun t : Fin n => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))).comp h1
    have hpcs : HasCompactSupport p := by
      have := (hc.iteratedFDeriv n).comp_left (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ =>
        T (fun t : Fin n => (EuclideanSpace.single (i t) (1:ℝ) : Euc d))) (by simp)
      exact this
    have hp2 : MemLp p 2 volume := hpc.memLp_of_hasCompactSupport hpcs
    have hp1 : Integrable p := hpc.integrable_of_hasCompactSupport hpcs
    have e1 : ∫⁻ x, ENNReal.ofReal (p x ^ 2) = ∫⁻ ξ, ENNReal.ofReal (‖fourierL2 p ξ‖ ^ 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hp2.integrable_sq (Filter.Eventually.of_forall fun x => sq_nonneg _),
        ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_fourierL2 hp2)
          (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_norm_sq_fourierL2 hp2]
    rw [e1]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 hp1 hp2, um_L1L2 hg1 hg2] with ξ h1 h2
    rw [h1, hp, ul0_fourier_partial_eq hg hc hn i ξ, h2]
    congr 1
    ring
  rw [um_sobE_sq hg2]
  have hm_meas : ∀ n : ℕ, ∀ i : Fin n → Fin d, AEMeasurable (fun ξ : Euc d =>
      ENNReal.ofReal (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2)) volume := by
    intro n i
    have hc1 : Continuous (fun ξ : Euc d => ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2) := by
      fun_prop
    exact (hc1.aemeasurable.mul hFm).ennreal_ofReal
  have hsum_meas : ∀ n : ℕ, AEMeasurable (fun ξ : Euc d => ∑ i : Fin n → Fin d, ENNReal.ofReal
      (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2)) volume := fun n =>
    Finset.aemeasurable_fun_sum _ fun i _ => hm_meas n i
  calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 g ξ‖ ^ 2)
      = ∫⁻ ξ, ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ≥0∞) *
          ∑ i : Fin n → Fin d, ENNReal.ofReal
            (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2) := by
        refine lintegral_congr fun ξ => ?_
        have h0 : ∀ n, ∀ i : Fin n → Fin d,
            0 ≤ ((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2 := fun n i => by positivity
        have : ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ≥0∞) *
            ∑ i : Fin n → Fin d, ENNReal.ofReal
              (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2) =
            ENNReal.ofReal (∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ) *
              ∑ i : Fin n → Fin d, (((2 * Real.pi) ^ n * ∏ t, |ξ (i t)|) ^ 2 * ‖fourierL2 g ξ‖ ^ 2)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _)
            (Finset.sum_nonneg fun i _ => h0 n i))]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 n i)]
        rw [this]
        congr 1
        have hw : wt ξ ^ (m : ℝ) = (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ m := by
          rw [Real.rpow_natCast]; rfl
        rw [hw, ← ul0_poly_id m ξ, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mul_assoc, Finset.sum_mul]
    _ = ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ≥0∞) *
          ∑ i : Fin n → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2) := by
        rw [lintegral_finset_sum' _ (fun n _ => (hsum_meas n).const_mul _)]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [lintegral_const_mul'' _ (hsum_meas n), lintegral_finset_sum' _ (fun i _ => hm_meas n i)]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (hterm n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) i).symm


/-- **UL-0 `sobolevNormE_le_derivs`** (converse of `um_deriv_le`): for `g ∈ C_c^m`,
`‖g‖²_{H^m} ≤ 2^m ∑_{n ≤ m} ∑_{i : Fin n → Fin d} ‖∂^i g‖²_{L²}`
(in fact the identity `ul0_sobE_sq_derivs` holds).  Squared form, in `ℝ≥0∞`. -/
theorem sobolevNormE_le_derivs (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Euc d → ℝ, ContDiff ℝ m g → HasCompactSupport g →
      sobolevNormE (m : ℝ) g ^ 2 ≤ ENNReal.ofReal C * ∑ n ∈ Finset.range (m + 1),
        ∑ i : Fin n → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2) := by
  refine ⟨2 ^ m, by positivity, fun g hg hc => ?_⟩
  rw [ul0_sobE_sq_derivs hg hc, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have h1 : (m.choose n : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [show ((2 : ℝ) ^ m) = ((2 ^ m : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast]
    exact_mod_cast Nat.choose_le_two_pow m n
  gcongr

/-- the norm of `g ∈ C_c^m` supported in `closedBall 0 R` with derivatives bounded by `M` -/
theorem ul0_sobE_le_sup {m : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ m g) (hc : HasCompactSupport g)
    (R M : ℝ) (hR : tsupport g ⊆ Metric.closedBall 0 R) (hM0 : 0 ≤ M)
    (hM : ∀ n ≤ m, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ M) :
    sobolevNormE (m : ℝ) g ≤ ENNReal.ofReal (Real.sqrt ((1 + d) ^ m *
      (volume (Metric.closedBall (0 : Euc d) R)).toReal) * M) := by
  set V : ℝ≥0∞ := volume (Metric.closedBall (0 : Euc d) R) with hV
  have hVfin : V ≠ ⊤ := measure_closedBall_lt_top.ne
  have hterm : ∀ n ≤ m, ∀ i : Fin n → Fin d,
      ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2) ≤ ENNReal.ofReal (M ^ 2) * V := by
    intro n hn i
    calc ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2)
        ≤ ∫⁻ x, (Metric.closedBall (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (M ^ 2)) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ Metric.closedBall (0 : Euc d) R
          · rw [Set.indicator_of_mem hx]
            apply ENNReal.ofReal_le_ofReal
            have h1 : |partialDeriv i g x| ≤ M := by
              have := (iteratedFDeriv ℝ n g x).le_opNorm
                (fun l => (EuclideanSpace.single (i l) (1 : ℝ) : Euc d))
              have h2 : ∏ l : Fin n, ‖(EuclideanSpace.single (i l) (1 : ℝ) : Euc d)‖ = 1 := by simp
              rw [h2, mul_one] at this
              have h3 := hM n hn x
              unfold partialDeriv
              rw [← Real.norm_eq_abs]
              exact this.trans h3
            nlinarith [abs_nonneg (partialDeriv i g x), sq_abs (partialDeriv i g x)]
          · rw [Set.indicator_of_notMem hx]
            have hx' : x ∉ tsupport g := fun h => hx (hR h)
            have : iteratedFDeriv ℝ n g x = 0 := by
              by_contra hne
              exact hx' (support_iteratedFDeriv_subset (𝕜 := ℝ) n hne)
            have h0 : partialDeriv i g x = 0 := by
              unfold partialDeriv; rw [this]; rfl
            rw [h0]; simp
      _ = ENNReal.ofReal (M ^ 2) * V := by
          rw [lintegral_indicator_const measurableSet_closedBall]
  have hS2 : sobolevNormE (m : ℝ) g ^ 2 ≤ ((1 + d : ℝ≥0∞)) ^ m * (ENNReal.ofReal (M ^ 2) * V) := by
    rw [ul0_sobE_sq_derivs hg hc]
    calc ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ≥0∞) *
          ∑ i : Fin n → Fin d, ∫⁻ x, ENNReal.ofReal ((partialDeriv i g x) ^ 2)
        ≤ ∑ n ∈ Finset.range (m + 1), (m.choose n : ℝ≥0∞) *
          ∑ _i : Fin n → Fin d, (ENNReal.ofReal (M ^ 2) * V) := by
          refine Finset.sum_le_sum fun n hn => ?_
          gcongr with i hi
          exact hterm n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) i
      _ = ∑ n ∈ Finset.range (m + 1), ((d : ℝ≥0∞) ^ n * 1 ^ (m - n) * (m.choose n : ℝ≥0∞)) *
            (ENNReal.ofReal (M ^ 2) * V) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_const, Finset.card_univ]
          simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, one_pow, mul_one]
          ring
      _ = ((1 + d : ℝ≥0∞)) ^ m * (ENNReal.ofReal (M ^ 2) * V) := by
          rw [← Finset.sum_mul, add_comm (1 : ℝ≥0∞), add_pow]
  have hK : ((1 + d : ℝ≥0∞)) ^ m * (ENNReal.ofReal (M ^ 2) * V) =
      ENNReal.ofReal (Real.sqrt ((1 + d) ^ m * V.toReal) * M) ^ 2 := by
    have h1 : ((1 + d : ℝ≥0∞)) ^ m = ENNReal.ofReal ((1 + d : ℝ) ^ m) := by
      rw [ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
      simp
    have hVr : V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hVfin).symm
    conv_lhs => rw [h1, hVr]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    congr 1
    ring
  rw [hK] at hS2
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hS2


/-! ### Closure facts -/

/-- `ulNormE` is finite on `C_c^∞ + const` -/
theorem ul0_ulNormE_ccc_lt_top (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (g : Euc d → ℝ)
    (hg : IsCcInftyPlusConst g) : ulNormE k θ g < ⊤ := by
  obtain ⟨h, c, hh, hhc, rfl⟩ := hg
  refine lt_of_le_of_lt (ul0_ulNormE_add k θ h (fun _ => c)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · obtain ⟨C, hC, hmul⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (k : ℝ)
      (Nat.cast_nonneg k) θ hθ.1 hθ.2.1
    have hfin := HRS.MS.UlocMW.um_chi_finite hh hhc (s := (k : ℝ)) (Nat.cast_nonneg k)
    refine lt_of_le_of_lt (iSup_le fun z => ?_ : ulNormE k θ h ≤ ENNReal.ofReal C *
      sobolevNormE (k : ℝ) h) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top)
    exact hmul (latticePt z) h
  · have hfin := HRS.MS.UlocMW.um_chi_finite (χ := fun y => c * θ y) (contDiff_const.mul hθ.1)
      (hθ.2.1.mul_left) (s := (k : ℝ)) (Nat.cast_nonneg k)
    refine lt_of_le_of_lt (iSup_le fun z => ?_ : ulNormE k θ (fun _ => c) ≤
      sobolevNormE (k : ℝ) (fun y => c * θ y)) hfin.lt_top
    have e : (fun x => θ (x - latticePt z) * c) = fun x => (fun y => c * θ y) (x - latticePt z) := by
      funext x; simp [mul_comm]
    rw [e]
    exact (HRS.MS.SobMul.sobolevNormE_translate (k : ℝ) (fun y => c * θ y) (latticePt z)).le

theorem ul0_closure_sub_ccc (k : ℕ) (θ : Euc d → ℝ) {f g : Euc d → ℝ} (hf : UlClosure k θ f)
    (hg : IsCcInftyPlusConst g) : UlClosure k θ (fun x => f x - g x) := by
  obtain ⟨h, c, hh, hhc, rfl⟩ := hg
  refine ⟨hf.1.sub (((contDiff_infty.1 hh 2)).add contDiff_const), fun ε hε => ?_⟩
  obtain ⟨g', ⟨h', c', hh', hhc', hg'⟩, hle⟩ := hf.2 ε hε
  refine ⟨fun x => h' x - h x + (c' - c), ⟨fun x => h' x - h x, c' - c, hh'.sub hh, hhc'.sub hhc, rfl⟩, ?_⟩
  have e : (fun x => (f x - (h x + c)) - (h' x - h x + (c' - c))) = fun x => f x - g' x := by
    funext x
    have := congrFun hg' x
    rw [this]; ring
  rw [e]; exact hle

theorem ulClosure_mono {k₁ k : ℕ} (h : k ≤ k₁) (θ f : Euc d → ℝ) (hf : UlClosure k₁ θ f) :
    UlClosure k θ f :=
  ⟨hf.1, fun ε hε => by
    obtain ⟨g, hg, hle⟩ := hf.2 ε hε
    exact ⟨g, hg, (ul0_ulNormE_mono h θ _).trans hle⟩⟩

theorem ul0_ulNormE_lt_top_of_closure (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) {f : Euc d → ℝ}
    (hf : UlClosure k θ f) : ulNormE k θ f < ⊤ := by
  obtain ⟨g, hg, hle⟩ := hf.2 1 one_pos
  exact lt_of_le_of_lt (ul0_ulNormE_sub_le k θ f g)
    (ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt hle ENNReal.ofReal_lt_top,
      ul0_ulNormE_ccc_lt_top k θ hθ g hg⟩)

/-- **UL-0 `ulClosure_cb`**: elements of the closure are in `C_b^j` for `j + d/2 < k`, with the bound. -/
theorem ulClosure_cb (k j : ℕ) (hkj : (j : ℝ) + (d : ℝ) / 2 < k) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euc d → ℝ, UlClosure k θ f →
      HRS.MemCb j f ∧ HRS.cbNorm j f ≤ C * (ulNormE k θ f).toReal := by
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := ul_equiv k θ χ hθ hχ
  obtain ⟨C1, h1⟩ := HRS.MS.UlocCb.uloc_embedding_cb_proof k j hkj χ hχ
  refine ⟨max C1 0 * Ce + 1, by positivity, fun f hf => ?_⟩
  have hfin := ul0_ulNormE_lt_top_of_closure k θ hθ hf
  have hfin' : ulocNormE k χ f < ⊤ :=
    lt_of_le_of_lt (hequ f).2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  obtain ⟨v, hvae, hv, hvb⟩ := h1 f hfin'
  have hvf : v = f := (Continuous.ae_eq_iff_eq volume hv.1.continuous hf.1.continuous).1 hvae
  subst hvf
  refine ⟨hv, hvb.trans ?_⟩
  have h2 : (ulocNormE k χ v).toReal ≤ Ce * (ulNormE k θ v).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) (hequ v).2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCe.le] at this
  have h3 : 0 ≤ (ulocNormE k χ v).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ulNormE k θ v).toReal := ENNReal.toReal_nonneg
  calc C1 * (ulocNormE k χ v).toReal ≤ max C1 0 * (ulocNormE k χ v).toReal :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h3
    _ ≤ max C1 0 * (Ce * (ulNormE k θ v).toReal) :=
        mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = max C1 0 * Ce * (ulNormE k θ v).toReal := by ring
    _ ≤ (max C1 0 * Ce + 1) * (ulNormE k θ v).toReal := by nlinarith

/-- **UL-0 `ulClosure_of_op`**: a linear operator, bounded on the closure, with `C²` values on the closure,
mapping `C_c^∞ + const` into the closure, maps the closure into the closure.  (The hypothesis `hC2` is the
adjustment of the sketch: the `C²` requirement of `UlClosure` cannot be recovered from the norm limit
without an embedding, and it is cheaply available in the applications.) -/
theorem ulClosure_of_op (k : ℕ) (θ : Euc d → ℝ) (T : (Euc d → ℝ) → (Euc d → ℝ))
    (hlin : ∀ f g : Euc d → ℝ, T (fun x => f x - g x) = fun x => T f x - T g x)
    (C : ℝ) (hC : 0 ≤ C)
    (hbd : ∀ f, UlClosure k θ f → ulNormE k θ (T f) ≤ ENNReal.ofReal C * ulNormE k θ f)
    (hC2 : ∀ f, UlClosure k θ f → ContDiff ℝ 2 (T f))
    (hdense : ∀ g, IsCcInftyPlusConst g → UlClosure k θ (T g)) :
    ∀ f, UlClosure k θ f → UlClosure k θ (T f) := by
  intro f hf
  refine ⟨hC2 f hf, fun ε hε => ?_⟩
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨g, hg, hle⟩ := hf.2 δ hδpos
  have hfg : UlClosure k θ (fun x => f x - g x) := ul0_closure_sub_ccc k θ hf hg
  obtain ⟨g', hg', hle'⟩ := (hdense g hg).2 (ε / 2) (by positivity)
  refine ⟨g', hg', ?_⟩
  have e : (fun x => T f x - g' x) = fun x => (T (fun x => f x - g x) x) + (T g x - g' x) := by
    funext x
    rw [hlin f g]; ring
  rw [e]
  refine (ul0_ulNormE_add k θ _ _).trans ?_
  have h1 : ulNormE k θ (T fun x => f x - g x) ≤ ENNReal.ofReal (ε / 2) := by
    refine (hbd _ hfg).trans ?_
    calc ENNReal.ofReal C * ulNormE k θ (fun x => f x - g x) ≤ ENNReal.ofReal C * ENNReal.ofReal δ := by
          gcongr
      _ = ENNReal.ofReal (C * δ) := (ENNReal.ofReal_mul hC).symm
      _ ≤ ENNReal.ofReal (ε / 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hδ]
          rw [show C * (ε / (2 * (C + 1))) = (C / (C + 1)) * (ε / 2) by field_simp]
          have : C / (C + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          nlinarith [div_nonneg hC (by positivity : (0 : ℝ) ≤ C + 1)]
  calc _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add h1 hle'
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring


/-! ### Closure of functions with decaying derivatives -/

/-- a bound for `ulNormE` by uniform sup bounds of the derivatives -/
theorem ul0_ulNormE_le_sup (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Euc d → ℝ, ContDiff ℝ ∞ w → ∀ η : ℝ, 0 ≤ η →
      (∀ n ≤ k, ∀ y, ‖iteratedFDeriv ℝ n w y‖ ≤ η) → ulNormE k θ w ≤ ENNReal.ofReal (K * η) := by
  obtain ⟨Rθ, hRθ⟩ := hθ.2.1.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hBθ : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ n θ x‖ ≤ B := by
    intro n
    have hcont : Continuous (iteratedFDeriv ℝ n θ) := hθ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hθ.2.1.iteratedFDeriv n)
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBθ
  set Bθ : ℝ := ∑ n ∈ Finset.range (k + 1), B n with hBθdef
  have hBn : ∀ n ≤ k, B n ≤ Bθ := fun n hn =>
    Finset.single_le_sum (f := B) (fun n _ => hB0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  have hBθ0 : 0 ≤ Bθ := Finset.sum_nonneg fun n _ => hB0 n
  refine ⟨Real.sqrt ((1 + d) ^ k * (volume (Metric.closedBall (0 : Euc d) (max Rθ 0))).toReal) *
    (2 ^ k * Bθ), by positivity, fun w hw η hη hwη => ?_⟩
  refine iSup_le fun z => ?_
  have e : (fun x => θ (x - latticePt z) * w x) = fun x => (fun y => θ y * w (y + latticePt z)) (x - latticePt z) := by
    funext x; simp
  rw [e]
  refine (HRS.MS.SobMul.sobolevNormE_translate (k : ℝ) (fun y => θ y * w (y + latticePt z))
    (latticePt z)).le.trans ?_
  set g : Euc d → ℝ := fun y => θ y * w (y + latticePt z) with hg
  have hwc : ∀ N : ℕ, ContDiff ℝ N w := fun N => contDiff_infty.1 hw N
  have hgc : ContDiff ℝ k g := (contDiff_infty.1 hθ.1 k).mul
    ((hwc k).comp (contDiff_id.add contDiff_const))
  have hgcs : HasCompactSupport g := hθ.2.1.mul_right
  have hts : tsupport g ⊆ Metric.closedBall 0 (max Rθ 0) := by
    intro x hx
    have : x ∈ tsupport θ := tsupport_mul_subset_left hx
    have := hRθ this
    simp only [Metric.mem_closedBall, dist_zero_right] at this ⊢
    exact this.trans (le_max_left _ _)
  have hbound : ∀ n ≤ k, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ 2 ^ k * Bθ * η := by
    intro n hn x
    have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (contDiff_infty.1 hθ.1 k)
      ((hwc k).comp (contDiff_id.add contDiff_const : ContDiff ℝ k fun y : Euc d => y + latticePt z)) x
      (n := n) (by exact_mod_cast hn)
    refine h1.trans ?_
    have hsh : ∀ j, iteratedFDeriv ℝ j (fun y => w (y + latticePt z)) x = iteratedFDeriv ℝ j w (x + latticePt z) := by
      intro j
      rw [iteratedFDeriv_comp_add_right]
    calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Bθ * η := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          have e1 : ‖iteratedFDeriv ℝ i θ x‖ ≤ Bθ := (hB i x).trans (hBn i (hi'.trans hn))
          have e2 : ‖iteratedFDeriv ℝ (n - i) (fun y => w (y + latticePt z)) x‖ ≤ η := by
            rw [hsh]; exact hwη (n - i) ((Nat.sub_le _ _).trans hn) _
          have h0 : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul (mul_le_mul_of_nonneg_left e1 h0) e2 (norm_nonneg _)
            (mul_nonneg h0 hBθ0)
      _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * Bθ * η := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 ^ k * Bθ * η := by
          have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
          have h2k : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2k hBθ0) hη
  have hbd := ul0_sobE_le_sup hgc hgcs (max Rθ 0) (2 ^ k * Bθ * η) hts (by positivity) hbound
  refine hbd.trans (le_of_eq ?_)
  congr 1
  ring

/-- `1 - ψ` has bounded derivatives and `D^i (1 - χ(R⁻¹ ·))` for `i ≥ 1` is `-` the scaled derivative -/
theorem ul0_iteratedFDeriv_one_sub_scaled (χ : Euc d → ℝ) (hχ : ContDiff ℝ ∞ χ) (R : ℝ) (i : ℕ) (hi : i ≠ 0)
    (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun x => 1 - χ (R⁻¹ • x)) y‖ ≤ |R⁻¹| ^ i * ‖iteratedFDeriv ℝ i χ (R⁻¹ • y)‖ := by
  have hc : ContDiff ℝ i (fun x : Euc d => χ (R⁻¹ • x)) :=
    (contDiff_infty.1 hχ i).comp (contDiff_const_smul R⁻¹)
  have e : iteratedFDeriv ℝ i (fun x => 1 - χ (R⁻¹ • x)) y =
      - iteratedFDeriv ℝ i (fun x => χ (R⁻¹ • x)) y := by
    have e0 : (fun x : Euc d => 1 - χ (R⁻¹ • x)) = (fun _ => (1 : ℝ)) - fun x => χ (R⁻¹ • x) := rfl
    rw [e0, iteratedFDeriv_sub_apply contDiff_const.contDiffAt hc.contDiffAt,
      iteratedFDeriv_const_of_ne hi]
    simp
  rw [e, norm_neg, iteratedFDeriv_comp_const_smul R⁻¹ (contDiff_infty.1 hχ i)]
  rw [norm_smul, Real.norm_eq_abs, abs_pow]

theorem ul0_iteratedFDeriv_sub_const (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (c : ℝ) (j : ℕ) (hj : j ≠ 0)
    (y : Euc d) : iteratedFDeriv ℝ j (fun x => f x - c) y = iteratedFDeriv ℝ j f y := by
  have e : (fun x : Euc d => f x - c) = f - fun _ => c := rfl
  rw [e, iteratedFDeriv_sub_apply (contDiff_infty.1 hf j).contDiffAt contDiff_const.contDiffAt,
    iteratedFDeriv_const_of_ne hj]
  simp

/-- **UL-0 `ulClosure_of_decay`**: a smooth function converging to a constant at infinity, whose derivatives of
orders `1..k` tend to `0` at infinity, lies in `UlClosure k θ` (approximation `χ(·/R)(f - c) + c`). -/
theorem ulClosure_of_decay (k : ℕ) (θ : Euc d → ℝ) (hθ : IsUlCutoff θ) (f : Euc d → ℝ) (c : ℝ)
    (hf : ContDiff ℝ ∞ f)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ → |f x - c| ≤ ε)
    (hder : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ j f x‖ ≤ ε) :
    UlClosure k θ f := by
  refine ⟨contDiff_infty.1 hf 2, fun ε hε => ?_⟩
  obtain ⟨χ, hχ⟩ := ul0_exists_ulocCutoff d
  obtain ⟨K, hK0, hK⟩ := ul0_ulNormE_le_sup k θ hθ
  -- bound of the derivatives of χ
  have hBχ : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ n χ x‖ ≤ B := by
    intro n
    have hcont : Continuous (iteratedFDeriv ℝ n χ) := hχ.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support (hχ.2.1.iteratedFDeriv n)
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBχ
  set B0 : ℝ := ∑ n ∈ Finset.range (k + 1), B n with hB0def
  have hBn : ∀ n ≤ k, B n ≤ B0 := fun n hn =>
    Finset.single_le_sum (f := B) (fun n _ => hB0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  have hB00 : 0 ≤ B0 := Finset.sum_nonneg fun n _ => hB0 n
  set B1 : ℝ := max 1 B0 with hB1
  have hB1pos : 0 < B1 := lt_of_lt_of_le one_pos (le_max_left _ _)
  set η : ℝ := ε / ((K + 1) * 1) with hηdef
  -- the target size of the derivatives of `w_R`
  set η1 : ℝ := ε / ((K + 1) * (2 ^ k * B1)) with hη1
  have hη1pos : 0 < η1 := by positivity
  -- decay of `f - c` and its derivatives
  have hdecay : ∀ᶠ R in atTop, ∀ j ∈ Finset.range (k + 1), ∀ x : Euc d, R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ j (fun x => f x - c) x‖ ≤ η1 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      obtain ⟨R, hR⟩ := hlim η1 hη1pos
      filter_upwards [Filter.eventually_ge_atTop R] with R' hR' x hx
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact hR x (hR'.trans hx)
    · obtain ⟨R, hR⟩ := hder j (Nat.one_le_iff_ne_zero.2 hj0)
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) η1 hη1pos
      filter_upwards [Filter.eventually_ge_atTop R] with R' hR' x hx
      rw [ul0_iteratedFDeriv_sub_const f hf c j hj0]
      exact hR x (hR'.trans hx)
  obtain ⟨R0, hR0⟩ := (hdecay.and (Filter.eventually_ge_atTop (1 : ℝ))).exists
  -- the approximating function
  set R : ℝ := R0 with hRdef
  have hR1 : 1 ≤ R := hR0.2
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  set ψ : Euc d → ℝ := fun x => χ (R⁻¹ • x) with hψ
  have hψs : ContDiff ℝ ∞ ψ := hχ.1.comp (contDiff_const_smul R⁻¹)
  have hψc : HasCompactSupport ψ := by
    have := hχ.2.1.comp_isClosedEmbedding (g := fun x : Euc d => R⁻¹ • x)
      (by
        refine (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hRpos.ne')).isClosedEmbedding)
    exact this
  refine ⟨fun x => ψ x * (f x - c) + c, ⟨fun x => ψ x * (f x - c), c, hψs.mul (hf.sub contDiff_const),
    hψc.mul_right, rfl⟩, ?_⟩
  set w : Euc d → ℝ := fun x => f x - (ψ x * (f x - c) + c) with hw
  have hwe : w = fun x => (1 - χ (R⁻¹ • x)) * (f x - c) := by
    funext x; simp only [hw, hψ]; ring
  have hws : ContDiff ℝ ∞ w := by
    rw [hwe]
    exact (contDiff_const.sub hψs).mul (hf.sub contDiff_const)
  have hwb : ∀ n ≤ k, ∀ y, ‖iteratedFDeriv ℝ n w y‖ ≤ 2 ^ k * B1 * η1 := by
    intro n hn y
    by_cases hy : ‖y‖ < R
    · -- `w` vanishes near `y`
      have hev : w =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have hop : IsOpen {x : Euc d | ‖x‖ < R} := isOpen_lt continuous_norm continuous_const
        filter_upwards [hop.mem_nhds hy] with x hx
        have : χ (R⁻¹ • x) = 1 := by
          apply hχ.2.2.2.2
          rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
          have : ‖x‖ < R := hx
          rw [inv_mul_le_iff₀ hRpos]; linarith
        rw [hwe]; simp [this]
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev n).eq_of_nhds]
      have : iteratedFDeriv ℝ n (fun _ : Euc d => (0 : ℝ)) y = 0 := by
        have := iteratedFDeriv_zero_fun (𝕜 := ℝ) (E := Euc d) (F := ℝ) (n := n)
        exact congrFun this y
      rw [this, norm_zero]
      positivity
    · have hyR : R ≤ ‖y‖ := not_lt.1 hy
      rw [hwe]
      have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun x : Euc d => 1 - χ (R⁻¹ • x))
        (g := fun x => f x - c) (N := (k : ℕ∞ω))
        (contDiff_const.sub (hχ.1.comp (contDiff_const_smul R⁻¹) |>.of_le (by exact_mod_cast le_top)))
        ((hf.sub contDiff_const).of_le (by exact_mod_cast le_top)) y (n := n) (by exact_mod_cast hn)
      refine h1.trans ?_
      calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B1 * η1 := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            have e1 : ‖iteratedFDeriv ℝ i (fun x : Euc d => 1 - χ (R⁻¹ • x)) y‖ ≤ B1 := by
              by_cases hi0 : i = 0
              · subst hi0
                rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
                have h0 := (hχ.2.2.2.1 (R⁻¹ • y)).1
                have h1 := (hχ.2.2.2.1 (R⁻¹ • y)).2
                rw [abs_le]
                constructor
                · have : (1 : ℝ) ≤ B1 := le_max_left _ _
                  linarith
                · have : (1 : ℝ) ≤ B1 := le_max_left _ _
                  linarith
              · refine (ul0_iteratedFDeriv_one_sub_scaled χ hχ.1 R i hi0 y).trans ?_
                have hRi : |R⁻¹| ≤ 1 := by
                  rw [abs_inv, abs_of_pos hRpos]; exact inv_le_one_of_one_le₀ hR1
                have : |R⁻¹| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg _) hRi
                calc |R⁻¹| ^ i * ‖iteratedFDeriv ℝ i χ (R⁻¹ • y)‖ ≤ 1 * B0 := by
                      gcongr
                      exact (hB i _).trans (hBn i (hi'.trans hn))
                  _ ≤ B1 := by rw [one_mul]; exact le_max_right _ _
            have e2 : ‖iteratedFDeriv ℝ (n - i) (fun x => f x - c) y‖ ≤ η1 :=
              hR0.1 (n - i) (Finset.mem_range.2 (Nat.lt_succ_of_le ((Nat.sub_le _ _).trans hn))) y hyR
            exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg _)) e2 (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hB1pos.le)
        _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * B1 * η1 := by
            rw [Finset.sum_mul, Finset.sum_mul]
        _ ≤ 2 ^ k * B1 * η1 := by
            have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
              exact_mod_cast Nat.sum_range_choose n
            rw [this]
            have h2k : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2k hB1pos.le) hη1pos.le
  have hfin := hK w hws (2 ^ k * B1 * η1) (by positivity) hwb
  refine hfin.trans (ENNReal.ofReal_le_ofReal ?_)
  have : K * (2 ^ k * B1 * η1) = K / (K + 1) * ε := by
    rw [hη1]; field_simp
  rw [this]
  have : K / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  nlinarith [div_nonneg hK0 (by positivity : (0 : ℝ) ≤ K + 1)]


/-! ### Lower semicontinuity -/

/-- `L²` convergence implies a.e. convergence of a subsequence of the Fourier transforms, and Fatou -/
theorem ul0_sobE_lsc_aux (m : ℕ) (g : ℕ → Euc d → ℝ) (G : Euc d → ℝ) (M : ℝ≥0∞)
    (hgm : ∀ n, MemLp (g n) 2 volume) (hG : MemLp G 2 volume)
    (hconv : Tendsto (fun n => ∫ x, (g n x - G x) ^ 2) atTop (𝓝 0))
    (hM : ∀ n, sobolevNormE (m : ℝ) (g n) ≤ M) : sobolevNormE (m : ℝ) G ≤ M := by
  have hdiff : ∀ n, MemLp (fun x => g n x - G x) 2 volume := fun n => (hgm n).sub hG
  have hFn : ∀ n, MemLp (fun ξ => fourierL2 (g n) ξ - fourierL2 G ξ) 2 volume := fun n =>
    (memLp_fourierL2 (hgm n)).sub (memLp_fourierL2 hG)
  have hint : ∀ n, ∫ ξ, ‖fourierL2 (g n) ξ - fourierL2 G ξ‖ ^ 2 = ∫ x, (g n x - G x) ^ 2 := by
    intro n
    rw [← integral_norm_sq_fourierL2 (hdiff n)]
    refine integral_congr_ae ?_
    filter_upwards [fourierL2_sub (hgm n) hG] with ξ hξ
    rw [hξ]
  have hnorm : Tendsto (fun n => eLpNorm ((fun ξ => fourierL2 (g n) ξ) - fun ξ => fourierL2 G ξ) 2 volume)
      atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm ((fun ξ => fourierL2 (g n) ξ) - fun ξ => fourierL2 G ξ) 2 volume =
        ENNReal.ofReal ((∫ x, (g n x - G x) ^ 2) ^ (1 / 2 : ℝ)) := by
      intro n
      have := (hFn n).eLpNorm_eq_integral_rpow_norm (p := 2) (by norm_num) (by norm_num)
      refine (this.trans ?_)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      rw [hint n]
      norm_num
    simp_rw [e]
    have h1 : Tendsto (fun n => (∫ x, (g n x - G x) ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 ((0 : ℝ) ^ (1 / 2 : ℝ))) :=
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto.comp hconv
    have h3 : Tendsto (fun n => ENNReal.ofReal ((∫ x, (g n x - G x) ^ 2) ^ (1 / 2 : ℝ))) atTop
        (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ (1 / 2 : ℝ)))) := (ENNReal.continuous_ofReal.tendsto _).comp h1
    rw [Real.zero_rpow (by norm_num), ENNReal.ofReal_zero] at h3
    exact h3
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (μ := volume) (p := 2) (by norm_num)
    (by norm_num) (f := fun n ξ => fourierL2 (g n) ξ) (g := fun ξ => fourierL2 G ξ) hnorm
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hsq : ∀ u : Euc d → ℝ, MemLp u 2 volume → sobolevNormE (m : ℝ) u ^ 2 =
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 u ξ‖ ^ 2) := fun u hu => um_sobE_sq hu _
  have hmeasf : ∀ k, AEMeasurable (fun ξ : Euc d => ENNReal.ofReal
      (wt ξ ^ (m : ℝ) * ‖fourierL2 (g (ns k)) ξ‖ ^ 2)) volume := fun k =>
    (aesm_wt_mul (aestronglyMeasurable_fourierL2 (hgm (ns k))) _).aemeasurable.ennreal_ofReal
  have hfat := lintegral_liminf_le' (μ := volume) (u := atTop) hmeasf
  have hlimeq : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 G ξ‖ ^ 2) =
      liminf (fun k => ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 (g (ns k)) ξ‖ ^ 2)) atTop := by
    filter_upwards [hae] with ξ hξ
    have h1 : Tendsto (fun k => wt ξ ^ (m : ℝ) * ‖fourierL2 (g (ns k)) ξ‖ ^ 2) atTop
        (𝓝 (wt ξ ^ (m : ℝ) * ‖fourierL2 G ξ‖ ^ 2)) :=
      (hξ.norm.pow 2).const_mul _
    exact ((ENNReal.continuous_ofReal.tendsto _).comp h1).liminf_eq.symm
  have hM2 : ∀ k, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 (g (ns k)) ξ‖ ^ 2) ≤ M ^ 2 := by
    intro k
    rw [← hsq _ (hgm (ns k))]
    exact pow_le_pow_left' (hM _) 2
  have hlim_le : liminf (fun k => ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 (g (ns k)) ξ‖ ^ 2))
      atTop ≤ M ^ 2 :=
    Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hM2)
  have hG2 : sobolevNormE (m : ℝ) G ^ 2 ≤ M ^ 2 := by
    rw [hsq G hG, lintegral_congr_ae hlimeq]
    exact hfat.trans hlim_le
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hG2

/-- **UL-0 `ulocNormE_lsc`**: lower semicontinuity of `ulocNormE` under pointwise convergence of a uniformly
bounded sequence (the uniform bound `|u_n| ≤ B` is the documented adjustment of the sketch; it gives
`L²` convergence of `χ(·-z) u_n` by dominated convergence). -/
theorem ulocNormE_lsc (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (u : ℕ → Euc d → ℝ) (v : Euc d → ℝ)
    (B : ℝ) (hB : ∀ n x, |u n x| ≤ B) (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (M : ℝ≥0∞) (hM : ∀ n, ulocNormE m χ (u n) ≤ M) : ulocNormE m χ v ≤ M := by
  refine iSup_le fun z => ?_
  by_cases hMtop : M = ⊤
  · rw [hMtop]; exact le_top
  set g : ℕ → Euc d → ℝ := fun n x => χ (x - z) * u n x with hg
  set G : Euc d → ℝ := fun x => χ (x - z) * v x with hG
  have hgM : ∀ n, sobolevNormE (m : ℝ) (g n) ≤ M := fun n =>
    (le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * u n x) z).trans (hM n)
  have hmem : ∀ n, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (g n) := by
    intro n
    by_contra h
    have : sobolevNormE (m : ℝ) (g n) = ⊤ := by unfold sobolevNormE; rw [if_neg h]
    exact hMtop (top_le_iff.1 (this ▸ hgM n))
  have hgm : ∀ n, MemLp (g n) 2 volume := fun n => (hmem n).1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have hvB : ∀ x, |v x| ≤ B := fun x => le_of_tendsto (hlim x).abs (Filter.Eventually.of_forall fun n => hB n x)
  have hχc : Continuous (fun x : Euc d => χ (x - z)) := hχ.1.continuous.comp (continuous_id.sub continuous_const)
  have hχs : HasCompactSupport (fun x : Euc d => χ (x - z)) :=
    hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  have hcz : MemLp (fun x : Euc d => χ (x - z)) 2 volume := hχc.memLp_of_hasCompactSupport hχs
  have hGae : AEStronglyMeasurable G volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hgm n).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => (hlim x).const_mul (χ (x - z)))
  have hGm : MemLp G 2 volume := by
    refine MemLp.of_le (hcz.const_mul B) hGae (Filter.Eventually.of_forall fun x => ?_)
    simp only [G, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg hB0]
    nlinarith [abs_nonneg (χ (x - z)), hvB x]
  have hconv : Tendsto (fun n => ∫ x, (g n x - G x) ^ 2) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure (Euc d))) (F := fun n x => (g n x - G x) ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun x => (2 * B) ^ 2 * (χ (x - z)) ^ 2)
      (fun n => ((hgm n).aestronglyMeasurable.sub hGae).pow 2 |>.congr (Filter.Eventually.of_forall fun x => rfl))
      (hcz.integrable_sq.const_mul _)
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · simpa using this
    · simp only [g, G, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _), ← mul_sub, mul_pow]
      rw [mul_comm ((2 * B) ^ 2)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [← sq_abs (u n x - v x)]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |u n x - v x| ≤ |u n x| + |v x| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hB n x, hvB x]
    · have : Tendsto (fun n => g n x - G x) atTop (𝓝 (G x - G x)) :=
        ((hlim x).const_mul (χ (x - z))).sub_const (G x) |>.congr' (by simp [g, G]) |> fun h => by
          simpa [g, G] using h
      simpa using (this.pow 2)
  exact ul0_sobE_lsc_aux m g G M hgm hGm hconv hgM

end HRS.MS.Ul
