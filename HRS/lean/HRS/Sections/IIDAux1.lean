import HRS.Dynamics.InitialData
import HRS.Prob.Metrics
import HRS.Prob.EdgeworthAux

/-!
# IID helper chain for Proposition 5.9 (`iid_field_comparison`, `iid_field_mixture`)

CHAIN PLAN (sizes = estimated Lean lines; files in dependency order; namespace `HRS.IID`).

Route (TeX M L6804-6920): Gaussian-smoothing Lindeberg on the modes of a finite box `T_L`, tails by
`E‖(I-P_T)S‖`, `W_2` from `W_1` and fourth moments, mixture by conditioning on the sign.

* `IIDAux1` (~450) Gaussian shift calculus on `𝔼 = ℝ^p` for the standard Gaussian `u`
  (density `κ(z) = (2π)^{-p/2} e^{-|z|²/2}` = `gaussKernel p (1/2)`):
  - Cameron–Martin `E q(u+a) = E[q(u) R_a(u)]`, `R_a = exp(a·u - |a|²/2)`; `E R_a = 1`, `E R_a² = e^{|a|²}`;
  - `|E w(u+a) - E w(u)| ≤ min(2, √(e^{|a|²}-1)) ‖w‖_∞` and the linear form `≤ 2|a| ‖w‖_∞`;
  - Gaussian moments of `c·u`: `E|(c·u)²-|c|²| ≤ √2 |c|²`, `E|u|⁴ ≤ 3p²`.
* `IIDAux2` (~700) smoothing along a line: for `q` of linear growth, `Q(s) = E q(u+sc)` is `C²` with
  `Q'(0) = E[q(u)(c·u)]`, `Q''(s) = E[q(u+sc)((c·u)²-|c|²)]`; Taylor remainder lemma
  (`|Q''(s)-Q''(0)| ≤ K s ⇒ |Q(1)-Q(0)-Q'(0)-Q''(0)/2| ≤ K/6`);
  the two bounds on `K`: `√2 L_c |c|²` for `q` Lipschitz along `c`, and `2‖q''_c‖_∞ |c|` for `q ∈ C²`.
* `IIDAux3` (~800) Lindeberg with Gaussian smoothing on measures: `convPow`, the telescoping
  `a_i = ∫ f d(μ^{*i} ∗ ν^{*(N-i)})`, one step (covariance matching, `A⁻¹`-weights, `E|A⁻¹y|² = p`),
  harmonic sum `∑ 1/(N-i) ≤ log(eN)`, `∑ (N-i)^{-1/2} ≤ 2√N`.  Output `FD-W1` (Lipschitz tests,
  `W_1 ≤ C (B+√trΣ)(1+p log(eN))/√N`) and `FD-d2` (`C_b²` tests, `≤ C (B²+trΣ)(1+√p)/√N`).
* `IIDAux4` (~500) lattice box `T_L = {‖k‖_∞ ≤ L}`: `|T_L| ≤ (3L)^d`, tail `∑_{k∉T_L} jp^{-2m} ≤ C L^{d-2m}`
  (shell counting by sup norm + p-series), isometric embedding `ι_T : ℝ^T → E_m`, `C_b^k` stability under
  composition with `ι_T`, positive definiteness of the mode covariance from `ρ ≥ c` (Parseval for trig polynomials).
* `IIDAux5` (~700) finite-mode theorem `FM` (generic centre `μ`, Gaussian `γ` with covariance `iidCov ρ`):
  `d_2(S,γ) ≤ ε₂ + 2 τ_T`, and a coupling of `Measure.pi μ` with `γ` with `E‖S-F‖ ≤ ε₁+η+2τ_T`
  (glue as in `block_coupling`), both reduced to finite-dimensional bounds on the `T`-coordinates.
* `IIDAux6` (~500) moments: `E‖S‖⁴ ≤ C`, `E‖F‖⁴ ≤ C`, `W_2² ≤ W_1^{2/3}(8M)^{1/3}` along a coupling;
  choice `L = ⌈(√N/log eN)^{1/(m+d/2)}⌉`, `L' = ⌈N^{1/(2m)}⌉`, rate arithmetic for `iidRateSmooth`, `iidRateW`.
* `IIDAux7` (~900) mixture: finite-dimensional white-noise coupling `E|G_q^T-G_ρ^T|² ≤ C‖q-ρ‖²_∞`
  (Gram-matrix Gaussian vector), coordinate decomposition `η = (N^{-1/2}∑(δ-q)) ± abρ`,
  convexity of `smoothDist`/`W_p` under mixtures, translation invariance.
* `IIDFinal` (~200) `iid_field_comparison_proof`, `iid_field_mixture_proof` with verbatim statements
  and `example := (@..._proof : type_of% @HRS.iid_field_comparison)` checks.

Total estimate ~5500 lines.  Abandoned alternatives: Stein/third-derivative formulas for `P_t f`
(replaced by Cameron–Martin differences), quantitative `Σ ≥ cD` (only positive definiteness is needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

/-- The standard Gaussian on `ℝ^p`. -/
abbrev gam (p : ℕ) : Measure (EuclideanSpace ℝ (Fin p)) := stdGaussian (EuclideanSpace ℝ (Fin p))

section Shift

variable {p : ℕ}

/-- `R_a(z) = exp(⟨a,z⟩ - |a|²/2)`: density of `N(a,I)` w.r.t. `N(0,I)`. -/
def Rsh (a z : EuclideanSpace ℝ (Fin p)) : ℝ := Real.exp (inner ℝ a z - ‖a‖ ^ 2 / 2)

lemma Rsh_pos (a z : EuclideanSpace ℝ (Fin p)) : 0 < Rsh a z := Real.exp_pos _

lemma measurable_Rsh (a : EuclideanSpace ℝ (Fin p)) : Measurable (Rsh a) := by
  unfold Rsh; fun_prop

lemma gam_eq_withDensity : gam p = volume.withDensity
    (fun z => ENNReal.ofReal (gaussKernel p (1 / 2) z)) := by
  have h := mvGaussian_eq_withDensity (p := p) (ε := 1) one_pos
  simp only [one_pow, one_smul, mul_one] at h
  show stdGaussian (EuclideanSpace ℝ (Fin p)) = _
  rw [← multivariateGaussian_zero_one]
  exact h

lemma integral_gam (f : EuclideanSpace ℝ (Fin p) → ℝ) :
    ∫ z, f z ∂(gam p) = ∫ z, gaussKernel p (1 / 2) z * f z := by
  have h := integral_kernel_eq_mvG (p := p) (ε := 1) one_pos f
  simp only [one_pow, one_smul, mul_one] at h
  show ∫ z, f z ∂(stdGaussian (EuclideanSpace ℝ (Fin p))) = _
  rw [← multivariateGaussian_zero_one]
  exact h.symm

lemma kappa_sub (a z : EuclideanSpace ℝ (Fin p)) :
    gaussKernel p (1 / 2) (z - a) = gaussKernel p (1 / 2) z * Rsh a z := by
  unfold gaussKernel Rsh
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  rw [norm_sub_sq_real, real_inner_comm]
  ring

/-- Cameron–Martin: `E q(u + a) = E[q(u) R_a(u)]`. -/
lemma integral_gam_shift (q : EuclideanSpace ℝ (Fin p) → ℝ) (a : EuclideanSpace ℝ (Fin p)) :
    ∫ z, q (z + a) ∂(gam p) = ∫ z, q z * Rsh a z ∂(gam p) := by
  rw [integral_gam, integral_gam]
  rw [← integral_sub_right_eq_self (fun z => gaussKernel p (1 / 2) z * q (z + a)) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [sub_add_cancel, kappa_sub]
  ring

lemma integral_Rsh (a : EuclideanSpace ℝ (Fin p)) : ∫ z, Rsh a z ∂(gam p) = 1 := by
  have := integral_gam_shift (fun _ => (1 : ℝ)) a
  simp only [integral_const, probReal_univ, one_smul, one_mul] at this
  exact this.symm

lemma integrable_Rsh (a : EuclideanSpace ℝ (Fin p)) : Integrable (Rsh a) (gam p) :=
  Integrable.of_integral_ne_zero (by rw [integral_Rsh]; norm_num)

lemma Rsh_sq (a z : EuclideanSpace ℝ (Fin p)) :
    Rsh a z ^ 2 = Real.exp (‖a‖ ^ 2) * Rsh ((2 : ℝ) • a) z := by
  unfold Rsh
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  rw [inner_smul_left, norm_smul]
  simp only [conj_trivial, Nat.cast_ofNat, Real.norm_ofNat]
  ring

lemma integrable_Rsh_sq (a : EuclideanSpace ℝ (Fin p)) : Integrable (fun z => Rsh a z ^ 2) (gam p) := by
  simp_rw [Rsh_sq]
  exact (integrable_Rsh _).const_mul _

lemma integral_Rsh_sq (a : EuclideanSpace ℝ (Fin p)) :
    ∫ z, Rsh a z ^ 2 ∂(gam p) = Real.exp (‖a‖ ^ 2) := by
  simp_rw [Rsh_sq]
  rw [integral_const_mul, integral_Rsh, mul_one]

lemma sq_integral_abs_Rsh_sub (a : EuclideanSpace ℝ (Fin p)) :
    ∫ z, (Rsh a z - 1) ^ 2 ∂(gam p) = Real.exp (‖a‖ ^ 2) - 1 := by
  have hi1 := integrable_Rsh a
  have hi2 := integrable_Rsh_sq a
  have e : ∀ z, (Rsh a z - 1) ^ 2 = Rsh a z ^ 2 - 2 * Rsh a z + 1 := fun z => by ring
  simp_rw [e]
  have h3 : Integrable (fun z => Rsh a z ^ 2 - 2 * Rsh a z) (gam p) := hi2.sub (hi1.const_mul 2)
  rw [integral_add h3 (integrable_const _), integral_sub hi2 (hi1.const_mul 2),
    integral_const_mul, integral_Rsh_sq, integral_Rsh]
  simp
  ring

lemma integral_abs_Rsh_sub_le (a : EuclideanSpace ℝ (Fin p)) :
    ∫ z, |Rsh a z - 1| ∂(gam p) ≤ Real.sqrt (Real.exp (‖a‖ ^ 2) - 1) := by
  have hi1 := integrable_Rsh a
  have hi2 := integrable_Rsh_sq a
  have hsq : Integrable (fun z => (Rsh a z - 1) ^ 2) (gam p) := by
    have e : ∀ z, (Rsh a z - 1) ^ 2 = Rsh a z ^ 2 - 2 * Rsh a z + 1 := fun z => by ring
    simp_rw [e]
    exact (hi2.sub (hi1.const_mul 2)).add (integrable_const _)
  have hm : AEStronglyMeasurable (fun z => |Rsh a z - 1|) (gam p) :=
    ((measurable_Rsh a).sub measurable_const).abs.aestronglyMeasurable
  have hmem : MemLp (fun z => |Rsh a z - 1|) 2 (gam p) := by
    refine (memLp_two_iff_integrable_sq hm).2 ?_
    simpa [sq_abs] using hsq
  have := sq_integral_le (gam p) hmem
  simp_rw [sq_abs] at this
  rw [sq_integral_abs_Rsh_sub] at this
  exact Real.le_sqrt_of_sq_le this

lemma abs_integral_shift_sub_le {w : EuclideanSpace ℝ (Fin p) → ℝ} (hw : Measurable w) {W : ℝ}
    (hW : ∀ z, |w z| ≤ W) (a : EuclideanSpace ℝ (Fin p)) :
    |∫ z, w (z + a) ∂(gam p) - ∫ z, w z ∂(gam p)| ≤ W * Real.sqrt (Real.exp (‖a‖ ^ 2) - 1) := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  have hwi : Integrable w (gam p) :=
    Integrable.of_bound hw.aestronglyMeasurable W (Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hW z)
  have hwR : Integrable (fun z => w z * Rsh a z) (gam p) := by
    refine ((integrable_Rsh a).const_mul W).mono' (hw.mul (measurable_Rsh a)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Rsh_pos a z)]
    exact mul_le_mul_of_nonneg_right (hW z) (Rsh_pos a z).le
  rw [integral_gam_shift, ← integral_sub hwR hwi]
  have e : ∀ z, w z * Rsh a z - w z = w z * (Rsh a z - 1) := fun z => by ring
  simp_rw [e]
  have hint : Integrable (fun z => |Rsh a z - 1|) (gam p) := ((integrable_Rsh a).sub (integrable_const _)).abs
  calc |∫ z, w z * (Rsh a z - 1) ∂(gam p)| ≤ ∫ z, |w z * (Rsh a z - 1)| ∂(gam p) := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := gam p) (fun z => w z * (Rsh a z - 1))
    _ ≤ ∫ z, W * |Rsh a z - 1| ∂(gam p) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (hint.const_mul W) (Filter.Eventually.of_forall fun z => ?_)
        show |w z * (Rsh a z - 1)| ≤ W * |Rsh a z - 1|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hW z) (abs_nonneg _)
    _ = W * ∫ z, |Rsh a z - 1| ∂(gam p) := integral_const_mul _ _
    _ ≤ W * Real.sqrt (Real.exp (‖a‖ ^ 2) - 1) := mul_le_mul_of_nonneg_left (integral_abs_Rsh_sub_le a) hW0

lemma abs_integral_shift_sub_le_two {w : EuclideanSpace ℝ (Fin p) → ℝ} (hw : Measurable w) {W : ℝ}
    (hW : ∀ z, |w z| ≤ W) (a : EuclideanSpace ℝ (Fin p)) :
    |∫ z, w (z + a) ∂(gam p) - ∫ z, w z ∂(gam p)| ≤ 2 * W := by
  have hb : ∀ f : EuclideanSpace ℝ (Fin p) → ℝ, (∀ z, |f z| ≤ W) → |∫ z, f z ∂(gam p)| ≤ W := fun f hf => by
    have := norm_integral_le_of_norm_le_const (μ := gam p) (f := f) (C := W)
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hf z)
    simpa using this
  have h1 := hb (fun z => w (z + a)) (fun z => hW _)
  have h2 := hb w hW
  calc _ ≤ |∫ z, w (z + a) ∂(gam p)| + |∫ z, w z ∂(gam p)| := abs_sub _ _
    _ ≤ W + W := add_le_add h1 h2
    _ = 2 * W := by ring

/-- Linear modulus of continuity of Gaussian shifts on bounded functions. -/
lemma abs_integral_shift_sub_le_lin {w : EuclideanSpace ℝ (Fin p) → ℝ} (hw : Measurable w) {W : ℝ}
    (hW : ∀ z, |w z| ≤ W) (a : EuclideanSpace ℝ (Fin p)) :
    |∫ z, w (z + a) ∂(gam p) - ∫ z, w z ∂(gam p)| ≤ 2 * W * ‖a‖ := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  by_cases ha : ‖a‖ ≤ 1
  · refine (abs_integral_shift_sub_le hw hW a).trans ?_
    have hx : |‖a‖ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [norm_nonneg a]
    have hb := Real.exp_bound hx (n := 1) one_pos
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_one, Nat.factorial_one, Nat.succ_eq_add_one, zero_add, mul_one] at hb
    have hb2 : Real.exp (‖a‖ ^ 2) - 1 ≤ 2 * ‖a‖ ^ 2 := by
      have := (abs_le.1 hb).2
      norm_num at this
      linarith
    have hs : Real.sqrt (Real.exp (‖a‖ ^ 2) - 1) ≤ 2 * ‖a‖ := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith [norm_nonneg a]
    calc W * Real.sqrt (Real.exp (‖a‖ ^ 2) - 1) ≤ W * (2 * ‖a‖) := mul_le_mul_of_nonneg_left hs hW0
      _ = 2 * W * ‖a‖ := by ring
  · push_neg at ha
    refine (abs_integral_shift_sub_le_two hw hW a).trans ?_
    nlinarith

end Shift

section Moments

variable {p : ℕ}

lemma isCenteredGaussian_gam : IsCenteredGaussian (gam p) :=
  ⟨inferInstance, fun L => integral_strongDual_stdGaussian L⟩

lemma integral_inner_sq (c : EuclideanSpace ℝ (Fin p)) :
    ∫ z, (inner ℝ c z) ^ 2 ∂(gam p) = ‖c‖ ^ 2 := by
  have h := variance_dual_stdGaussian (E := EuclideanSpace ℝ (Fin p)) (innerSL ℝ c)
  rw [innerSL_apply_norm, variance_of_integral_eq_zero] at h
  · simpa using h
  · exact (innerSL ℝ c).continuous.aemeasurable
  · exact integral_strongDual_stdGaussian (innerSL ℝ c)

lemma integrable_inner_pow (c : EuclideanSpace ℝ (Fin p)) (j : ℕ) :
    Integrable (fun z => (inner ℝ c z) ^ (2 * j)) (gam p) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have h := IsGaussian.memLp_dual (gam p) (innerSL ℝ c) ((2 * j : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top _)
  have := h.integrable_norm_pow (by simpa using hj.ne')
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [innerSL_apply_apply, Real.norm_eq_abs]
  exact (Even.pow_abs ⟨j, by ring⟩ _)

lemma integral_inner_pow4_le (c : EuclideanSpace ℝ (Fin p)) :
    ∫ z, (inner ℝ c z) ^ 4 ∂(gam p) ≤ 3 * ‖c‖ ^ 4 := by
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin p)) := innerSL ℝ c with hL
  have : IsProbabilityMeasure ((gam p).map L) := inferInstance
  have hcg : IsCenteredGaussian ((gam p).map L) := by
    refine ⟨inferInstance, fun L' => ?_⟩
    rw [integral_map L.continuous.aemeasurable L'.continuous.aestronglyMeasurable]
    exact integral_strongDual_stdGaussian (L'.comp L)
  have h := HRS.EdgeAux.gaussian_fourth_le hcg
  rw [integral_map L.continuous.aemeasurable (by fun_prop), integral_map L.continuous.aemeasurable (by fun_prop)] at h
  have e4 : ∀ z, ‖L z‖ ^ 4 = (inner ℝ c z) ^ 4 := fun z => by
    simp only [hL, innerSL_apply_apply, Real.norm_eq_abs]
    exact (Even.pow_abs ⟨2, by ring⟩ _)
  have e2 : ∀ z, ‖L z‖ ^ 2 = (inner ℝ c z) ^ 2 := fun z => by
    simp only [hL, innerSL_apply_apply, Real.norm_eq_abs]
    exact sq_abs _
  simp_rw [e4, e2, integral_inner_sq] at h
  nlinarith [h]

lemma integral_abs_inner_sq_sub_le (c : EuclideanSpace ℝ (Fin p)) :
    ∫ z, |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2| ∂(gam p) ≤ Real.sqrt 2 * ‖c‖ ^ 2 := by
  have h2 : Integrable (fun z => (inner ℝ c z) ^ 2) (gam p) := by
    simpa using integrable_inner_pow c 1
  have h4 : Integrable (fun z => (inner ℝ c z) ^ 4) (gam p) := by
    simpa using integrable_inner_pow c 2
  have hf : Integrable (fun z => ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ^ 2) (gam p) := by
    have e : ∀ z, ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ^ 2 =
        (inner ℝ c z) ^ 4 - 2 * ‖c‖ ^ 2 * (inner ℝ c z) ^ 2 + ‖c‖ ^ 4 := fun z => by ring
    simp_rw [e]
    exact (h4.sub (h2.const_mul _)).add (integrable_const _)
  have hm : AEStronglyMeasurable (fun z => |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2|) (gam p) := by
    have : Continuous fun z : EuclideanSpace ℝ (Fin p) => |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2| := by fun_prop
    exact this.aestronglyMeasurable
  have hmem : MemLp (fun z => |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2|) 2 (gam p) := by
    refine (memLp_two_iff_integrable_sq hm).2 ?_
    simpa [sq_abs] using hf
  have hs := sq_integral_le (gam p) hmem
  simp_rw [sq_abs] at hs
  have e : ∫ z, ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ^ 2 ∂(gam p) =
      ∫ z, (inner ℝ c z) ^ 4 ∂(gam p) - ‖c‖ ^ 4 := by
    have e1 : ∀ z, ((inner ℝ c z) ^ 2 - ‖c‖ ^ 2) ^ 2 =
        (inner ℝ c z) ^ 4 - 2 * ‖c‖ ^ 2 * (inner ℝ c z) ^ 2 + ‖c‖ ^ 4 := fun z => by ring
    simp_rw [e1]
    have h3 : Integrable (fun z => (inner ℝ c z) ^ 4 - 2 * ‖c‖ ^ 2 * (inner ℝ c z) ^ 2) (gam p) :=
      h4.sub (h2.const_mul _)
    rw [integral_add h3 (integrable_const _), integral_sub h4 (h2.const_mul _), integral_const_mul,
      integral_inner_sq]
    simp
    ring
  rw [e] at hs
  have h4le := integral_inner_pow4_le c
  have : (∫ z, |(inner ℝ c z) ^ 2 - ‖c‖ ^ 2| ∂(gam p)) ^ 2 ≤ (Real.sqrt 2 * ‖c‖ ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [h4le, hs]
  exact le_of_sq_le_sq this (by positivity)

lemma integral_norm_sq_gam : ∫ z, ‖z‖ ^ 2 ∂(gam p) = p := by
  have h := integral_norm_sq_mvGaussian (p := p) (Δ := (1 : Matrix (Fin p) (Fin p) ℝ)) Matrix.PosSemidef.one
  rw [multivariateGaussian_zero_one] at h
  simpa using h

lemma integral_norm_pow4_gam_le : ∫ z, ‖z‖ ^ 4 ∂(gam p) ≤ 3 * (p : ℝ) ^ 2 := by
  have h := HRS.EdgeAux.gaussian_fourth_le (isCenteredGaussian_gam (p := p))
  rw [integral_norm_sq_gam] at h
  exact h

end Moments

end HRS.IID
