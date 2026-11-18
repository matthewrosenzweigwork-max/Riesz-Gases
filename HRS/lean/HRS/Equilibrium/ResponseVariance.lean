/-
# HRS.Equilibrium.ResponseVariance — the variance inputs of Lemma 4.19 (packet Q32-SPEC)

Specification file (statements only, `sorry`'d except where stated) for the inputs missing from
`HRS.response_subGaussian` (`Response.lean`, Lemma 4.19 `V:lem:finite-response-rates`, last
clause `V:eq:response-subGaussian`; source lines 5221-5276 of
`source/handoff/sources/HRS_periodic_main_20261008T010000Z.tex`).

The TeX proof of that clause (source lines 5252-5268) uses exactly two inputs beyond the
(proved) log-mgf identities of its first display:
* the compact-family linear variance estimate `V:eq:response-variance-input`
  (source lines 5100-5106, justified 5113-5131), used at `f = φ = cos(2πk·x)`;
* `C(θ) ≤ Var_{μ_θ}(φ) ≤ 1` (source line 5267, from `V:eq:response-susceptibility` and the
  contraction property after `V:eq:response-positive-inverse`, lines 5199-5201).
-/
import HRS.Equilibrium.Response
import HRS.Equilibrium.Q32aAux1
import HRS.Equilibrium.Q32bAux1
import HRS.Equilibrium.Q32cAux1
import HRS.Equilibrium.Q32cAux2

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

section ResponseVariance

/-- **Fixed-density linear variance bound** (`A:eq:variance-transfer`, second inequality, source
lines 3531-3533; also `P:eq:static-linear` 3990, `R:eq:linear-input` 4187,
`Q:eq:linear-input` 4485; "holds for every `L²(μ)` test, not just smooth tests", line 2756):
for a smooth positive probability density `ρ` (the standing "smooth positive background", source
lines 3388-3394, not tied to a potential), `β > 0`, there is `C` with
`N Var_{Q_{N,β}(μ)}[μ_N(f)] ≤ C ‖f‖²_{L²(μ)}` for all `N ≥ 2` and all `f ∈ L²(μ)`,
`μ = ρ dx`, `Q_{N,β}(μ) = modulatedGibbs (periodicRiesz d s) N β μ`.

This is the linear analogue of `quadStat_variance` (`QuadraticVariance.lean`, whose hypotheses
`2 ≤ d`, `0 ≤ s < d`, `0 < β`, `SmoothPosDensity ρ` it copies; the TeX of Appendix A is stated in
the range of Prop 4.3, not just `d/2 ≤ s < d`).  Representation decisions:
* the variance is the extended-real `evariance` (as in `quadStat_variance`), so there is no
  `variance`-of-non-`L²` junk (`variance` would be `0`); `μ_N(f) = N⁻¹ ∑ f(x_i)`;
* the right side is `ofReal (C * ∫ f² dμ)`; to keep the Bochner integral non-junk we assume
  `MemLp f 2 μ` (otherwise `∫ f² = 0` and the claim would be false); `Measurable f` makes
  `X ↦ f (X i)` measurable, so no `Measure.map`/`AEStronglyMeasurable` junk;
* constant `C` is chosen before `N` and `f` (it may depend on `d, s, β, ρ`).
Ambiguity: the TeX writes `‖f‖_{L²(μ)}` for the bound but does not say whether `f` is real
bounded measurable or `L²(μ)`; the `L²` reading is the stronger one and is the one the TeX
asserts (line 2756). -/
theorem linearStat_variance (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal ρ) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρ)) :=
  HRS.Q32b.q32b_main hd hs0 hsd β hβ ρ hρ

/-- **`V:eq:response-variance-input`** (source lines 5100-5106; compact-family uniformity
justified in lines 5113-5131): for every compact interval `I = [a, b]` there is `C_I` such that
`N Var_{N,θ}[μ_N(f)] ≤ C_I ‖f‖²_{L²(μ_θ)}` for `N ≥ 2`, `θ ∈ I`, where
`P_{N,θ} = rateGibbs d s k β θ N` is the canonical law of the rate family
`V_θ = -θ cos(2πk·x)/β` (`H:eq:rate-family`, source line 1021) and `μ_θ = ρ_θ dx` its thermal
equilibrium measure.

Setting copied from `response_subGaussian`/`thermal_response_rates` (`2 ≤ d`,
`d/2 ≤ s < d` the range of the subsection, source line 5083; `β > 0`; `k ≠ 0`;
`ρ θ` thermal density of `rateV k β θ` for every `θ`).  Representation decisions:
* quantifier order `∃ C, ∀ θ ∈ Icc a b, ∀ N ≥ 2, ∀ f` — the constant before `θ`, `N`, `f`
  (the family uniformity is the whole point; `C` may depend on `d, s, β, k, a, b`);
* `evariance`, `MemLp f 2 (withDensityReal (ρ θ))`, `Measurable f` and the form
  `μ_N(f) = N⁻¹ ∑ f(x_i)` exactly as in `linearStat_variance` (no junk: for fixed `N` the canonical
  density is bounded and `μ_θ ≍ dx` since `ρ θ` is bounded above and below, so `f ∈ L²(μ_θ)`
  makes `μ_N(f) ∈ L²(P_{N,θ})`, the mean in `evariance` is a genuine integral);
* `P_{N,θ} = Q_{N,β}(μ_θ)` (`canonicalGibbs_eq_modulatedGibbs`), so for each fixed `θ` this
  is `linearStat_variance` at `ρ = ρ θ`; the content here is the uniformity of the constant in
  `θ ∈ [a,b]` (TeX lines 5113-5127: common upper/lower density bounds from the thermal equation,
  Jensen and the lower bound of the periodic kernel, common smooth norms, a single heat cutoff and
  positive Fourier block; finitely many small `N` by `N Var ≤ N E[μ_N(f²)]`, line 5129).
Ambiguity: TeX says "for every compact parameter interval `I`" (an interval of `θ`), not `[a,b]`
specifically; `Set.Icc a b` with arbitrary `a b` (including `b < a`, trivially fine) covers it. -/
theorem response_variance_input (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (a b : ℝ) :
    ∃ C : ℝ, ∀ θ ∈ Set.Icc a b, ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f →
      MemLp f 2 (withDensityReal (ρ θ)) →
        (N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
            (rateGibbs d s k β θ N) ≤
          ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal (ρ θ))) := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  obtain ⟨Λ, hΛ1, hΛ⟩ := Q32c.q32c_family_upper hd hs0 hsd hβ k a b
  obtain ⟨C, hC⟩ := Q32c.q32c_main hd hs0 hsd β hβ Λ hΛ1
  refine ⟨C, fun θ hθ N hN f hf hf2 => ?_⟩
  have hΛθ := hΛ θ hθ (ρ θ) (hρ θ)
  rw [Q32c.q32c_rateGibbs_eq hd hs0 hsd k θ (hρ θ) hΛθ N]
  exact hC (ρ θ) (hρ θ).1 hΛθ N hN f hf hf2

/-- **The `φ = cos(2πk·x)` case of `V:eq:response-variance-input`, as used in the TeX proof of
Lemma 4.19** (source line 5249: "Choose `D_I ≥ 2` above the bound for `C_N` on the enlargement of
`I` by one in each direction, using `V:eq:response-variance-input`"): the finite-particle
variance `C_N(θ) = E[Y_{N,θ}²] = N Var_{N,θ}[μ_N(φ)]` (`rateVarN`, `V:eq:response-means`) is
bounded uniformly for `N ≥ 2`, `θ ∈ [a,b]`.

It follows from `response_variance_input` with `f = Torus.cosMode k`, since
`‖cos‖²_{L²(μ_θ)} = ∫ cos² dμ_θ ≤ 1` (`Torus.norm_cosMode_le`, `μ_θ` a probability measure),
and `rateVarN = N * variance(μ_N(cos))` (`rateMeanN` is the `P_{N,θ}`-mean of `μ_N(cos)` by
exchangeability, `resp_integral_sum_cos`/`resp_pair_firstMarginal` in `Response.lean`);
stated separately because it is the exact shape consumed by `response_subGaussian`.
No density `ρ` appears (the claim is about `rateGibbs` only); no junk: `Y_{N,θ}` is bounded by
`2√N`, so `rateVarN` is a genuine integral, and `rateGibbs` is a probability measure for `β > 0`.
Quantifier order `∃ C, ∀ N ≥ 2, ∀ θ ∈ Icc a b` — constant before `N` and `θ`. -/
theorem rateVarN_uniform_bound (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (a b : ℝ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc a b, rateVarN d s k β N θ ≤ C := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hd1 : 1 ≤ d := by omega
  have hex : ∀ θ : ℝ, ∃ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ := fun θ =>
    let ⟨ρ, h, _, _⟩ := PDE.MFThermalAssembly.thermal_exists_continuous hd1 s hs0 hsd
      (rateV k β θ) (Q32c.q32c_rateV_continuous k θ) β hβ
    ⟨ρ, h⟩
  choose ρ hρ using hex
  obtain ⟨C, hC⟩ := response_variance_input hd hs hsd β hβ k hk ρ hρ a b
  obtain ⟨Λ, hΛ1, hΛ⟩ := Q32c.q32c_family_upper hd hs0 hsd hβ k a b
  refine ⟨max C 0, fun N hN θ hθ => ?_⟩
  have hN0 : 0 < N := by omega
  have hΛθ := hΛ θ hθ (ρ θ) (hρ θ)
  have hP := Q32c.q32c_rateGibbs_eq hd hs0 hsd k θ (hρ θ) hΛθ N
  haveI : IsProbabilityMeasure (rateGibbs d s k β θ N) := by
    rw [hP]
    exact Q32c.q32c_Q_isProb hd hs0 hsd hβ hΛ1 (hρ θ).1 hΛθ hN0
  have hex' : IsExchangeable (rateGibbs d s k β θ N) := by
    rw [hP]
    exact modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)
  refine Q32c.q32c_rateVarN_le_of_evariance k β θ hN0 hex' (le_max_right _ _) ?_
  haveI := isProb_withDensityReal (hρ θ).1
  have hφL2 : MemLp (Torus.cosMode k) 2 (withDensityReal (ρ θ)) :=
    MemLp.of_bound (Torus.continuous_cosMode k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => Torus.norm_cosMode_le k x)
  have h := hC θ hθ N hN (Torus.cosMode k) (Torus.continuous_cosMode k).measurable hφL2
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hφ2 : Integrable (fun x => Torus.cosMode k x ^ 2) (withDensityReal (ρ θ)) :=
    hφL2.integrable_sq
  have hI0 : 0 ≤ ∫ x, Torus.cosMode k x ^ 2 ∂(withDensityReal (ρ θ)) :=
    integral_nonneg fun x => sq_nonneg _
  have hI1 : ∫ x, Torus.cosMode k x ^ 2 ∂(withDensityReal (ρ θ)) ≤ 1 := by
    have hbd : ∀ x, Torus.cosMode k x ^ 2 ≤ 1 := fun x => by
      have := Q32c.q32c_cosMode_abs_le k x
      nlinarith [abs_nonneg (Torus.cosMode k x), sq_abs (Torus.cosMode k x)]
    have := integral_mono hφ2 (integrable_const (1 : ℝ)) hbd
    simpa using this
  rcases le_total C 0 with hC0 | hC0
  · calc C * ∫ x, Torus.cosMode k x ^ 2 ∂(withDensityReal (ρ θ)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC0 hI0
      _ ≤ max C 0 := le_max_right _ _
  · calc C * ∫ x, Torus.cosMode k x ^ 2 ∂(withDensityReal (ρ θ)) ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hI1 hC0
      _ = C := mul_one C
      _ ≤ max C 0 := le_max_left _ _

/-- Auxiliary (proved from `ResponseAux.susc_bounds_general`, the upper half of
`susceptibilityCov_bounds` whose constant `C = 1` is hidden by its `∃ C`): for a bounded
probability density and `β ≥ 0`, `C_{β,μ}(φ,φ) ≤ ‖P_μ φ‖²_{L²(μ)}` (the contraction property
of the response inverse, TeX lines 5199-5201). -/
theorem susceptibilityCov_le_variance (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) (φ : Torus d → ℝ) (hφ : MemLp φ 2 (withDensityReal ρ)) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ≤
      l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
        (projMean (withDensityReal ρ) φ) := by
  have h0 : ∀ n : Lattice d, 0 ≤ rieszCoeff d s n := fun n => by
    by_cases hn : n = 0
    · simp [rieszCoeff, hn]
    · exact (rieszCoeff_pos hd hs0 hsd n hn).le
  have hgi := (integral_periodicRiesz hd hs0 hsd).1
  have hcoef := periodicRiesz_fourierCoeff hd hs0 hsd
  obtain ⟨c, hc, H⟩ := ResponseAux.susc_bounds_general hgi _ h0
    (ResponseAux.hcoef_of_funFourierCoeff hcoef) hρ hΛ hβ
  have hex := exists_unique_response_of_kernel hgi _ h0 hcoef ρ hρ Λ hΛ β hβ φ hφ
  have hex' : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ h :=
    let ⟨h, hh, _⟩ := hex; ⟨h, hh⟩
  have hr : IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ) := by
    have e : responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ = hex'.choose := by
      unfold responseInverse
      simp only [hex', dite_true]
    rw [e]
    exact hex'.choose_spec
  exact (H φ _ hφ hr).2

/-- **`C(θ) ≤ 1`** (TeX line 5267: "the limiting variance satisfies
`C(θ) ≤ Var_{μ_θ}(φ) ≤ 1`"): the limiting variance `C(θ) = C_{β,μ_θ}(φ,φ)` of the Gaussian
`G_θ` is at most `1`, for the thermal densities of the rate family and `φ = cos(2πk·x)`.

Hypotheses as in `response_subGaussian`; `hβ` and the range `d/2 ≤ s < d` are those of the
subsection (the proof only needs `0 ≤ s < d`, `β ≥ 0`).  Junk check: `susceptibilityCov` uses
`responseInverse`, which is `0` when no `IsResponse` solution exists; for a thermal density
(bounded above and below, probability) the solution exists and is a.e.-unique
(`exists_unique_response`), so the value is the genuine `⟨P φ, R P φ⟩_{L²(μ_θ)}`, and the bound
`≤ 1` is not a junk artifact (the form is `≥ 0` by `susceptibilityCov_bounds`).  Route:
`susceptibilityCov_le_variance` with `Λ` the common upper bound of `ρ θ`, then
`Var_μ(φ) = ∫φ² dμ - μ(φ)² ≤ ∫ φ² dμ ≤ 1`.  The bound `Λ` on a thermal density is the only
missing ingredient (`ρ θ x = exp(-β(V + g*ρ)) / Z`, `g ≥ -c`, Jensen lower bound of `Z`, TeX lines
3357-3363). -/
theorem susceptibilityCov_cosMode_le_one (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
      (Torus.cosMode k) (Torus.cosMode k) ≤ 1 := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hVc : Continuous (rateV k β θ) := by
    unfold rateV
    exact (continuous_const.mul (Torus.continuous_cosMode k)).div_const β
  have hVM : ∀ x, |rateV k β θ x| ≤ |θ| / β := by
    intro x
    have hc : |Torus.cosMode k x| ≤ 1 := by
      have := Torus.norm_cosMode_le k x
      rwa [Real.norm_eq_abs] at this
    unfold rateV
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hβ]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg θ) hc) hβ.le
  obtain ⟨Λ, hΛ⟩ := q32a_thermal_bounded_above hd hs0 hsd hVc hVM hβ.le (hρ θ)
  obtain ⟨hprob, _⟩ := hρ θ
  haveI : IsProbabilityMeasure (withDensityReal (ρ θ)) := isProb_withDensityReal hprob
  have hφL2 : MemLp (Torus.cosMode k) 2 (withDensityReal (ρ θ)) :=
    MemLp.of_bound (Torus.continuous_cosMode k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => Torus.norm_cosMode_le k x)
  have hle := susceptibilityCov_le_variance hd hs0 hsd (ρ θ) hprob Λ hΛ β hβ.le
    (Torus.cosMode k) hφL2
  refine hle.trans ?_
  have hφi : Integrable (Torus.cosMode k) (withDensityReal (ρ θ)) := hφL2.integrable (by norm_num)
  have hφ2 : Integrable (fun x => Torus.cosMode k x ^ 2) (withDensityReal (ρ θ)) :=
    hφL2.integrable_sq
  have hbd : ∀ x, Torus.cosMode k x ^ 2 ≤ 1 := fun x => by
    have h := Torus.norm_cosMode_le k x
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (Torus.cosMode k x), sq_abs (Torus.cosMode k x)]
  have h1 : ∫ x, Torus.cosMode k x ^ 2 ∂(withDensityReal (ρ θ)) ≤ 1 := by
    have := integral_mono hφ2 (integrable_const (1 : ℝ)) hbd
    simpa using this
  have hexp : ∫ x, (projMean (withDensityReal (ρ θ)) (Torus.cosMode k) x) *
      (projMean (withDensityReal (ρ θ)) (Torus.cosMode k) x) ∂(withDensityReal (ρ θ))
      = ∫ x, Torus.cosMode k x ^ 2 ∂(withDensityReal (ρ θ))
        - (pair (withDensityReal (ρ θ)) (Torus.cosMode k)) ^ 2 := by
    unfold projMean
    have e : ∀ x, (Torus.cosMode k x - pair (withDensityReal (ρ θ)) (Torus.cosMode k)) *
        (Torus.cosMode k x - pair (withDensityReal (ρ θ)) (Torus.cosMode k))
        = Torus.cosMode k x ^ 2 - 2 * pair (withDensityReal (ρ θ)) (Torus.cosMode k) * Torus.cosMode k x
          + pair (withDensityReal (ρ θ)) (Torus.cosMode k) ^ 2 := fun x => by ring
    simp only [e]
    have i1 : Integrable (fun x => Torus.cosMode k x ^ 2
        - 2 * pair (withDensityReal (ρ θ)) (Torus.cosMode k) * Torus.cosMode k x)
        (withDensityReal (ρ θ)) := hφ2.sub (hφi.const_mul _)
    rw [integral_add i1 (integrable_const _),
      integral_sub hφ2 (hφi.const_mul _), integral_const_mul, integral_const]
    have hp : ∫ x, Torus.cosMode k x ∂(withDensityReal (ρ θ))
        = pair (withDensityReal (ρ θ)) (Torus.cosMode k) := rfl
    rw [hp]
    simp
    ring
  unfold l2Inner
  rw [hexp]
  nlinarith [sq_nonneg (pair (withDensityReal (ρ θ)) (Torus.cosMode k))]

/-
Proof sketch of `response_subGaussian` from the statements above (TeX lines 5248-5268).
Fix `a b` and let `C` be the constant of `rateVarN_uniform_bound` for `[a - 1, b + 1]`; put
`D = max 2 C`.  Fix `N ≥ 2`, `θ ∈ [a,b]`.  By `finite_response_rates` (proved first display) the
function `L_N(θ) := log (respA k gm β N 0 θ)` (the log-normaliser of the exponential tilt
`resp_rateGibbs_eq`, `resp_respA_contDiff`, `resp_respA_hasDerivAt`) is smooth with
`L_N' = N * rateMeanN`, `L_N'' = N * rateVarN` (`hMderiv`: `(rateMeanN)' = rateVarN`), so the log-mgf
`Ψ(t) = L_N(θ + t/√N) - L_N(θ) - t √N rateMeanN θ` of `Y = rateY d s k β N θ` has
`Ψ(0) = Ψ'(0) = 0` and `Ψ''(t) = rateVarN d s k β N (θ + t/√N) ≤ D` for `|t| ≤ √N`, because
`θ + t/√N ∈ [a-1, b+1]` (`rateVarN_uniform_bound`).  Hence (Taylor with Lagrange remainder, e.g.
`taylor_mean_remainder_lagrange`) `Ψ(t) ≤ D t²/2` for `|t| ≤ √N`; the mgf identity
`E exp(t Y) = exp(Ψ(t))` is `resp_rateGibbs_eq` + `resp_integral_sum_cos`-type change of density
(`mgf`, `ProbabilityTheory.mgf`).  Exponential Markov (`ProbabilityTheory.measure_ge_le_exp_mul_mgf`)
with `t = ± x / D ≤ √N` for `0 ≤ x ≤ 2√N` gives `P(Y > x) ≤ exp(-x²/(2D))` and the same for `-Y`,
so `P(|Y| > x) ≤ 2 exp(-x²/(2D))` (`measure_union_le`); for `x ≥ 2√N` the event `{|Y| > x}` is
empty since `|Y| ≤ 2√N` (`Torus.norm_cosMode_le`, `rateMeanN` bounded by `1`).  For the Gaussian
term, `susceptibilityCov_cosMode_le_one` gives variance `v := C(θ).toNNReal ≤ 1 ≤ D`, and
`gaussianReal 0 v {z | x < |z|} ≤ 2 exp(-x²/(2v)) ≤ 2 exp(-x²/(2D))` (Gaussian tail bound:
`gaussianReal` mgf `mgf_id_gaussianReal`, again exponential Markov; `v = 0` is the Dirac mass at `0`,
tail `0`).  Adding the two bounds gives `4 exp(-x²/(2D))`, `ENNReal.ofReal` conversion by
`ENNReal.ofReal_add`.
-/

end ResponseVariance

end HRS

end
