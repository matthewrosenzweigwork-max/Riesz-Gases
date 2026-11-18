import HRS.MS.QsfTie
import HRS.MS.CanThm
import HRS.MS.Canon

/-!
# S4.6 (`quadratic_preparation_static`, `quadratic_preparation_static_osc`), packet A1

Worker S46.  Namespace `S46`, helper prefix `s46_`.  Frozen rows: `HRS/Whole/Thermal.lean` (`quadratic_preparation_static`
:383, `quadratic_preparation_static_osc` :396); TeX: supplement L2649-2699 (corollary and proof).  Plan: `S46_PLAN.md`
(scratch directory), repeated here.

## Verdict on the statements

Both are true and non-vacuous as stated; no statement change is needed.  If one of the three intervals is empty
(`ap < am`, `βp < βm` or `γp < γm`) the quantifier `∀ a ∈ Icc …` is vacuous; otherwise `a ≥ am > 0`, `β ≥ βm > 0`,
`γ₀ ≥ γm > 0`.  Junk-value audit: as in S4.5 (`QsfAux1`).  The Gibbs law is `modulatedGibbs g N γ₀ μ_{a,β}`, a
probability measure by `GibbsWellDefined` (S3.3/S3.5 at inverse temperature `γ₀ ∈ [γm,γp]`); `Kop` is a genuine integral
`μ`-a.e.; `responseInverse` is the honest resolvent `(I + γ₀ K)⁻¹ P_μ` because the corrector exists
(`thermal_corrector_proof`, three temperatures); `featureVec` is honest by conjunct 1 of `StaticFieldConclusion`
(`s45_feature_memℓp`), `law` is honest by conjunct 2 (`s45_feature_measurable`); `smoothDist` is only used through
`Real.iSup_le` with a nonnegative bound; `Real.log 0` and `0 ^ (-s)` at coinciding particles are never evaluated (null set);
`d ≥ 2`, `N ≥ 2` make `firstMarginal` a probability measure.  The constant is quantified before `a, β, γ₀, φ, N, γ`, and
every ingredient is an explicit function of the constants of `tc6_unif`, `thermal_corrector_proof`, `euc_static_proof`,
`r2_log_static_proof` (for `s = 0` a uniform `HasSphericalBound` follows from the uniform Gaussian bound).

## Route (S4.6 from S4.5)

1. **Exact identification.**  With `V_Q = (β/γ₀) V + (β/γ₀ - 1) g*μ` the density `ρ` of `μ = μ_{a,β}` solves the thermal
   equation for `(g, V_Q, γ₀)`, so `canonicalGibbs_eq_modulatedGibbs_proof` gives
   `modulatedGibbs g N γ₀ μ = canonicalGibbs g V_Q N γ₀` (`s46_P_eq`).  The weight is `e^{-γ₀ H_{a'}} e^{-(β-γ₀) ∑ U(x_i)}`,
   `a' = βa/γ₀`, `U = g*μ` (smooth, bounded gradient).
2. **Gibbs IBP** (`QprepAux3`-`QprepAux6`) by tilting the S4.5 identity `s45_gibbs_ibp` (confinement `a' = βa/γ₀`, temperature `γ₀`) with
   the compactly supported tests `F e^{-c ∑ U(x_i)} θ(S/R²)` (`c = β-γ₀`, `S = ∑|x_i|²`) and letting `R → ∞` (the test equals `F e^{-c∑U}`
   near each `X` once `R² > S(X)`; domination by `s46_J_bound`, using the true-kernel weighted pair bound `s46_pair_w0` obtained from
   the `ε`-uniform bound of S4.5 by continuity in `ε`, and `|U(x)| ≤ |U(0)| + B_U|x|`).
3. **Corrector identity / covariance / Stein identity** (`QprepAux7`, `QprepAux8`): copies of `s45_star`, `s45_cov_identity`,
   `s45_stein_id` with Dirichlet coefficient `γ₀⁻¹` and drift `β a x + (β-γ₀) ∇U`.
4. **Static bundle** (`QprepAux2`), **`R` and `T` bounds** (`QprepAux9`), uniform in `(a, β, γ₀)`: the constants are quantified before
   the parameters (`K_R = √C_s (C_W (s+1) C_s + 1)`, `K_T = √C_s + C_s`; `C_W` depends on `d, s` and the density bound only).
5. **Assembly** (`QprepAux10`-`QprepAux13`): copy of `QsfAsm3`-`QsfAsm11` (vector Stein identity, `hfin` data, `static_stein_hilbert`,
   tails, `smoothDist`) with constant `K_R C_c + γm⁻¹ K_T C_c`; the oscillator clause (`QprepAux14`) is the feature form for the
   Hermite family (its `C_b^J` norm sum `S` does not depend on `(a, β, γ₀)`); ties in `QprepTie`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace S46

open HRS.Whole HRS.MS.Thm HRS.MS.Can2
open HRS (Euc)

variable {d : ℕ}

/-! ### The auxiliary potential and the identification `Q = canonicalGibbs g V_Q N γ₀` -/

/-- `V_γ = (β/γ) V + (β/γ - 1) g * μ` (S lines 2672-2673), `V = a|x|²/2`, `μ = μ_{a,β}`. -/
def s46_VQ (d : ℕ) (s a β γ : ℝ) : Euc d → ℝ := fun x =>
  (β / γ) * confinement a x +
    (β / γ - 1) * convMeasure (rieszKernel d s) (thermalMeasure d s a β) x

/-- The preparation law, in canonical form. -/
abbrev s46_P (d : ℕ) (s a β γ : ℝ) (N : ℕ) : Measure (EucConfig d N) :=
  canonicalGibbs (rieszKernel d s) (s46_VQ d s a β γ) N γ

/-- Its one-particle marginal. -/
abbrev s46_nu (d : ℕ) (s a β γ : ℝ) (N : ℕ) : Measure (Euc d) := firstMarginal (s46_P d s a β γ N)

theorem s46_isThermalDensity_VQ {s a β γ : ℝ} (hγ : 0 < γ)
    (h : IsThermalDensity (rieszKernel d s) (confinement a) β (thermalDensity d s a β)) :
    IsThermalDensity (rieszKernel d s) (s46_VQ d s a β γ) γ (thermalDensity d s a β) := by
  refine ⟨h.1, fun x => ?_⟩
  have key : ∀ y : Euc d, -γ * (s46_VQ d s a β γ y +
      convMeasure (rieszKernel d s) (withDensityReal (thermalDensity d s a β)) y) =
      -β * (confinement a y + convMeasure (rieszKernel d s) (withDensityReal (thermalDensity d s a β)) y) := by
    intro y
    unfold s46_VQ
    have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
    rw [hμ]
    field_simp
    ring
  simp_rw [key]
  exact h.2 x

theorem s46_hint {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y)) (withDensityReal (thermalDensity d s a β)) := by
  have hd1 : 1 ≤ d := by omega
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    have hth := can2_isThermalDensity_log hd ha hβ
    obtain ⟨B, M, μ, hS, hM, hρC, hρfix, hpt⟩ := clb_thermalDensity_eq_rep hd1 ha hβ
    have hle : ∀ x, thermalDensity d 0 a β x ≤ M * t67gammaBar d a β x := fun x =>
      (hpt x) ▸ hρC.2 x
    exact can2_hint_log hd1 ha hβ hth.1 (by linarith) hle x
  · have hth := can2_isThermalDensity_pos hd h0 hsd ha hβ
    obtain ⟨_, c, C, hc, hC, hbd⟩ := cb_thermal_two_sided hd1 h0 hsd ha hβ
    obtain ⟨B, _, hB⟩ := convMeasure_bound_of_le hd1 h0 hsd ha hβ
    exact (hB C (thermalDensity d s a β) hth.1 hC.le (fun y => (hbd y).2) x).1

theorem s46_isThermalDensity {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) :
    IsThermalDensity (rieszKernel d s) (confinement a) β (thermalDensity d s a β) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0; exact can2_isThermalDensity_log hd ha hβ
  · exact can2_isThermalDensity_pos hd h0 hsd ha hβ

/-- **`Q_{N,γ₀} = canonicalGibbs g V_Q N γ₀`.** -/
theorem s46_P_eq {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hγ : 0 < γ) (N : ℕ) :
    s46_P d s a β γ N =
      modulatedGibbs (rieszKernel d s) N γ (thermalMeasure d s a β) :=
  HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof (rieszKernel d s) (s46_VQ d s a β γ) γ
    (thermalDensity d s a β) (s46_isThermalDensity_VQ hγ (s46_isThermalDensity hd hs0 hsd ha hβ))
    (fun x => can2_rieszKernel_neg s x) (s46_hint hd hs0 hsd ha hβ)

end S46

end
