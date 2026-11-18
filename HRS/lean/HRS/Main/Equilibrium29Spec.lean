import HRS.Main.Headline
import HRS.Stochastic.LyonsZhengSpec
import HRS.Equilibrium.MarginalDensity
import HRS.Equilibrium.StaticLimits
import HRS.Equilibrium.Response
import HRS.Main.HaarAux1
import HRS.PDE.MeanFieldThermalUnique

/-!
# Theorem 2.9 (`M:H:thm:equilibrium`): the missing clauses (SPEC-2.9)

Specification file (statements with `sorry` proofs, except the glue lemmas that are proved;
definitions contain no `sorry`).  Source: `HRS_periodic_main_20261008T010000Z.tex` ("M"), statement
L943-993, proof L3847-3964 (`sec:critical-bias`, marginal expansion, centering transition),
L3984-4163 (stationarity, finite history, stronger topology), L4100-4133 (Lyons-Zheng strong moment).
Before this file only `firstMarginal_canonicalGibbs_const` (`HRS/Energy/Modulated.lean`, last sentence
L992) was stated.

## Clause list (Lean declaration <-> TeX)

| Lean | TeX | content |
|---|---|---|
| `equilibrium_paths_direct` | L945-955 (`H:eq:equilibrium-smooth`, `H:eq:equilibrium-W2`), proof L4090-4099 | `d_2^{𝒳_{m,T}}(ζ_N,Z_β) ≤ C_T√δ_N`, `W_2 ≤ C_T(N^{-1/4}+√δ_N)`, `m > max{d+1,d/2+2}` |
| `equilibrium_paths_interpolation` | L956-966 (`H:eq:equilibrium-interpolation-W`, `-d`), proof L4134-4163 | the stronger topology `m > d/2+1`, `d/2+1<q<m<m_1` |
| (existing) `critical_centered_path` (`HeadlineEquilibrium.lean`) | L967-970 (`H:prop:critical`) | at `s = d/2`, `m ≥ 24d+240`: `W_2, d_k ≤ C_T N^{-1/2}`; NOT restated |
| `equilibrium_marginal_L2` (+ proved `equilibrium_marginal_L2_fixed`) | L972-973, proof L3992 (`P:eq:static-marginal`) | `m_{N,β} ≪ μ_β` and `‖dm_{N,β}/dμ_β - 1‖_{L²(μ_β)} ≤ Cδ_N` |
| `supercriticalBiasDensity`, `supercriticalBias_eq_integral` (proved) | L974-980 (`H:eq:supercritical-bias`) | the density `db_{β,μ}/dμ` of the bias and its link with the existing `supercriticalBias` |
| `equilibrium_bias_expansion` | L981-986 (`H:eq:periodic-bias-expansion`), proof L3925-3961 | `d/2<s<d`: `(dm/dμ-1)/N^{1-d/s} → db/dμ` in `L²(μ_β)` |
| `supercriticalBias_pos` | L987 | nonconstant `ρ_β`: `b_{β,μ_β}(ρ_β) > 0` |
| `centering_transition` (every smooth `φ`), `centering_transition_density` (`φ = ρ_β`) | L988-991, proof L3961-3964 | `√N(μ_N-μ_β)(φ)`: centered Gaussian for `s<2d/3`, shifted by `b(φ)` at `2d/3`, divergent for `s>2d/3` if `b(φ) ≠ 0` |
| `equilibrium_const_background` (proved, from `firstMarginal_canonicalGibbs_const`) | L991-993 | `V` constant: `μ_β = dx` and `m_{N,β} = dx` for every `N`, `s<d` |
| `equilibrium_initial_law` | cited by 5.10: L6926-6940 (`P:eq:Gibbs-initial-smooth`, `-W2`) and L7098 | time-zero static comparison for `η_N^0` (flag (7) of the dependency plan) |
| `lyonsZheng_maximal*` (`HRS/Stochastic/LyonsZhengSpec.lean`) | L4979-4989, L4100-4133 | Lyons-Zheng reversible maximal inequality |

"All bounds are uniform in the start of a fixed-length stationary window" (L967) is the quantifier
`∀ u ≥ 0` after the constant; "no initial Gaussian-approximation error" is that the stationary
Gaussian field `Z_β` is the comparison object.

## Representation decisions (the orchestrator checks each)

* Process: `LZ.IsStationaryGibbsFlow` = `SelectedFlow` of `PDE.mfData` on the horizon `u + T`,
  Brownian filtration (`IsFilteredSolution`; ISSUES D1 "filtered strong solutions"), `law X₀` =
  canonical Gibbs law, exactly the hypotheses of `critical_centered_path`.  `ζ_N` is `windowZeta`
  (centered at the actual mean empirical measure of `X^{u+t}`, which by stationarity is `m_{N,β}`);
  `Z_β` is `IsStationaryGaussianField`, window start `0`; `d_2` is `smoothDist 2`.
* Constants: as in `critical_centered_path` (Prop. 2.10), `C_T` is chosen before `β ∈ [β₋,β₊]` (the
  uniformity paragraph, TeX L1001-1006: "constants ... may be chosen uniformly for β in a compact
  interval"); the fixed-`β` statement of the theorem is the case `β₋ = β₊`.  `C` depends on
  `d, s, V, m, T` (and `q, m_1`), never on `β, ρ_β, u, N`, the probability spaces, `X`, `Z`.
* The thermal density is any `ρ_β` with `IsThermalDensity` (as in Prop. 2.10).  The unique smooth positive
  one exists (`PDE.thermal_exists_unique_smooth`).
* `0 ≤ T` (TeX: "every fixed T<∞"), `N ≥ 2` (standing assumption M L418).
* `L²` statement: `rnDeriv` is junk without absolute continuity, so `≪` is a conjunct; norms are
  `eLpNorm` in `ℝ≥0∞`; the limit in the bias expansion is `Tendsto` in `ℝ≥0∞` (no junk).
* Centering transition: the statistic is `√N(μ_N(φ) - μ_β(φ))` (`linCoord`; the field `η_N` tested on any
  smooth `φ`, "mean-field centering"; `φ = ρ_β` is the density of the proof, the only case where the TeX
  proves `b > 0`), under the canonical Gibbs law (by stationarity its time-`t`
  law for every `t`).  AMBIGUITY: the TeX does not name the statistic or the mode of divergence
  ("diverges in probability"); both the unsigned and the signed (`+∞`, Coulomb paragraph L3969-3972)
  versions are stated for `s > 2d/3`.

## Packet plan for the proofs (sizes S/M/L/XL; order)

Inputs: 3.28 `comparison_smooth`/`comparison_wasserstein` (open, being proved), 4.2/4.3
(`firstMarginal_density_L2`, proved), B.15 free branch (proved; `d ≥ 2` forces the strong branch),
`stationaryField_exists` (proved), Lyons-Zheng (`lyonsZheng_maximal_family`, open).
1. `EQ-GLUE` (done here): `supercriticalBias_eq_integral`, `equilibrium_marginal_L2_fixed`,
   `equilibrium_const_background`.
2. `EQ-MARG-U` (M): uniformity of the constant of `firstMarginal_density_L2` over `β ∈ [β₋,β₊]` and
   all thermal `ρ_β` of a fixed smooth `V` -> `equilibrium_marginal_L2` (needs the 4.2 constant to be
   uniform along the smooth family `β ↦ ρ_β`; if not extractable, restate at fixed `β`).
3. `EQ-LZ` (L + M + M-L, see `LyonsZhengSpec.lean`): Lyons-Zheng, then the stationary strong moment
   `sup_N E sup_{t≤T}‖ζ_N^t‖²_{E_q} < ∞`, `q > d/2+1` (`P:eq:stationary-strong-moment`, L4127-4133),
   and the same for `Z_β` (Gaussian path maximal estimate `P:eq:maximal`).
4. `EQ-REM` (L): stationary remainder `R_{N,stat}` (`P:eq:stationary-identity`, `-R`, L4009-4047):
   needs Theorem 2.1 (proved) for the exact centered identity, variance bounds
   `P:eq:static-linear and P:eq:static-quadratic` (4.x, proved), `equilibrium_marginal_L2`; gives
   `sup_t‖R^t‖_{L²(E_M)} ≤ C_Mε_N` and the time-integrated remainder (via 4.17 `integrated_forcing`
   in the critical case, `Minkowski + P:eq:decay` otherwise); bracket bias `P:eq:stationary-trace` (M).
5. `EQ-COMP` (XL): burn-in estimates `P:eq:burnin-smooth and P:eq:burnin-W2` (L4083-4094): independent stationary
   Gaussian initial field, global polar coupling, 3.28 for smooth and Wasserstein distances; the
   Lyapunov identity `P:eq:Lyapunov` (stationarity of `Z_β`, exists as `IsStationaryGaussianField`),
   then `a → ∞` at fixed `N` -> `equilibrium_paths_direct` (S, with `b_N ≤ Cε_N`,
   `√b_N ≤ N^{-1/4}+ε_N`).
6. `EQ-INTERP` (M for W, M-L for d): Sobolev Hölder interpolation `P:eq:Sobolev-interpolate` (S),
   its use on polar couplings (W_2, requires the coupling form of `wassersteinE`), and the frequency
   cut-off `P_R` with `C_b²` composition estimate `P:eq:stationary-smooth-projection` -> `equilibrium_paths_interpolation`.
7. `EQ-BIAS` (L): cavity solution of the marginal response, `A:eq:leading-marginal-general`
   (L3938-3958), from 4.2/4.3 (proved) and the bounded inverse of `I + βT_μ`; with `μ = μ_β` gives
   `equilibrium_bias_expansion`.  `EQ-POS` (M): `A:eq:strict-coefficient` (self-adjointness of
   `R_{β,μ}`, `P_μρ_β ≠ 0` iff `ρ_β` nonconstant) -> `supercriticalBias_pos`.
8. `EQ-TRANS` (M): static CLT `ζ_N(ρ_β) ⇒ N(0, C_β(ρ_β,ρ_β))` (from `equilibrium_paths_direct` at `T = 0`
   with the evaluation functional, `smoothDist_map_clm_le`; or the static CLT) + shift `√N(m_N-μ_β)(ρ_β) =
   √Nδ_N(b+o(1))` from `equilibrium_bias_expansion` and Slutsky for `ConvergesInLaw`.
9. `EQ-INIT` (M): `equilibrium_initial_law` from `equilibrium_paths_direct` at time zero (projection
   `ev₀`, `wassersteinE_map_clm_le`, `smoothDist_map_clm_le`) plus the `E_m` bound
   `‖√N(m_N-μ_β)‖_{E_m} ≤ C√Nδ_N` from `equilibrium_marginal_L2` and `√δ_N ≤ √Nδ_N`.
Non-vacuity: `IsStationaryGibbsFlow` is not asserted satisfiable (same exposure as
`critical_centered_path`); stationarity/reversibility of the Gibbs flow is a theorem to prove (B.15
`sde_entropy_law` + time reversal, packet LZ-b of `LyonsZhengSpec.lean`).  LZ proof route (recorded
there): smooth compactly supported off collisions -> truncation -> collision cut-off by zero weighted
capacity for `d ≥ 2` -> Fatou over rational times.
`EQ-NONVAC` (S): for `equilibrium_paths_interpolation` at small `m` (`d/2+1 < m ≤ max{d+1,d/2+2}`) the
statement must not be vacuous: record the inclusion `E_{m₁} ↪ E_m`, so the clause is the interpolation
of the direct clause at `m₁` and the `q`-moment; `Z` exists in `E_m` by `stationaryField_exists` (`m > d/2`).
`EQ-MARG-U` refinement: do not reprove 4.2; extract the dependence of its constant on the bounds of
`ρ_β` (positive lower/upper bounds, `C^k` norms) and show these are uniform for `β ∈ [β₋,β₊]` (thermal
equation + bootstrap).
Order: 2, 3 (parallel) -> 4 -> 5 (blocked on 3.28) -> 6; 7 independent of 3-6; 8, 9 last.

## Doubts for the reviewer

* Uniformity in `β`: stated for the path/L² clauses as in Prop. 2.10; the TeX theorem itself is
  fixed-`β`.  Either reading is a one-line change.
* `equilibrium_marginal_L2_fixed` is the proved fixed-`β` version (4.2 constant depends on `ρ`).
* Interpolation clause: "choose `q < m < m_1`" is read as for EVERY admissible `(q, m_1)` (the
  proof L4134-4163 works for any), the constant depending on them.
* Spec flag (7): the clause that 5.10 cites is `equilibrium_initial_law` (static, `η_N^0`, `m > d+2`),
  not literally printed in 2.9; it is the time-zero case of the path clauses plus the marginal bound.
* Spec flag (10): coverage row 2.9 should list all of the above.
* `smoothDist`/`wassersteinE` of `law P (windowZeta ..)`: `0`-junk if the window map is not a.e.
  measurable (it is, by `SelectedFlow`); no Dirac junk since `Measure.map` of a non-a.e.-measurable
  map is `0`, and then the bounds would compare against the zero measure, which the hypotheses exclude.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

open HRS.LZ

variable {d : ℕ}

/-! ### The density of the supercritical bias -/

/-- The density `db_{β,μ}/dμ (x) = |𝕊^{d-1}|Γ(2-p)/(s p (p-1)) β^p (R_{β,μ}P_μρ)(x)`, `p = d/s`, of
`b_{β,μ}` (`H:eq:supercritical-bias`, TeX L974-980), `μ = ρ dx` (`responseInverse` is `R_{β,μ}P_μ`,
as in `criticalBias`). -/
def supercriticalBiasDensity (d : ℕ) (s β : ℝ) (ρ : Torus d → ℝ) (x : Torus d) : ℝ :=
  sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1)) * β ^ ((d : ℝ) / s) *
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x

/-- `b_{β,μ}(φ) = ∫ φ (db_{β,μ}/dμ) dμ` (consistency of `supercriticalBias`
(`HRS/Equilibrium/Response.lean`) with the density `supercriticalBiasDensity`). -/
theorem supercriticalBias_eq_integral (d : ℕ) (s β : ℝ) (ρ φ : Torus d → ℝ) :
    supercriticalBias d s β ρ φ =
      ∫ x, supercriticalBiasDensity d s β ρ x * φ x ∂(withDensityReal ρ) := by
  unfold supercriticalBias supercriticalBiasDensity
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-! ### The marginal: `L²` bound -/

/-- Theorem 2.9 `M:H:thm:equilibrium`, marginal bound (TeX L972-973; proof L3992
`P:eq:static-marginal`, Proposition 4.2): `m_{N,β} ≪ μ_β` and
`‖dm_{N,β}/dμ_β - 1‖_{L²(μ_β)} ≤ Cδ_N`, `N ≥ 2`, `0 ≤ s < d`, `d ≥ 2`, smooth `V`; the constant `C` is
chosen before `β ∈ [β₋,β₊]` (uniformity paragraph, TeX L1001-1006).  Technical hypotheses: `N ≥ 2`
(standing, M L418).  `≪` is a conjunct: `rnDeriv` is junk without it. -/
theorem equilibrium_marginal_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ ∧
        eLpNorm (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
            (withDensityReal ρβ) y).toReal - 1) 2 (withDensityReal ρβ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  sorry

/-- Fixed-`β` version of `equilibrium_marginal_L2` (the case `β₋ = β₊ = β`, but for the smooth positive
thermal density and without uniformity in `β`), PROVED from Proposition 4.2 `firstMarginal_density_L2`
and `P_{N,β} = Q_{N,β}(μ_β)` (`canonicalGibbs_eq_modulatedGibbs`). -/
theorem equilibrium_marginal_L2_fixed (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ) (hρs : SmoothPosDensity ρβ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ ∧
        eLpNorm (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
            (withDensityReal ρβ) y).toReal - 1) 2 (withDensityReal ρβ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  have hP : ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
    intro N
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρ
      (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ x).1
  obtain ⟨C, hC⟩ := firstMarginal_density_L2 hd hs0 hsd β hβ ρβ hρs
  refine ⟨C, fun N hN => ?_⟩
  rw [hP N]
  exact hC N hN

/-! ### The supercritical bias expansion -/

/-- Theorem 2.9 `M:H:thm:equilibrium`, supercritical bias expansion
`H:eq:periodic-bias-expansion` (TeX L981-986; proof L3925-3961, `A:eq:leading-marginal-general`):
for `d/2 < s < d`, `d ≥ 2`, smooth `V`, `β > 0`, `ρ_β` the thermal density,
`‖(dm_{N,β}/dμ_β - 1)/N^{1-d/s} - db_{β,μ_β}/dμ_β‖_{L²(μ_β)} → 0`
(`db/dμ = supercriticalBiasDensity`, `H:eq:supercritical-bias`), and `m_{N,β} ≪ μ_β` for `N ≥ 2`.
Fixed `β` (a limit, no rate asserted). -/
theorem equilibrium_bias_expansion (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    (∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ) ∧
    Tendsto (fun N : ℕ =>
      eLpNorm (fun y =>
        (((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
            (withDensityReal ρβ) y).toReal - 1) / (N : ℝ) ^ (1 - (d : ℝ) / s) -
          supercriticalBiasDensity d s β ρβ y) 2 (withDensityReal ρβ)) atTop (𝓝 0) := by
  sorry

/-- Theorem 2.9 `M:H:thm:equilibrium` (TeX L987, proof `A:eq:strict-coefficient`, L3948-3961):
for `d/2 < s < d` and a nonconstant thermal density `ρ_β`, `b_{β,μ_β}(ρ_β) > 0`. -/
theorem supercriticalBias_pos (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hnc : ∃ x y, ρβ x ≠ ρβ y) :
    0 < supercriticalBias d s β ρβ ρβ := by
  sorry

/-! ### The centering transition -/

/-- Theorem 2.9 `M:H:thm:equilibrium` (TeX L988-991; proof L3961-3964): "mean-field centering has the same
centered Gaussian limit for `s < 2d/3`, a nonzero deterministic shift at `s = 2d/3`, and a statistic that
diverges in probability for `s > 2d/3`", for every smooth observation `φ`.  The statistic is
`√N(μ_N(φ) - μ_β(φ))` (`linCoord`, the field `η_N` tested on `φ`) under the canonical Gibbs law (the law of
`η_N^t` for every `t` along the stationary flow).  With `v = C_β(φ,φ)` (`susceptibilityCov`) and
`b = b_{β,μ_β}(φ)` (`supercriticalBias d s β ρβ φ`):
* `s < 2d/3`: convergence in law to `N(0,v)`;
* `s = 2d/3`: convergence in law to `N(b,v)`;
* `s > 2d/3`, `b ≠ 0`: `|statistic| → ∞` in probability; if `b > 0` also `statistic → +∞`
  in probability (TeX L3969-3972 for the signed version).
(For `s ≤ d/2` the bias term is the `δ_N`-bound only; `b` is the `s > d/2` coefficient and is used only for
`s ≥ 2d/3 > d/2`.)  AMBIGUITY: the TeX does not say which statistic. -/
theorem centering_transition (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) :
    (s < 2 * (d : ℝ) / 3 →
      ConvergesInLaw
        (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
          (linCoord (withDensityReal ρβ) φ))
        (gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ))) ∧
    (s = 2 * (d : ℝ) / 3 →
      ConvergesInLaw
        (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
          (linCoord (withDensityReal ρβ) φ))
        ((gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ)).map
          (fun x => x + supercriticalBias d s β ρβ φ))) ∧
    (2 * (d : ℝ) / 3 < s → supercriticalBias d s β ρβ φ ≠ 0 →
      ∀ M : ℝ, Tendsto (fun N : ℕ =>
        canonicalGibbs (periodicRiesz d s) V N β
          {X | M < |linCoord (withDensityReal ρβ) φ X|}) atTop (𝓝 1)) ∧
    (2 * (d : ℝ) / 3 < s → 0 < supercriticalBias d s β ρβ φ →
      ∀ M : ℝ, Tendsto (fun N : ℕ =>
        canonicalGibbs (periodicRiesz d s) V N β
          {X | M < linCoord (withDensityReal ρβ) φ X}) atTop (𝓝 1)) := by
  sorry

/-- The density instance `φ = ρ_β` of `centering_transition` (the observation of the proof, TeX
L3961-3964), where `b_{β,μ_β}(ρ_β) > 0` for nonconstant `ρ_β` (`supercriticalBias_pos`): shift at
`s = 2d/3` and divergence to `+∞` for `s > 2d/3`.  Technical hypothesis: `ρ_β` smooth (the unique
thermal density is smooth, `PDE.thermal_exists_unique_smooth`).  PROVED from `centering_transition` and
`supercriticalBias_pos`. -/
theorem centering_transition_density (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρs : Torus.IsSmooth ρβ) :
    (s < 2 * (d : ℝ) / 3 →
      ConvergesInLaw
        (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
          (linCoord (withDensityReal ρβ) ρβ))
        (gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ρβ ρβ))) ∧
    (s = 2 * (d : ℝ) / 3 →
      ConvergesInLaw
        (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
          (linCoord (withDensityReal ρβ) ρβ))
        ((gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β ρβ ρβ)).map
          (fun x => x + supercriticalBias d s β ρβ ρβ))) ∧
    (2 * (d : ℝ) / 3 < s → (∃ x y, ρβ x ≠ ρβ y) →
      (∀ M : ℝ, Tendsto (fun N : ℕ =>
        canonicalGibbs (periodicRiesz d s) V N β
          {X | M < |linCoord (withDensityReal ρβ) ρβ X|}) atTop (𝓝 1)) ∧
      (∀ M : ℝ, Tendsto (fun N : ℕ =>
        canonicalGibbs (periodicRiesz d s) V N β
          {X | M < linCoord (withDensityReal ρβ) ρβ X}) atTop (𝓝 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := centering_transition hd hs0 hsd V hV β hβ ρβ hρβ ρβ hρs
  refine ⟨h1, h2, fun hs hnc => ?_⟩
  have hd2 : (d : ℝ) / 2 < s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hpos := supercriticalBias_pos hd hd2 hsd V hV β hβ ρβ hρβ hnc
  exact ⟨h3 hs hpos.ne', h4 hs hpos⟩

/-- The constant density `1` is a thermal density for a constant potential (translation invariance
of Haar measure makes `g * 1` constant). -/
theorem equilibrium_one_thermal (g : Torus d → ℝ) (c β : ℝ) :
    IsThermalDensity g (fun _ => c) β (fun _ => (1 : ℝ)) := by
  have hc : ∀ x : Torus d, convFun g (fun _ => (1 : ℝ)) x = ∫ y, g y := by
    intro x
    unfold convFun
    simp only [mul_one]
    exact integral_sub_left_eq_self g volume x
  refine ⟨⟨fun _ => zero_le_one, measurable_const, by simp⟩, fun x => ?_⟩
  simp only [hc, integral_const, smul_eq_mul]
  have hv : (volume : Measure (Torus d)).real Set.univ = 1 := by simp
  rw [hv, one_mul]
  have := Real.exp_pos (-β * (c + ∫ y, g y))
  rw [div_self this.ne']

/-- Theorem 2.9 `M:H:thm:equilibrium`, last sentence (TeX L991-993): "if `V` is constant,
`m_{N,β} = μ_β = dx` exactly, for every `N` and `s < d`": every continuous positive thermal density of a
constant potential is `1`, so `μ_β = dx`; and `m_{N,β} = dx` for `N ≥ 1`.  PROVED from
`firstMarginal_canonicalGibbs_const` and the uniqueness of the thermal density. -/
theorem equilibrium_const_background (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (c β : ℝ) (hβ : 0 < β) :
    (∀ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d s) (fun _ => c) β ρ → Continuous ρ →
      (∀ x, 0 < ρ x) → withDensityReal ρ = (volume : Measure (Torus d))) ∧
    ∀ N : ℕ, 1 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) (fun _ => c) N β) = volume := by
  refine ⟨fun ρ hρ hc hp => ?_, fun N hN => firstMarginal_canonicalGibbs_const hd hs0 hsd c β hβ hN⟩
  have h1 : (fun _ : Torus d => (1 : ℝ)) = ρ :=
    PDE.MFThermal.thermal_unique hd s hs0 hsd β hβ (fun _ => c) ρ (fun _ => 1) hρ hc hp
      (equilibrium_one_thermal _ c β) continuous_const (fun _ => one_pos)
  rw [← h1]
  unfold withDensityReal
  simp

/-! ### The path clauses -/

/-- Theorem 2.9 `M:H:thm:equilibrium`, direct estimates (`H:eq:equilibrium-smooth`,
`H:eq:equilibrium-W2`, TeX L945-955; proof L4083-4099 and `P:eq:burnin-smooth and P:eq:burnin-W2`):
`d ≥ 2`, `0 ≤ s < d`, `β > 0`, smooth `V`, stationary canonical gradient dynamics (`IsStationaryGibbsFlow`,
`law X₀` = `ℙ_{N,β}`), centered at the actual first marginal (`windowZeta`), `m > max{d+1, d/2+2}`,
`T < ∞`: `d_2^{𝒳_{m,T}}(ζ_N, Z_β) ≤ C_T √δ_N` and `W_2^{𝒳_{m,T}}(ζ_N, Z_β) ≤ C_T(N^{-1/4} + √δ_N)`,
with `C_T` independent of the window start `u ≥ 0` (TeX L967), of `N ≥ 2`, `β ∈ [β₋,β₊]`, and of the
realization and the field `Z`.  `Z_β` is any `IsStationaryGaussianField` (window start `0`; its law is
stationary).  Technical hypotheses: `N ≥ 2` (M L418), `0 ≤ T`, probability measures. -/
theorem equilibrium_paths_direct (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (u + T) X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        smoothDist 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            C * Real.sqrt (deltaN d s N) ∧
        wassersteinE 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N))) := by
  sorry

/-- Theorem 2.9 `M:H:thm:equilibrium`, the stronger topology (`H:eq:equilibrium-interpolation-W`,
`H:eq:equilibrium-interpolation-d`, TeX L956-966; proof L4134-4163, `P:eq:Sobolev-interpolate`,
`P:eq:stationary-smooth-projection`): for every `m > d/2+1` and every `d/2+1 < q < m < m_1` with
`m_1 > max{d+1, d/2+2}`,
`W_2^{𝒳_{m,T}}(ζ_N, Z_β) ≤ C_T (N^{-1/4} + √δ_N)^{(m-q)/(m_1-q)}` and
`d_2^{𝒳_{m,T}}(ζ_N, Z_β) ≤ C_T δ_N^{(m-q)/(2(2m_1-m-q))}`.
Same hypotheses and uniformity as `equilibrium_paths_direct`; `C_T` depends on `q, m_1` too.
READING: "choose q<m<m_1" is for every admissible choice (the proof works for each). -/
theorem equilibrium_paths_interpolation (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : (d : ℝ) / 2 + 1 < m) (q m₁ : ℝ) (hq : (d : ℝ) / 2 + 1 < q) (hqm : q < m)
    (hmm₁ : m < m₁) (hm₁ : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m₁) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (u + T) X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        wassersteinE 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 4) + Real.sqrt (deltaN d s N)) ^
              ((m - q) / (m₁ - q))) ∧
        smoothDist 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            C * deltaN d s N ^ ((m - q) / (2 * (2 * m₁ - m - q))) := by
  sorry

/-- The time-zero static comparison cited by Proposition 5.10 (TeX L6926-6940,
`P:eq:Gibbs-initial-smooth`, `P:eq:Gibbs-initial-W2`; "Theorem 2.9 evaluated at time zero ... gives an
explicit static comparison"; spec flag (7) of the dependency plan): for `m > d+2`, the mean-field
centered field `η_N^0 = √N(μ_N - μ_β)` under the canonical Gibbs law and the Gaussian `Z_β^0` satisfy
`d_{2,E_m}(η_N^0, Z_β^0) ≤ C √N δ_N` and
`W_{2,E_m}(η_N^0, Z_β^0) ≤ C(√N δ_N + N^{-1/4} + ε_N)`, `ε_N = √δ_N` (TeX L3344).
`Z_β^0` is the time-zero value of an `IsStationaryGaussianField`.  Same conventions as
`equilibrium_paths_direct` (constant before `β ∈ [β₋,β₊]`, `N ≥ 2`). -/
theorem equilibrium_initial_law (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : (d : ℝ) + 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        smoothDist 2 (law (canonicalGibbs (periodicRiesz d s) V N β)
            (fun X => etaE m X (withDensityReal ρβ))) (law P' (Z 0)) ≤
          C * (Real.sqrt N * deltaN d s N) ∧
        wassersteinE 2 (law (canonicalGibbs (periodicRiesz d s) V N β)
            (fun X => etaE m X (withDensityReal ρβ))) (law P' (Z 0)) ≤
          ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N + (N : ℝ) ^ (-(1 : ℝ) / 4) +
            Real.sqrt (deltaN d s N))) := by
  sorry

end Main

end HRS
