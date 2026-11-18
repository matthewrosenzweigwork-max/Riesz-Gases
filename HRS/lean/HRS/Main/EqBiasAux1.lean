import HRS.Equilibrium.MarginalDensity
import HRS.Equilibrium.CavityResponse
import HRS.PDE.MeanFieldLinearResponse
import HRS.Sections.Q41Aux14
import HRS.Energy.Modulated

/-!
# EQ-BIAS / EQ-POS: chain plan and foundations (`equilibrium_bias_expansion`, `supercriticalBias_pos`)

Targets (HRS/Main/Equilibrium29Spec.lean, relocated to `HRS/Main/EqBiasFinal.lean`):
* `equilibrium_bias_expansion` (TeX M L981-986; proof L3925-3961, `A:eq:leading-marginal-general`);
* `supercriticalBias_pos` (TeX M L987; proof `A:eq:strict-coefficient`, L3953-3961).

Setting: `d ≥ 2`, `d/2 < s < d`, `p = d/s ∈ (1,2)`, `μ = ρ dx` with `ρ = ρ_β` the thermal density
(smooth and positive: `eqbias_smoothPos`), `n = N - 1`, `λ = β/N`, `δ_N = N^{1-p}` (`deltaN`).
`z_N = dπ_N/dμ - 1 = pDens - 1` (a.e.), `D_N = insDefect` (`= insertionDefect`), `K = Kop`.

## Why the critical files do not apply verbatim

Everything in `L49Aux*`, `L48Aux*`, `CavityPsi/Field/Main`, `TaylorAux*` has `hcrit : s = d/2` in an
`include` (rates `log N/N`, `critical_integrals`); at `s > d/2` the hypotheses are false.  The
general-`s` inputs that ARE reused: `pDens_bounds`, `L2_all` (`‖z_N‖₂ ≤ Cδ_N`), `sup_dev_small`
(`‖z_N‖_∞ → 0`), `cavity_L2` (`‖p - q‖₂ ≤ C√(δ_N/N) = C N^{-p/2}`, `= o(δ_N)` as `p < 2`),
`qDens_bound`, `insDefect_le` (`0 ≤ D_N ≤ Cδ_N`), `cavity_eq_z` (exact cavity equation),
`partA` (`D_N = ∫(1-t)λ² Var_{P_t}(∑ g_+(x-y_i))dt`), `pole_variance_clause`, `pole_density_clauses`,
`pole_dual`, `var_fracF_le`, `critPole_formula`, `gPlus_envelope`, `periodicRiesz_local_singularity`,
`l49_integral_H`; operator side `MFLinear.*` (`TLp_inner_nonneg`, `exists_unique_response_of_one_le`).

## Chain (size in Lean lines; sections S1..S9 are the files EqBiasAux1..9)

S1 (`EqBiasAux1`, ~150) foundations: `eqbias_smoothPos` (thermal + smooth `V` ⇒ `SmoothPosDensity`),
   `eqbias_canonical` (`canonicalGibbs = modulatedGibbs (μ_β)`), `1 < p < 2`, `deltaN = N^{1-p}`.
S2 (`EqBiasAux2`, ~300) operator theory at `μ = ρ dx`: the response `h = responseInverse` is an
   `IsResponse` solution (existence from `exists_unique_response_of_one_le`), coercivity
   `‖u‖ ≤ ‖(I+βT)u‖` on `L²_0(μ)`, Schur bound `‖Kop f‖₂ ≤ C‖f‖₂` for general `s < d`.
   ==> `supercriticalBias_pos` (EQ-POS): `b(ρ) = c₀β^p ⟨h, ρ⟩ = c₀β^p(‖h‖² + β⟨h,Kh⟩) > 0`,
   `h ≠ 0` since `Pρ ≠ 0` for continuous nonconstant `ρ` (positive full-support `μ`).
S3 (`EqBiasAux3`, ~450) supercritical cavity equation (analogue of `response_bound`): with
   `F_N = z_N + βK z_N - P D_N`, `‖F_N‖₂ ≤ ε_N δ_N`, `ε_N → 0`  (inputs: log-Taylor remainder
   `‖z - log(1+z)‖₂ ≤ e^{Mp}‖z‖_∞‖z‖₂ = o(δ)`; forcing `β K(p-q)`: `N^{-p/2} = o(N^{1-p})` by `p<2` and
   the Schur bound; `λ K q = O(1/N) = o(δ)`).
S4 (`EqBiasAux4`, ~350) abstract assembly: from S3, `‖D_N/δ_N - c₀β^pρ‖₂ → 0` (hypothesis lemma `D`),
   coercivity and `h`: `‖z_N/δ_N - c₀β^p h‖₂ → 0`; conversion to `eLpNorm`/`Tendsto` in `ℝ≥0∞` with the
   `rnDeriv` of `firstMarginal (modulatedGibbs …)` (a.e. equal to `pDens`).
S5 (`EqBiasAux5`, ~450) LLN under pole laws: `ε_N := sup_{x,t,y} E_{P_{x,t}}|v_Y(y)| → 0`
   (`v_Y(y) = λ∑_{j≠i} g_+(y-y_j) - β g_+*μ(y)`): truncation `g_+ ∧ K`, `var_fracF_le` for the bounded part,
   `pole_dual` + `cavity/μ` marginal closeness for the mean, one-particle density bound for the tail.
S6 (`EqBiasAux6`, ~350) pole prefactor: `|A_{N,x,t}(y) - 1| ≤ C ε_N` uniformly (copy of `psi_bound`
   with `C₁√δ` replaced by `ε_N`; `Z_bounds`, `v_integral` re-proved without `hcrit`) and the resulting
   `|E_{P_t} f(y_i)² - ∫ f² e^{-tλ f}dμ| ≤ Cε_N ∫ f² e^{-tλf}dμ`.
S7 (`EqBiasAux7`, ~400) radial integrals for `p < 2`: `J(u) = ∫ g_+² e^{-u g_+}dμ ≤ C u^{p-2}`,
   `∫_{|w|>R} g_+² ≤ C R^{d-2s}`, `∫_{|w|≤R} g_+ ≤ C R^{d-s}`.
S8 (`EqBiasAux8`, ~700) compensated local integral: `sup_x |λ^{-p}∫H(λ g_+(x-y))ρ(y)dy - κρ(x)| → 0`,
   `κ = |𝕊^{d-1}|Γ(2-p)/(s p (p-1))` (uses `∫_0^∞ v^{-p-1}(e^{-v}-1+v)dv = Γ(2-p)/(p(p-1))`).
S9 (`EqBiasAux9`, ~600) variance of the pole sum (the core/tail route of TeX L3902-3931):
   `F = F_core + F_tail` at scale `Lλ^{1/s}`; `Var F_tail ≤ C nλ^{p-2}L^{d-2s}` (pole variance clause),
   core diagonal `= nJ(1+O(ε_N))` (S6), core off-diagonal and squared mean `≤ C n²m_c²`, `m_c ≲ L^{d-s}λ^{p-1}`,
   `n²m_c² = o(nλ^{p-2})`; Cauchy-Schwarz for the cross term.  Time integration: `D_N = n∫H(λ g_+)dμ + o(nλ^p)`
   uniformly in `x` (`l49_integral_H`), then with S8: `sup_x|D_N/δ_N - κβ^pρ| → 0`.
Final (`EqBiasFinal`, ~100) `equilibrium_bias_expansion_proof`, `supercriticalBias_pos_proof`,
   `example := (@… : type_of% @HRS.Main.…)`.

Constants: `κ = 2A_{d,s}` of TeX L3838; `supercriticalBiasDensity = κβ^p · responseInverse`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- A thermal density of a smooth potential is a smooth positive probability density. -/
theorem eqbias_smoothPos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) : SmoothPosDensity ρ := by
  obtain ⟨hp, hs⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρ
  exact ⟨hρ.1, hs, hp⟩

/-- The canonical Gibbs law of the thermal potential is the modulated Gibbs law of `μ_β`. -/
theorem eqbias_canonical (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (β : ℝ) (ρ : Torus d → ℝ) (hρs : SmoothPosDensity ρ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (N : ℕ) :
    canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρ hρ
    (fun x => periodicRiesz_neg x) ?_
  intro x
  exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ x).1

/-- `p = d/s ∈ (1,2)` for `d/2 < s < d`. -/
theorem eqbias_p_range {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) (hd : 2 ≤ d) :
    0 < s ∧ 1 < (d : ℝ) / s ∧ (d : ℝ) / s < 2 := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs0 : 0 < s := by linarith
  refine ⟨hs0, ?_, ?_⟩
  · rw [lt_div_iff₀ hs0]; linarith
  · rw [div_lt_iff₀ hs0]; linarith

/-- `δ_N = N^{1-d/s}` for `s > d/2`. -/
theorem eqbias_deltaN {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (N : ℕ) :
    deltaN d s N = (N : ℝ) ^ (1 - (d : ℝ) / s) := by
  unfold deltaN
  rw [if_neg (not_lt.2 hs1.le), if_neg (ne_of_gt hs1)]

end Main

end HRS

end
