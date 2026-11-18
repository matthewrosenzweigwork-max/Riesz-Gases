import HRS.Main.Headline

/-!
# THERMLIN, part 5: the Gaussian comparison `Y` versus `Z_β` (SPECIFICATION, statements with `sorry`)

This file only states the new lemma `thermlin_gaussian_comparison` that Corollary 2.7 (`thermalization`,
`thermalization_W2`) needs besides the frozen Theorem 2.5 (`prepared_fluctuations`, `prepared_fluctuations_W2`) and
the existence row `preparedLinear_exists` (proved in `ThermLinFinal`).  It is NOT a frozen row of `Headline.lean`;
it is the second half of the proof of Corollary 2.7 (TeX `M:proof:L6969`, L6969-7011, main manuscript).

## Source (TeX L6969-7011, `M:proof:L6969`)

"In the particle comparison first retain the actual initial field.  Couple the resulting linear equation `Y` and a
stationary Gaussian field `Z_β` with one vector white noise, independent of their initial variables.  Their difference
obeys `d(Y-Z_β) = 𝓛_t^T(Y-Z_β)dt + (𝓛_t^T-𝓛_β^T)Z_β dt - √(2/β) Div((√ρ^t-√ρ_β) d𝒲^t)` (`P:eq:Gaussian-difference`).
Choose `b` with `max(1,s+2-d) < b < 2`.  Smooth exponential relaxation and the Fourier multiplier estimates give
`‖(𝓛_t^T-𝓛_β^T)z‖_{E_m} ≤ C e^{-κt}‖z‖_{E_{m-b}}`, `sup_t‖Z_β^t‖_{L²(E_{m-b})} < ∞` (`P:eq:Gaussian-forcing`).  The squared
Hilbert-Schmidt norm of the noise coefficient difference in `E_m` is `≤ C e^{-2κt}`.  The initial term costs
`C e^{-ca}(1+‖Y⁰‖_{L^p(E_m)})`, `p = 1,2`.  Minkowski and `P:eq:decay` bound the general forcing by
`C∫_0^a e^{-c(a-r)}e^{-κr}dr + C_T∫_a^{a+T}e^{-κr}dr ≤ C_T e^{-c'a}` (`P:eq:Gaussian-forcing-integral`), the noise before
`a` by the Itô isometry with doubled exponents, and the noise inside the window by the maximal estimate `P:eq:maximal`.
Thus `‖Y^{a+·}-Z_β^{a+·}‖_{L^p(𝒳_{m,T})} ≤ C_T e^{-c'a}(1+‖Y⁰‖_{L^p(E_m)})`."

The inequality `‖Y^{a+·}-Z_β^{a+·}‖_{L^p(𝒳_{m,T})} ≤ …` for a coupling bounds the Wasserstein distance between the window laws
(`W_p^{𝒳_{m,T}}(Y^{a+·}, Z_β^{a+·}) ≤ …`), and `Z_β^{a+·}` has the law of `Z_β^{0+·}` by stationarity.

## Representation

* `Y` is any `IsPreparedLinear S m (a+T) ν P' Y₀ Y` (law `ν` of the initial field), `Z` any stationary Gaussian field
  (`IsStationaryGaussianField`, thermal density `ρβ` of `(V, β)`) on its own probability space; the coupling of the TeX
  proof is built inside the proof of the lemma, so the statement is a statement about the two LAWS on `𝒳_{m,T}`.
* The constants `C, c` are chosen after `(S, m, T, ρβ)` and before the window start `a`, the initial law `ν`, and the
  probability spaces (they do not depend on `Y`, `Z`: both laws are determined by their finite-dimensional marginals).
* The norms of the initial field are `lintegral`s in `ℝ≥0∞` (the bound is vacuous if infinite); the `W_1` bound uses the
  `L¹(E_m)` norm and the `W_2` bound the `L²(E_m)` norm, exactly as in `H:eq:thermalization` and the `W_2` clause.
* The smooth (`d_2`) comparison of the corollary is the `W_1` clause (`smoothDist 2 ≤ smoothDist 1 ≤ W_1`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

/-- The Gaussian comparison `Y` versus the stationary field `Z_β` (TeX L6969-7011): for the prepared linear process
`Y` with initial law `ν` on the horizon `a + T` and the stationary Gaussian field `Z`,
`W_1^{𝒳_{m,T}}(law Y^{a+·}, law Z^{0+·}) ≤ C e^{-ca}(1 + ‖ν‖_{L¹(E_m)})` and
`W_2^{𝒳_{m,T}}(law Y^{a+·}, law Z^{0+·}) ≤ C e^{-ca}(1 + ‖ν‖_{L²(E_m)})`, with `C, c` independent of `a ≥ 0`, `ν`, `Y`, `Z`. -/
theorem thermlin_gaussian_comparison (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
        {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE 1 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) * (1 + ∫⁻ y, ‖y‖ₑ ∂ν) ∧
        wassersteinE 2 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) *
            (1 + (∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) := by
  sorry

end Main

end HRS
