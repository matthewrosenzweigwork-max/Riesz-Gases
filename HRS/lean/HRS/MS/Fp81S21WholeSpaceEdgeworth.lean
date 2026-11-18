import HRS.MS.Fp81S21O4Physical

namespace HRS.Fp81.S21

theorem fp81s21_whole_space_edgeworth : HRS.Whole.WholeSpaceEdgeworthStatement :=
  fp81s21_whole_space_edgeworth_skeleton fp81s21_O4_physical

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_whole_space_edgeworth

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- Theorem S2.1 (S:H:thm:whole-space, TeX S L348-396), part (iii) (L387-394): `0 ≤ s < d/2`; for a positive Riesz
exponent `β₀ > 0`, for the logarithm every `β₀ ≥ 0`; same data as (ii).  The exactly centered path
`ζ_N^{a₀+·}` (centered at the actual first marginal `m_N^t`, the preparation `ℚ_{N,β₀}(μ⁰)`
evolved from time zero) satisfies the uniform `C_b^5` expansion `H:eq:window-edgeworth` in
`𝒳 = C([0,T];B_m)`: there are symmetric projective cubic tensors `κ_{a₀,T} ∈ 𝒳 ⊗̂_π 𝒳 ⊗̂_π 𝒳`
(`projTensor`) with `sup_{a₀≥0} ‖κ_{a₀,T}‖_π < ∞` and a sequence `ε_N(T) → 0` such that, uniformly in
`a₀ ≥ 0` and `‖Φ‖_{C_b^5(𝒳)} ≤ 1`,
`|√N(E Φ(ζ_N^{a₀+·}) - E Φ(Z^{a₀+·})) - (1/6) E⟨D³Φ(Z^{a₀+·}), κ_{a₀,T}⟩| ≤ ε_N(T)`.  The tensor has
the three terms of `H:eq:cubic-formula` with the whole-space adjoint and the actual nonstationary
Gaussian covariance: for every observation family (`φ_i` oscillator test functions at window times
`τ_i ∈ [0,T]`, physical times `t_i = a₀ + τ_i`) and every bounded trilinear form `M` on `𝒳` evaluating
`M(w₁,w₂,w₃) = ∏_i w_i(τ_i)(φ_i)`, and every family `χ_i^r` of signed densities with `χ_i^r/ρ^r ∈ L²(ρ^r dx)` (the source's `L²(μ)`-relative densities; no
smoothness) determined by
`∫ψχ_i^r = Cov(Z^r(ψ), Z^{t_i}(φ_i))` (`linearGaussianCov`; their existence is part of the conclusion, repair P4 of
2026-10-20, so that the formula clause is not vacuous; imposed for *all* `r ∈ [0,a₀+T]`, since
`cubicFormula` uses `χ_{i+1}^r, χ_{i+2}^r` for `r ≤ t_i` where `t_{i+1}` may be smaller; M L1297 defines `χ_i^r`
for all `r`), `⟨κ_{a₀,T}, M⟩ = cubicFormula` with all integrals absolutely defined
(`CubicFormulaIntegrable`, part of the conclusion); the
`r`-integrals begin at physical time `0` even for a late window; at `β₀ = 0` the initial
susceptibility is the identity.  `ε_N(T)` and `κ` depend on the data (they are not uniform over the
class), and `ε_*` is the smallness constant of the class.  The logarithmic endpoint is verified in
`O:cor:log-path` (M), not here.  Depends on S6.3 and on the static/window Edgeworth rows of S9-S11
for its proof.
Technical hypotheses: `T > 0`; the densities `χ_i^r` are quantified (their existence is asserted in the conclusion). -/
theorem whole_space_edgeworth (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀s : 0 < s → 0 < β₀)
    (T : ℝ) (hT : 0 < T) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∃ (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ),
          (∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖κ a₀‖ ≤ Kb) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
            (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
            (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) (M.domDomCongr σ) =
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M) ∧
          Tendsto εN atTop (𝓝 0) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
            (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
            (∃ χ : Fin 3 → ℝ → Euc d → ℝ,
              ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
                MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
                ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                  Integrable (fun x => ψ' x * χ i r x) ∧
                  ∫ x, ψ' x * χ i r x = linearGaussianCov
                    ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                    (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                    ψ' (φ i)) ∧
            ∀ χ : Fin 3 → ℝ → Euc d → ℝ,
            (∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
              MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
              ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                Integrable (fun x => ψ' x * χ i r x) ∧
                ∫ x, ψ' x * χ i r x = linearGaussianCov
                  ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                  (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                  ψ' (φ i)) →
            ∀ M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ,
              (∀ w : Fin 3 → OscPath d (wholeSpaceIndex d) T,
                M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) →
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M =
                cubicFormula (quadraticGradientDyn d s a β) ρ β β₀ (withDensityReal (ρ 0))
                  (fun i => a₀ + τ i) φ χ ∧
              CubicFormulaIntegrable (quadraticGradientDyn d s a β) ρ β₀ (withDensityReal (ρ 0))
                (fun i => a₀ + τ i) φ χ) ∧
          ∀ N : ℕ, 2 ≤ N →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
            (X : ℝ≥0 → Ω → EucConfig d N),
            IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
            law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
            (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
            (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
              (wholeSpaceIndex d) β⁻¹ T'
              (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
          ∀ a₀ : ℝ, 0 ≤ a₀ →
            AEMeasurable (zetaPathW (wholeSpaceIndex d) T a₀ P X) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
            ∀ Φ : OscPath d (wholeSpaceIndex d) T → ℝ,
              Φ ∈ CbUnitBall (OscPath d (wholeSpaceIndex d) T) 5 →
              |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T a₀ P X ζ) ∂P -
                  ∫ ζ', Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ') ∂P') -
                (1 / 6) * ∫ ζ', (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
                  (iteratedFDeriv ℝ 3 Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ')) ∂P'| ≤
                εN N :=
  @HRS.Fp81.S21.fp81s21_whole_space_edgeworth d hd s hs0 hs a β ha hβ β₀ hβ₀ hβ₀s T hT c₁ C₁

end HRS.Whole
