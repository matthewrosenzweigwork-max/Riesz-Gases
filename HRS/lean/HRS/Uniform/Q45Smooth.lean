import HRS.Uniform.Q45Fnl6

/-!
# Proposition 3.21 `smooth_path_comparison` (packet Q45), proved in the relocated form

`HRS/Uniform/Spec.lean` cannot import this file (the helper files `HRS/Uniform/Q45*.lean` import `Spec`), so the
statement is repeated verbatim as `smooth_path_comparison_proof` and identified with the frozen statement by
`example := (@smooth_path_comparison_proof : type_of% @smooth_path_comparison)`.

Route (TeX M L2233-2257, realised without Itô calculus): the Gaussian heat interpolation is the Lindeberg replacement
method; a generalised finite-dimensional martingale CLT (`Q45Lind*.lean`, with an `ℱ₀`-measurable shift and the
Hessian-pairing seminorm `ν_ρ` in place of the trace norm, which is what makes the constant independent of the grid)
is applied to block-constant integrands (`Q45Blocks*.lean`) on a time/Fourier grid (`Q45Grid*.lean`, `Q45Path*.lean`),
and the grid is removed by `L²`-convergence of Riemann sums and uniform convergence of the interpolants
(`Q45Lim*.lean`, `Q45Core*.lean`, `Q45Fnl*.lean`).  No third derivative is used.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

open HRS.Uniform.Q45 in
/-- Proposition 3.21, proved. -/
theorem smooth_path_comparison_proof (T K : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (_ : S.MaxHyp T K)
        (X₀ X₀' : Ω → H) (_ : Measurable[ℱ 0] X₀) (_ : Measurable[ℱ 0] X₀')
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (_ : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
        (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (_ : IsDetCovDensity T Cb)
        (_ : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cb r))
        (Z Zb R : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j G 0 t (Zb t))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 T))
        (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 T))
        (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
        (X Xb : ℝ → Ω → E)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
        (_ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω),
        ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 T X)) (law P (windowPath 0 T Xb))) ≤
          ENNReal.ofReal C * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 T R ω‖ₑ ∂P +
            ENNReal.ofReal C *
              ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P := by
  refine ⟨detConst T K ^ 2, by positivity, ?_⟩
  intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS X₀ X₀' hX₀ hX₀' M Sg hM G Cb hCb hG Z Zb R hZ hZb hZc
    hZbc hRc hZm hZbm hRm X Xb hXd hXbd
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    exact Q45.smooth_zero_final P ℱ S hS X₀ X₀' hX₀ hX₀' M Sg G Cb Z Zb R hZ hZb hZm hZbm hRm X Xb hXd
      hXbd
  · exact Q45.smooth_pos_final hpos P ℱ S hS X₀ X₀' hX₀ hX₀' M Sg hM G Cb hCb hG Z Zb R hZ hZb hZc hZbc
      hRc hZm hZbm hRm X Xb hXd hXbd

example := (@smooth_path_comparison_proof : type_of% @smooth_path_comparison)

end Uniform

end HRS
