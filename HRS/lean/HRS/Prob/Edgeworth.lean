import HRS.Prob.Gaussian
import HRS.Prob.EdgeworthAux
import HRS.Prob.EdgeworthC4Aux

/-!
# Lemma 7.1 `M:O:lem:iid-edge`: initial Hilbert-valued Edgeworth expansion

Source: HRS periodic main paper, lines 7729-7736. The statements were moved unchanged from
`HRS.Prob.Gaussian` so that the proof can use the Stein lemmas (Lemma 7.2) proved there. The
representation of the third-moment pairing is `thirdMomentPairing` (see `docs/ISSUES.md` §G1).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Lemma 7.1 `M:O:lem:iid-edge` (lines 7729-7736), `C_b^6` form: for i.i.d. centered `X_i` in
a separable real Hilbert space with finite fourth moment and `G` centered Gaussian with the same
covariance, uniformly for `‖F‖_{C_b^6(H)} ≤ 1`,
`|E[F(N^{-1/2} ∑ X_i)] - E[F(G)] - (6√N)⁻¹ E[D³F(G)[M₃]]| ≤ C/N`, with `C` depending only on
the second, third and fourth moments.  Degenerate covariance allowed. -/
theorem hilbert_edgeworth_C6 : ∃ C : ℝ → ℝ → ℝ → ℝ, ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (hN : 1 ≤ N)
    (X₀ : Ω → H) (hmeas₀ : AEMeasurable X₀ P) (hcent : ∫ ω, X₀ ω ∂P = 0) (h4 : HasMoment P 4 X₀)
    (X : Fin N → Ω → H) (hiid : IsIIDCopies P X) (hmeas : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, law P (X i) = law P X₀)
    (G : Ω → H) (hG : IsCenteredGaussianRV P G fun x y => ProbabilityTheory.covarianceBilin (law P X₀) x y)
    (F : H → ℝ) (hF : F ∈ CbUnitBall H 6),
    |∫ ω, F ((Real.sqrt N)⁻¹ • ∑ i, X i ω) ∂P - ∫ ω, F (G ω) ∂P -
        (1 / (6 * Real.sqrt N)) * thirdMomentPairing P F G X₀| ≤
      C (momentNorm P 2 X₀) (momentNorm P 3 X₀) (momentNorm P 4 X₀) / N := by
  refine ⟨EdgeAux.c6const, ?_⟩
  intro Ω _ P _ N hN X₀ hmeas₀ hcent h4 X hiid hmeas hlaw G hG F hF
  have h4' : Integrable (fun ω => ‖X₀ ω‖ ^ (4 : ℕ)) P := by
    have h4'' : Integrable (fun ω => ‖X₀ ω‖ ^ (4 : ℝ)) P := h4
    simpa using h4''
  have := EdgeAux.c6_core (P := P) hN hmeas₀ hcent h4' hiid.1 hmeas hlaw hG hF
  simpa [momentNorm] using this


/-- Lemma 7.1, `C_b^4` form with `o(N^{-1/2})` remainder, uniform over families with a uniform
fourth-moment bound and uniformly vanishing squared projection tails: for every such family
(indexed by `ι`) and `ε > 0` there is `N₀` with
`|E[F(N^{-1/2}∑X_i)] - E[F(G)] - (6√N)⁻¹ E[D³F(G)[M₃]]| ≤ ε N^{-1/2}` for `N ≥ N₀`,
uniformly over the family and over `‖F‖_{C_b^4} ≤ 1`.  Tails are measured along a fixed
Hilbert basis `e`.
The copies `Xs i` are random vectors, hence a.e.-measurable; this is stated explicitly because
`IsIIDCopies` does not include it and `law` of a non-measurable map is a junk Dirac mass
(`docs/ISSUES.md` §E). -/
theorem hilbert_edgeworth_C4 (e : HilbertBasis ℕ ℝ H) {ι : Type*}
    {Ω : ι → Type} [∀ a, MeasurableSpace (Ω a)] (P : ∀ a, Measure (Ω a))
    [∀ a, IsProbabilityMeasure (P a)] (X : ∀ a, Ω a → H) (hmeas : ∀ a, AEMeasurable (X a) (P a))
    (hcent : ∀ a, ∫ ω, X a ω ∂(P a) = 0) (M₄ : ℝ)
    (hint4 : ∀ a, Integrable (fun ω => ‖X a ω‖ ^ 4) (P a)) (h4 : ∀ a, ∫ ω, ‖X a ω‖ ^ 4 ∂(P a) ≤ M₄)
    (htail : ∀ ε > 0, ∃ n₀ : ℕ, ∀ a, ∫ ω, ∑' n : {n : ℕ // n₀ ≤ n}, (inner ℝ (e n) (X a ω)) ^ 2 ∂(P a) ≤ ε)
    (G : ∀ a, Ω a → H)
    (hG : ∀ a, IsCenteredGaussianRV (P a) (G a) fun x y => ProbabilityTheory.covarianceBilin (law (P a) (X a)) x y) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a, ∀ (Xs : Fin N → Ω a → H), (∀ i, AEMeasurable (Xs i) (P a)) →
      IsIIDCopies (P a) Xs → (∀ i, law (P a) (Xs i) = law (P a) (X a)) →
      ∀ F : H → ℝ, F ∈ CbUnitBall H 4 →
        |∫ ω, F ((Real.sqrt N)⁻¹ • ∑ i, Xs i ω) ∂(P a) - ∫ ω, F (G a ω) ∂(P a) -
            (1 / (6 * Real.sqrt N)) * thirdMomentPairing (P a) F (G a) (X a)| ≤
          ε / Real.sqrt N :=
  EdgeAux.c4_main e P X hmeas hcent M₄ hint4 h4 htail G hG

end Hilbert

end HRS
