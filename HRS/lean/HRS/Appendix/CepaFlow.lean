import HRS.Stochastic.SelectedLawFKE

/-!
# Appendix B (particle dynamics): statements of the remaining rows (packet SPEC-D, part B)

Statements only (`sorry` proofs); every declaration is a specification draft to be compared with
the TeX `HRS_periodic_main_20261008T010000Z.tex` (M).  Rows:

* Proposition B.2 `M:B:prop:cepa-log-flow` (L11662-11670): `cepa_log_flow`;
* Proposition B.4 `M:B:prop:selected-law-smoothing` (L11694-11702): `selected_law_smoothing`;
* Remark B.5 `M:B:rem:d1-particle-threshold` (L11714-11715): no formal content (a pointer);
* Remark B.6 `M:B:rem:sde-wp` (L11717-11719): no formal content (literature and scope);
* Remark B.13 `M:B:rem:d1-threshold-sharp` (L11977-11985): `cepa_noncollision_iff_threshold`;
* Proposition B.14 `M:B:prop:cepa-entropy-confined` (L12020-12032): `cepa_entropy_confined`;
* Proposition B.15 `M:B:prop:sde-entropy-law` (L12140-12152): `sde_entropy_law`;
* the Gibbs-entropy objects of `B:eq:particle-total-potential`, `B:eq:gibbs-relative-entropy-fisher`,
  `B:eq:gibbs-entropy-measure-convention`, `B:eq:selected-fisher-variational` (L12004-12019,
  L12205-12209), which the two entropy propositions need.

Reused (not redefined): `DynData`, `IsStrongSolution`, `PathwiseUnique`, `IsVectorBrownian`
(`Dynamics/Setup.lean`), `IsCepaLepingleFlow`, `SelectedFlow`, `IsFilteredSolution`,
`selectedLaw`, `HasSelectedDensity`, `IsFKETest`, `configLift`, `configBasis`, `fkeGenerator`,
`fkeInteraction` (`Stochastic/SelectedFlow.lean`), `selected_law_fke` (`Stochastic/SelectedLawFKE.lean`),
`relEntropy` (`Energy/Modulated.lean`).

## Representation decisions (to be checked by the orchestrator)

* **Collision-free vs contact flows.**  The Cépa-Lépingle flow is `IsCepaLepingleFlow` (a
  contact-allowing strong solution of the integrated equations, cyclically ordered, with Lebesgue-null
  contact occupation); "the boundary finite-variation process vanishes" is encoded by the absence of any
  reflection term in the integrated equation.  Its uniqueness is stated within that class.
* **Brownian drivers of the canonical flow.**  The TeX (L11664-11665) assigns to a label the Brownian
  motion of its *initial cyclic rank*.  `cepa_log_flow` is stated for an *arbitrary* vector Brownian
  motion `W` independent of `X₀`; the TeX convention is the special case `W̃_i = W_{rank(i)}`, which is
  again a vector Brownian motion independent of `X₀` (the rank is `X₀`-measurable), so the two are
  equivalent.
* **Gibbs entropies** are `EReal`-valued, `𝓗_G(P) = H(P | Z_G⁻¹ G dX) - log Z_G` exactly as in
  `B:eq:gibbs-entropy-measure-convention`, with `Z_G` a `lintegral` (so no Bochner junk) and `H = relEntropy`
  (Mathlib `klDiv`, `⊤` unless `P ≪ Q` with integrable log-likelihood ratio).
* **Fisher information** `𝓘_G(P)` is the lower-semicontinuous extension given by the variational formula
  `B:eq:selected-fisher-variational` (L12205-12209), as a supremum in `ℝ≥0∞` over smooth vector fields
  with compact support in `Ω_N = 𝔇_N^c`; `∇ log G = -β ∇U` on `Ω_N`, computed by differentiating the
  lift of the potential `U`.  The supremum includes `ζ = 0`, so no real `iSup` junk arises.
* The time integral `∫ 𝓘_G(P_N^r) dr` is a `lintegral` (measurability of `r ↦ 𝓘_G(P_N^r)` is provable:
  supremum of narrowly continuous functionals of a narrowly continuous curve).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### Proposition B.2: the canonical one-dimensional logarithmic flow -/

/-- Proposition B.2 (`M:B:prop:cepa-log-flow`, TeX M L11662-11670), Cépa-Lépingle.
Let `d = 1`, `s = 0`, `β_N < ∞` (`0 < invβ`), `M = -a` with `a > 0`, `V'` globally Lipschitz (`V` is
`C¹` with Lipschitz gradient on the covering line).  For every a.s. pairwise distinct initial
configuration `X₀` independent of the Brownian motions `W`, there is a global cyclically ordered
contact-allowing solution (`IsCepaLepingleFlow` on `[0,T]` for every `T`): its drift is integrable
along paths (`lift`, integrated form), the contact set has Lebesgue-null occupation time
(`occupation`), and there is no reflection / local-time term in the integrated equation; and it is
pathwise unique among such flows.

Representation: see the module docstring (Brownian drivers; SVI formulation replaced by the
characterising properties of the flow).  The "cyclic convention" paragraph (L11664-11669: anchor, lifts,
projection, relabelling invariance of the empirical measure) is a construction/convention, not a
separate claim, and is not stated; the relabelling invariance of the empirical measure is immediate
from the definition.
AMBIGUITY (L11665): "Periodicity and permutation equivariance show that another deterministic anchor
gives the same projected empirical process" cannot hold pathwise for a fixed `W` (a different anchor
rotates the Brownian assignment); it holds in law.  Not stated.
The existence clause also asserts (L11663) local time-integrability of each singular pair force
`∇g(x_i - x_j)` (a.s., on `[0,T]`), and that `X` is a strong solution, i.e. `IsFilteredSolution` for every
Brownian filtration `ℱ` of `W` (coordinates `W'`) for which `X₀` is `ℱ t`-measurable for every real `t` (the filtration is real-indexed and `IsFilteredSolution.progressive` includes `t < 0`; repair CEPA-LOG-FLOW, ISSUES 2026-10-18), as consumed by B.3/B.4/B.14.
Technical hypotheses: none beyond the TeX (`X₀` measurable, `W` a vector Brownian motion, independent);
`N` is arbitrary. -/
theorem cepa_log_flow {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hV₁ : Torus.IsCk 1 D.V) {L : ℝ≥0} (hV₂ : LipschitzWith L (gradient (Torus.lift D.V)))
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    (∃ X : ℝ≥0 → Ω → Config 1 N,
      (∀ T : ℝ, 0 ≤ T → IsCepaLepingleFlow P D T X₀ W X) ∧
      -- the singular pair forces are locally integrable in time
      (∀ T : ℝ, 0 ≤ T → ∀ᵐ ω ∂P, ∀ i j : Fin N, i ≠ j →
        IntegrableOn (fun r : ℝ => periodicRieszGrad 1 D.s
          (X (Real.toNNReal r) ω i - X (Real.toNNReal r) ω j)) (Set.Icc 0 T)) ∧
      -- strong solution: adapted to every Brownian filtration of `W` for which `X₀` is `ℱ t`-measurable for every real `t`
      (∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ),
        IsBrownianFiltration P ℱ W' → (∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) →
        (∀ t : ℝ, Measurable[ℱ t] X₀) → IsFilteredSolution P ℱ W' W X)) ∧
    ∀ (T : ℝ) (X X' : ℝ≥0 → Ω → Config 1 N),
      IsCepaLepingleFlow P D T X₀ W X → IsCepaLepingleFlow P D T X₀ W X' →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X' t ω := by
  sorry

/-! ### Proposition B.4: smoothing on the collision-free configuration space -/

/-- The forward Kolmogorov operator `f ↦ β⁻¹ Δ_X f - div_X(b f)` of the particle system, applied at
`(r, X)`, computed through the lift to the covering space `(ℝ^d)^N` at `Y = rep ∘ X`;
`b = particleDrift` (the drift of `H:eq:intro-particles`) and `e_k = configBasis d N k`.
The classical forward equation of B.4 is `∂_r f = fkeForward D f r X` (the adjoint of the generator
whose weak form is `B:eq:selected-law-fke`, L11680-11686). -/
def fkeForward (D : DynData d) (f : ℝ → Config d N → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  let Y : Fin N → Euc d := fun i => Torus.rep (X i)
  D.invβ * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (configLift f r)) Y (configBasis d N k) (configBasis d N k)
  - ∑ k : Fin N × Fin d,
      fderiv ℝ (fun Z : Fin N → Euc d =>
        (particleDrift D (fun i => Torus.mk (Z i)) k.1) k.2 * configLift f r Z) Y
        (configBasis d N k)

/-- Proposition B.4 (`M:B:prop:selected-law-smoothing`, TeX M L11694-11702).
Under Assumption A.1 (`SelectedFlow`, with the Brownian filtration `IsFilteredSolution` exactly as in
Proposition B.3), `β_N < ∞` and `V ∈ C^∞(𝕋^d)`: the (possibly singular) initial law is arbitrary, and
there is `f_N ∈ C^∞((0,T) × Ω_N)`, nonnegative, which is
* the density of every time marginal on `Ω_N` (`P_N^t|_{Ω_N} = f_N^t dX`, all `t ∈ (0,T)`, which is the
  pointwise-in-time form of "the restriction of the spacetime law `dr dP_N^r` to `(0,T) × Ω_N` has
  density `f_N`"; the spacetime statement follows by integrating in `r`), and
* a classical solution of the forward Kolmogorov equation `∂_r f = β⁻¹ Δ f - div(b f)` on `(0,T) × Ω_N`
  (`fkeForward`);
and if the selected process is a.s. collision-free on `[0,T]` then `P_N^t(𝔇_N) = 0` (i.e.
`P_N^t(Ω_N) = 1`) and `P_N^t = f_N^t dX` on all of `𝕋^{dN}` for every `t ∈ (0,T)`.
In the collisional Cépa-Lépingle case `Ω_N` is the disjoint union of the open ordering chambers, so the
smoothness on `Ω_N` is the smoothness on each open chamber; the proposition makes no assertion about a
labelled density on the chamber boundary, hence none is stated.  Smoothness is `ContDiffOn ℝ ∞` of
the lift `(r, Y) ↦ f r (mk ∘ Y)` on `(0,T) × lift(Ω_N)` (`∞` = `((⊤ : ℕ∞) : WithTop ℕ∞)`, not
analyticity).
PARTIAL: `SelectedFlow` omits case (c) of Assumption A.1 (`d = 1`, `s = 0`, `M = 0`, TeX L10130-10133),
so the row is covered only for the cases `SelectedFlow` represents.
Technical hypotheses: `2 ≤ N`, `0 < T`, `hF` (same as `selected_law_fke`, B.3, which the TeX proof
invokes; the filtered-solution structure is the strong-solution adaptedness the manuscript takes for
granted, ISSUES D1). -/
theorem selected_law_smoothing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ f : ℝ → Config d N → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}) ∧
      (∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x) ∧
      (∀ t ∈ Set.Ioo 0 T,
        (selectedLaw P X t).restrict (collisionSet d N)ᶜ =
          ((volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ).withDensity
            (fun x => ENNReal.ofReal (f t x))) ∧
      (∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N,
        HasDerivAt (fun r' => f r' x) (fkeForward D f r x) r) ∧
      ((∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N) →
        ∀ t ∈ Set.Ioo 0 T, selectedLaw P X t (collisionSet d N) = 0 ∧
          selectedLaw P X t =
            (volume : Measure (Config d N)).withDensity (fun x => ENNReal.ofReal (f t x))) := by
  sorry

/-! ### Remarks B.5 and B.6 (no formal content) -/

/-! Remark B.5 `M:B:rem:d1-particle-threshold` (TeX M L11714-11715) has no formal content: it says only
that the logarithmic threshold and the continuation through contacts are explained in Remark B.13.
Remark B.6 `M:B:rem:sde-wp` (TeX M L11717-11719) has no formal content: it lists literature
(`[B-rosenzweig2023global, B-liu2016coulomb, B-cepa1997diffusing, B-cepa2001circle, B-guillin2023oned,
B-decourcel2025sharp]`) and states that the results are finite-`N` and do not verify Assumption `B:ass:MF`
(a non-claim). -/

/-! ### Remark B.13: the one-dimensional logarithmic threshold -/

/-- Remark B.13 (`M:B:rem:d1-threshold-sharp`, TeX M L11977-11985), the checkable content.
For the Cépa-Lépingle flow of B.2 (`d = 1`, `s = 0`, `0 < invβ`, `M = -a`, `a > 0`, `V` as in B.2,
`N ≥ 2`, `T > 0`), almost sure noncollision on `[0,T]` holds iff `a β_N ≥ N` (`β_N = invβ⁻¹`, i.e.
`N * invβ ≤ a`): this is `[B-cepa2001circle, Thm 3.1]`.  The sufficiency half for strong solutions is already
formal (`particle_no_collision_d1_log`, `particle_wellposed_d1_log`, `ParticleLog.lean`); the necessity half
(below the threshold contacts occur with positive probability on every `[0,T]`) is the new content.
The remaining sentences of the remark are statements about hypotheses and are already formal without any
threshold hypothesis: the ordered process continues canonically below the threshold (`cepa_log_flow`
above, whose hypotheses contain no threshold), and the empirical Itô identity has no collision
local-time correction (`cepa_empirical_ito`, whose hypotheses contain no threshold).
Technical hypotheses: `2 ≤ N` (for `N = 1` there are no pairs, so the "only if" fails) and `0 < T`
(on `[0,0]` the initial configuration is collision-free). -/
theorem cepa_noncollision_iff_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hV₁ : Torus.IsCk 1 D.V) {L : ℝ≥0} (hV₂ : LipschitzWith L (gradient (Torus.lift D.V)))
    {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet 1 N) ↔
      (N : ℝ) * D.invβ ≤ a := by
  sorry

/-! ### The Gibbs weight, entropy and Fisher information (`B:eq:particle-total-potential` ff.) -/

/-- The `N`-particle potential `U_{N,V}(X_N) = (1/2N) ∑_{i≠j} g(x_i - x_j) + ∑_i V(x_i)` on `𝕋^d`
(`B:eq:particle-total-potential`, TeX M L12006), `g = periodicRiesz d s`. -/
def totalPotential (D : DynData d) (X : Config d N) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d D.s (X i - X j)
    + ∑ i, D.V (X i)

open Classical in
/-- The unnormalised Gibbs weight `G_{N,β_N,V} = exp(-β_N U_{N,V}) 1_{𝔇_N^c}`
(`B:eq:particle-total-potential`, TeX M L12008), `β_N = invβ⁻¹` (used only with `0 < invβ`). -/
def gibbsWeight (D : DynData d) (X : Config d N) : ℝ :=
  if X ∈ collisionSet d N then 0 else Real.exp (-(D.invβ⁻¹) * totalPotential D X)

/-- The partition function `Z_G = ∫ G dX` as a `lintegral` (the TeX convention, L12016, requires
`0 < Z_G < ∞`, which holds in the situations of B.14 and B.15; the `lintegral` avoids Bochner junk). -/
def gibbsPartition (D : DynData d) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ X : Config d N, ENNReal.ofReal (gibbsWeight D X)

/-- The normalised Gibbs reference measure `Z_G⁻¹ G dX` (TeX M L12018). -/
def gibbsRef (D : DynData d) (N : ℕ) : Measure (Config d N) :=
  (gibbsPartition D N)⁻¹ •
    (volume : Measure (Config d N)).withDensity fun X => ENNReal.ofReal (gibbsWeight D X)

/-- The relative entropy `𝓗_G(P) = H(P | Z_G⁻¹ G dX) - log Z_G` of a probability measure
(`B:eq:gibbs-entropy-measure-convention`, TeX M L12018), `EReal`-valued: `+∞` when `P` is not
absolutely continuous with respect to the normalised Gibbs measure. -/
def gibbsEntropy (D : DynData d) (P : Measure (Config d N)) : EReal :=
  ((relEntropy P (gibbsRef D N) : ℝ≥0∞) : EReal) - ((Real.log (gibbsPartition D N).toReal : ℝ) : EReal)

/-- Test fields of the variational formula `B:eq:selected-fisher-variational` (TeX M L12205-12209):
`ζ ∈ C_c^∞(Ω_N; ℝ^{dN})`, i.e. smooth (through the periodic lift) with compact support in the
collision-free configuration space `Ω_N = 𝔇_N^c`. -/
structure IsFisherTestField (ζ : Config d N → (Fin N → Euc d)) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun Y : Fin N → Euc d => ζ (fun i => Torus.mk (Y i)))
  support : ∃ K : Set (Config d N), IsCompact K ∧ Disjoint K (collisionSet d N) ∧
    ∀ X, X ∉ K → ζ X = 0

/-- The divergence `Div ζ = ∑_{i,j} ∂_{x_{ij}} ζ_{ij}` of a vector field on `𝕋^{dN}`, through the lift
at `Y = rep ∘ X`. -/
def configDiv (ζ : Config d N → (Fin N → Euc d)) (X : Config d N) : ℝ :=
  let Y : Fin N → Euc d := fun i => Torus.rep (X i)
  ∑ k : Fin N × Fin d,
    fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1) k.2) Y
      (configBasis d N k)

/-- The relative Fisher information `𝓘_G(P)` as the lower-semicontinuous extension given by the
variational formula `B:eq:selected-fisher-variational` (TeX M L12205-12209):
`sup_ζ ∫ (-2 Div ζ - 2 ζ·∇log G - |ζ|²) dP`, over `ζ ∈ C_c^∞(Ω_N; ℝ^{dN})`, where on `Ω_N`
`∇ log G = -β_N ∇U_{N,V}`, so that `-2 ζ·∇ log G = 2 β_N D U[ζ]` (`β_N = invβ⁻¹`; `DU[ζ]` computed by
differentiating the lift of `totalPotential`).  `ζ = 0` is admissible, so the supremum is `≥ 0`;
it is `+∞` for measures without a (Sobolev) density.  Used with `0 < invβ`. -/
def fisherInfo (D : DynData d) (N : ℕ) (P : Measure (Config d N)) : ℝ≥0∞ :=
  ⨆ (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ),
    ENNReal.ofReal (∫ X : Config d N,
      (-2 * configDiv ζ X
        + 2 * D.invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc d => totalPotential D (fun i => Torus.mk (Z i)))
            (fun i => Torus.rep (X i)) (ζ X)
        - ∑ i, ‖ζ X i‖ ^ 2) ∂P)

/-- The weak forward equation of Proposition B.3 (`B:eq:selected-law-fke`, TeX M L11680-11686) for a
family of laws `μ`, in the form of `selected_law_fke`: for every `Φ ∈ C_c^{1,2}([0,T) × Ω_N)`,
`-∫ Φ(0,·) dμ_0 = ∫_0^T ∫ (fkeGenerator + fkeInteraction) dμ_r dr`. -/
def SolvesSelectedFKE (D : DynData d) (T : ℝ) (μ : ℝ → Measure (Config d N)) : Prop :=
  ∀ Φ : ℝ → Config d N → ℝ, IsFKETest T Φ →
    - ∫ x, Φ 0 x ∂(μ 0)
      = ∫ r in (0 : ℝ)..T, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x) ∂(μ r)

/-! ### Propositions B.14 and B.15: entropy admissibility -/

/-- Proposition B.14 (`M:B:prop:cepa-entropy-confined`, TeX M L12020-12032): entropy admissibility on the
circle.  `𝔻 = 𝕋`, `X_N` the canonical Cépa-Lépingle flow of B.2 with `a = 1` (`M = -I`), `0 < invβ`,
`V ∈ C²` (`‖V''‖_∞ < ∞` is automatic on the compact torus), initial law with a density `f_N^0` of finite
Gibbs entropy `𝓗_G(f_N^0) < ∞` (`B:eq:cepa-initial-entropy`).  Then for every deterministic `t ∈ [0,T]`
the law `P_N^t` has a density; the family solves the forward equation of B.3 (distributionally, away
from `𝔇_N`); and `𝓗_G(P_N^t) + β_N⁻¹ ∫_0^t 𝓘_G(P_N^r) dr ≤ 𝓗_G(P_N^0)` (`B:eq:cepa-entropy-inequality`),
in `EReal`.  No labelled forward equation across the collision boundary is asserted.
Technical hypotheses: `2 ≤ N`, `0 < T` (as in B.3), `hF` (Brownian filtration, as in B.3, needed to
make the forward-equation clause the one of B.3).  The standing initial-data hypotheses of Assumption
A.1 (`hX₀`, `hdist`, `hW`, `hind`) are listed explicitly. -/
theorem cepa_entropy_confined
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    (∀ t ∈ Set.Icc 0 T, HasSelectedDensity P X t ∧
      gibbsEntropy D (selectedLaw P X t)
        + ((ENNReal.ofReal D.invβ *
            ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P X 0)) ∧
    SolvesSelectedFKE D T (selectedLaw P X) := by
  sorry

/-- Proposition B.15 (`M:B:prop:sde-entropy-law`, TeX M L12140-12152): entropy admissibility of the
selected gradient law.  `X_N` the canonical selected particle process of Assumption A.1
(`SelectedFlow`) with `M = -I`, `0 < invβ`, `V ∈ C²(𝕋^d)`, initial law with a density `f_N^0` of finite
Gibbs entropy `𝓗_G(f_N^0) < ∞` (`B:eq:selected-initial-gibbs-entropy`).  Then for every deterministic
`t ∈ [0,T]` the law `P_N^t` has a density; on `Ω_N` the family solves the selected-law forward equation
of B.3 (`SolvesSelectedFKE`); and `𝓗_G(P_N^t) + β_N⁻¹ ∫_0^t 𝓘_G(P_N^r) dr ≤ 𝓗_G(P_N^0)`
(`B:eq:selected-gradient-entropy`), in `EReal`.  The one-dimensional logarithmic case is B.14.
Technical hypotheses: `2 ≤ N`, `0 < T`, `hF` as in B.3 / B.14. -/
theorem sde_entropy_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hβ : 0 < D.invβ)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    (∀ t ∈ Set.Icc 0 T, HasSelectedDensity P X t ∧
      gibbsEntropy D (selectedLaw P X t)
        + ((ENNReal.ofReal D.invβ *
            ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P X 0)) ∧
    SolvesSelectedFKE D T (selectedLaw P X) := by
  sorry

end HRS
