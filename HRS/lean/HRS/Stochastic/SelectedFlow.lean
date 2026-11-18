import HRS.Stochastic.Bridge
import HRS.Dynamics.Setup

/-!
# Selected particle flows: contact-allowing solution concepts and Assumption A.1

Package PART-01, packet P1 (definitions only; no theorems).  Sources
(`HRS_periodic_main_20261008T010000Z.tex`): Assumption A.1 `M:B:ass:sde` (L10127-10143),
Proposition B.2 (L11662-11670, the Cépa–Lépingle ordered flow), Lemma 3.6 (L1637-1648),
Proposition B.3 (L11678-11688), `B:eq:selected-particle-law` (L10141).

Contents:
* `IsContactStrongSolution`: `IsStrongSolution` without the collision-free clause (the notion of
  the Cépa–Lépingle flow, case (c) of A.1);
* `NullContactOccupation`, `CyclicallyOrdered`, `IsCepaLepingleFlow`;
* `IsFilteredSolution`: the Brownian filtration to which a solution is adapted (ISSUES D1; now defined in
  `HRS/Dynamics/Setup.lean`, which Theorem 2.1 needs, and re-exported here by the import);
* `SelectedFlow` (Assumption A.1), `selectedLaw`, `HasSelectedDensity`, `selectedDensity`;
* the test-function classes `IsC12Test`, `IsFKETest` and the generators of Proposition B.3
  (`configLift`, `fkeGenerator`, `fkeInteraction`), the empirical noise integrand and martingale
  (`empiricalNoiseIntegrand`, `empiricalMartingale`) and the label-off-diagonal interaction
  `empiricalInteraction` of Lemma 3.6.

Deviation from `PART01_REST_SPEC.md` (to be reported to the lead): `IsFilteredSolution` carries
an additional field `progressive : IsProgressive ℱ (ofNNRealTime X)`.  The spec's field
`adapted : ∀ t, Measurable[ℱ t] (X t)` is kept verbatim, but it does not imply that the
integrand `empiricalNoiseIntegrand D t f X` is progressively measurable (the paths of `X` are
only a.s. continuous, so on a null set they may be non-measurable in time), and then
`empiricalMartingale` (an `itoIntegral`, junk-valued off the `L²` class) is meaningless.  With
the extra field the statements of Lemma 3.6 / Proposition 3.7 / Proposition B.3 are provable as
stated.  The field holds for every a.s.-continuous adapted process modified on a null set.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d N : ℕ}

/-! ### Contact-allowing solution concepts -/

/-- A strong solution in the sense of `IsStrongSolution` **without** the collision-free
clause: the same `lift`, `init`, `cont`, `adapted` fields.  This is the notion the
manuscript uses for the Cépa–Lépingle flow (case (c) of Assumption A.1, L10136) in which
contacts are allowed.  At a contact, `particleDrift` evaluates the junk value
`periodicRieszGrad d s 0`; see `NullContactOccupation`. -/
structure IsContactStrongSolution (P : Measure Ω) (D : DynData d) (T : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  lift : ∃ Y : ℝ≥0 → Ω → (Fin N → Euc d),
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (∀ i, IntegrableOn (fun s : ℝ => particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
        (Set.Icc 0 (t : ℝ))) ∧
      ∀ i, Y t ω i = Y 0 ω i + (∫ s in Set.Icc (0 : ℝ) t, particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
        + Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i)) ∧
    X = projectPath Y
  init : ∀ᵐ ω ∂P, X 0 ω = X₀ ω
  cont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t => X t ω i
  adapted : ∀ t : ℝ≥0, Measurable (X t)

theorem IsStrongSolution.toContact {P : Measure Ω} {D : DynData d} {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : IsStrongSolution P D T X₀ W X) : IsContactStrongSolution P D T X₀ W X :=
  ⟨h.lift, h.init, h.cont, h.adapted⟩

/-- The set of contact times has Lebesgue measure zero, a.s. (CL 1997, Thm 2.2:
the ordered gap processes are Bessel of dimension δ > 1 and so spend zero time at 0). -/
def NullContactOccupation (P : Measure Ω) (T : ℝ) (X : ℝ≥0 → Ω → Config d N) : Prop :=
  ∀ᵐ ω ∂P, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ω ∈ collisionSet d N} = 0

/-- Cyclic order of a lift `y : Fin N → Euc d` under a labelling `π`: along the lift the
labelled points are nondecreasing and the total spread is at most one period
(`B:eq:…` L11665: "ordered on the circle, with the order preserved").  Stated for every
coordinate so the definition type-checks for general `d`; it is used only with `d = 1`. -/
def CyclicallyOrdered (π : Equiv.Perm (Fin N)) (y : Fin N → Euc d) : Prop :=
  ∀ j : Fin d, (∀ k k' : Fin N, k ≤ k' → y (π k) j ≤ y (π k') j) ∧
    ∀ k k' : Fin N, y (π k') j ≤ y (π k) j + 1

/-- The Cépa–Lépingle ordered flow (Prop B.2, L11662-11670): a contact-allowing strong
solution whose lift is cyclically ordered for all times by a (random, measurable)
labelling fixed at time 0, and whose contact set is Lebesgue-null a.s. -/
structure IsCepaLepingleFlow (P : Measure Ω) (D : DynData d) (T : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  toContact : IsContactStrongSolution P D T X₀ W X
  ordered : ∃ π : Ω → Equiv.Perm (Fin N), (∀ σ, MeasurableSet {ω | π ω = σ}) ∧
    ∀ᵐ ω ∂P, ∃ Y : ℝ≥0 → Fin N → Euc d,
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = fun i => Torus.mk (Y t i)) ∧
      Continuous Y ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T → CyclicallyOrdered (π ω) (Y t)
  occupation : NullContactOccupation P T X

/-! ### Assumption A.1 and the selected law -/

/-- Assumption A.1 (L10127-10143).  Cases (a), (b) and (d) are all "the unique strong
collision-free solution" and collapse into one disjunct; case (c) is the Cépa–Lépingle flow. -/
structure SelectedFlow (P : Measure Ω) (D : DynData d) (T : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  init_meas : Measurable X₀
  init_distinct : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ω => fun t => W t ω) P
  flow :
    (IsStrongSolution P D T X₀ W X ∧ PathwiseUnique P D T X₀ W) ∨
    (d = 1 ∧ D.s = 0 ∧ 0 < D.invβ ∧ (∃ a : ℝ, 0 < a ∧ D.M = -(a • 1)) ∧
      IsCepaLepingleFlow P D T X₀ W X)

/-- `P_N^t := Law(X_N^t)` (`B:eq:selected-particle-law` L10141). -/
def selectedLaw (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) : Measure (Config d N) :=
  law P (X (Real.toNNReal t))

/-- `f_N^t` exists iff `P_N^t ≪ volume`; it is then `rnDeriv`. -/
def HasSelectedDensity (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) : Prop :=
  selectedLaw P X t ≪ (volume : Measure (Config d N))

/-- The density `f_N^t = dP_N^t/dX` (a junk measurable function unless `HasSelectedDensity`). -/
def selectedDensity (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (t : ℝ) : Config d N → ℝ≥0∞ :=
  (selectedLaw P X t).rnDeriv volume

/-! ### Test-function classes -/

/-- Regularity of a time-dependent test `f : ℝ → Torus d → ℝ` on `[0,t]`: the exact
regularity the adjoint solution of Definition 3.5 enjoys (`IsClassicalAdjointSolution`
fields `c2`, `cont_c2`, `cont_time_deriv`), with the time derivative `ft` given on
`Ioo 0 t` and continuous on `Icc 0 t × Torus d`. -/
structure IsC12Test (t : ℝ) (f ft : ℝ → Torus d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, Torus.IsCk 2 (f r)
  cont_c2 : ∀ j ≤ 2, Continuous fun p : Set.Icc (0:ℝ) t × Euc d =>
    iteratedFDeriv ℝ j (Torus.lift (f p.1)) p.2
  time_deriv : ∀ x, ∀ r ∈ Set.Ioo 0 t, HasDerivAt (fun r => f r x) (ft r x) r
  cont_time_deriv : Continuous fun p : Set.Icc (0:ℝ) t × Torus d => ft p.1 p.2

theorem IsClassicalAdjointSolution.isC12Test {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ}
    {φ : Torus d → ℝ} {f : ℝ → Torus d → ℝ} (h : IsClassicalAdjointSolution D ρ t φ f) :
    IsC12Test t f (fun r x => -(backwardGenerator D (ρ r) (f r) x)) :=
  ⟨h.c2, h.cont_c2, h.time_deriv, h.cont_time_deriv.neg⟩

/-- The integrand of the empirical martingale `M_N^t[f]` (`B:eq:…` L1645):
`N⁻¹ √(2/β) ∂_j f(r, x_i(r))` for the coordinate `k = (i,j)`, zero outside `[0,t]`. -/
def empiricalNoiseIntegrand (D : DynData d) (t : ℝ) (f : ℝ → Torus d → ℝ)
    (X : ℝ≥0 → Ω → Config d N) : ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun s ω k => if s ∈ Set.Icc 0 t then
    (Real.sqrt (2 * D.invβ) / N) * (Torus.grad (f s) (X (Real.toNNReal s) ω k.1)) k.2 else 0

/-- The empirical martingale `M_N^τ[f] = ∫_0^τ ∑_{i,j} (empiricalNoiseIntegrand)_{(i,j)} dW'_{(i,j)}`. -/
def empiricalMartingale (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
    (D : DynData d) (t : ℝ) (f : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) : ℝ → Ω → ℝ :=
  itoIntegral P ℱ W' (empiricalNoiseIntegrand D t f X)

/-- Label-off-diagonal empirical interaction (`B:eq:…` L1500, "the CL label-off-diagonal
sum"): `(2N²)⁻¹ ∑_i ∑_{j ≠ i} ⟨∇ψ(x_i) − ∇ψ(x_j), M ∇g(x_i − x_j)⟩`.  At a contact
`x_i = x_j` the summand contains the junk value `∇g(0)`. -/
def empiricalInteraction (D : DynData d) (ψ : Torus d → ℝ) (x : Config d N) : ℝ :=
  (1 / (2 * (N:ℝ)^2)) * ∑ i, ∑ j ∈ Finset.univ.erase i,
    inner ℝ (Torus.grad ψ (x i) - Torus.grad ψ (x j))
      (Torus.matVec D.M (periodicRieszGrad d D.s (x i - x j)))

/-! ### The test class and generators of Proposition B.3 -/

/-- `Φ` read on the covering space. -/
def configLift (Φ : ℝ → Config d N → ℝ) (r : ℝ) (Y : Fin N → Euc d) : ℝ :=
  Φ r (fun i => Torus.mk (Y i))

/-- `C_c^{1,2}([0,T) × Ω_N)`: `C^{1,2}` on the covering space (the exact regularity Itô's
formula needs), vanishing for `r ≥ T'` for some `T' < T`, and vanishing outside a compact
`K ⊆ Ω_N`. -/
structure IsFKETest (T : ℝ) (Φ : ℝ → Config d N → ℝ) : Prop where
  c12 : IsC12On T Set.univ (configLift Φ)
  time_support : ∃ T' < T, ∀ r, T' ≤ r → ∀ X, Φ r X = 0
  space_support : ∃ K : Set (Config d N), IsCompact K ∧ Disjoint K (collisionSet d N) ∧
    ∀ r X, X ∉ K → Φ r X = 0

/-- The basis vector `e_k := Pi.single k.1 (EuclideanSpace.single k.2 1)` of the covering
space `Fin N → Euc d`. -/
def configBasis (d N : ℕ) (k : Fin N × Fin d) : Fin N → Euc d :=
  Pi.single k.1 (EuclideanSpace.single k.2 1)

/-- `∂_r Φ + β⁻¹ Δ_X Φ − ∑_i ∇V(x_i)·∇_{x_i} Φ` at `(r, X)`, computed through the lift
at `Y = rep ∘ X`. -/
def fkeGenerator (D : DynData d) (T : ℝ) (Φ : ℝ → Config d N → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  let Y : Fin N → Euc d := fun i => Torus.rep (X i)
  derivWithin (fun r => configLift Φ r Y) (Set.Icc 0 T) r
  + D.invβ * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (configLift Φ r)) Y (configBasis d N k) (configBasis d N k)
  - ∑ i, fderiv ℝ (configLift Φ r) Y (Pi.single i (Torus.grad D.V (X i)))

/-- `∑_i N⁻¹ ∑_{j ≠ i} ∇_{x_i}Φ · M∇g(x_i − x_j)`, written label-off-diagonal and
antisymmetrised, `w_ij := M∇g(x_i − x_j)`. -/
def fkeInteraction (D : DynData d) (Φ : ℝ → Config d N → ℝ) (r : ℝ) (X : Config d N) : ℝ :=
  let Y : Fin N → Euc d := fun i => Torus.rep (X i)
  (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
    (fderiv ℝ (configLift Φ r) Y
        (Pi.single i (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j))))
     - fderiv ℝ (configLift Φ r) Y
        (Pi.single j (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))))

end HRS
