import HRS.Uniform.Comparison
import HRS.Stochastic.SelectedFlow
import HRS.Stochastic.Duality

/-!
# Packet GF-SPEC, part 1: definitions, the evolution inputs (GF-EV), continuity (GF-CONT), small items

All declarations of this file are STATEMENTS of the sub-packets of the proof of Theorem 2.1
(`HRS.GeneralSetup.general_fluctuation`, `_transport`, `_matrix`; TeX M L580-620, proof L2445-2478, L3294-3310)
unless marked "PROVED".  The chain plan and the inventory of the proved inputs is in the header of
`HRS/Main/GFAux1.lean`; the overall assembly plan (and the conditional assembly theorems) is in the header of
`HRS/Main/GFSpec7.lean`.  Nothing here edits an existing statement.

## Representation decisions of the GF-SPEC files (consequential: please review)

* **One abstract chain for the three statements.**  Let `H = E_γ = NegSobolev d γ` and `E = E_m = NegSobolev d m`
  with `m = γ` (gradient clause and its transport variant, `M = -I`, `EvolData.Dissipative` alternative, `E = H`)
  or `m = γ + 2` (matrix clause, `EvolData.TwoLevel` alternative).  The evolution is the `EvolData H E` of Lemma 3.17
  (`HRS.Uniform.EvolData`) with `j = embed m`; its dual action is *characterised* by the pairing identity
  `⟨V(t,r) z, φ⟩ = ⟨z, U^{r,t} φ⟩` (`IsDualOn`, a horizon-`T` version of `HRS.Uniform.IsDualEvolution`, which
  quantifies over all `t` and so cannot be used when `ρ_N` is only regular on `[0,T]`).  Both alternatives are bundled
  in `GFEvo` together with the adjoint bound that the remainder estimate needs.
* **`flucProc`** is the ℝ-indexed `E_m`-valued process `t ↦ σ_N(μ_N^t - μ^t)`; `flucPath` of the frozen statements is its
  `windowPath 0 T` (`flucPath_eq_windowPath`, PROVED).  `PathSpace d m T` and `Uniform.PathSp T (NegSobolev d m)` are two
  `def`s of `C([0,T]; E_m)` with `inferInstanceAs` instances, hence defeq: no transport map is needed, the laws are
  literally equal (`toPath_eq_windowPath`, `flucPath_eq_windowPath`); this settles the "PathSpace vs PathSp" item of
  `GFAux1`.
* **Constants.**  The `C₀`-threshold prefix of `general_fluctuation` is mirrored: every packet whose proof touches the energy
  completion has the shape `∃ C₀min, ∀ C₀ ≥ C₀min, ∃ C, …`, and quantifies over setups `S.Within { b with C₀ := C₀ }`.
  Packets that do not see `C₀` (evolution, continuity, martingale) are stated for `S.Within { b with C₀ := S.C₀ }`
  (the bounds `b` up to the free completion constant), so that no `C₀` quantifier is needed.
* **`Ω : Type`** throughout (`smooth_path_comparison_proof`, `maximal_estimate_meas` are stated at `Type`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-! ### Definitions -/

/-- The fluctuation process `t ↦ Ξ^t = σ (μ_N^t - μ^t)` as an `ℝ`-indexed `E_m`-valued process
(NEW definition; the path version of the frozen statements is `HRS.flucPath`, equal to its `windowPath 0 T` by
`flucPath_eq_windowPath`). -/
def flucProc {Ω : Type*} {N : ℕ} (m σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) :
    ℝ → Ω → NegSobolev d m :=
  fun t ω => σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))

/-- `σ_N = min{κ_N, √(Nβ_N)}` of the setup at particle number `N` (abbreviation of `sigmaScale`, NEW). -/
abbrev sigN (S : GeneralSetup d) (N : ℕ) : ℝ := sigmaScale N (S.κ N) (S.invβ N)

/-- `A_N = σ_N/κ_N` (abbreviation of `Ascale`, NEW). -/
abbrev AN (S : GeneralSetup d) (N : ℕ) : ℝ := Ascale N (S.κ N) (S.invβ N)

/-- `q_N = σ_N²/(Nβ_N)` (abbreviation of `qScale`, NEW). -/
abbrev qN (S : GeneralSetup d) (N : ℕ) : ℝ := qScale N (S.κ N) (S.invβ N)

/-- Horizon-`T` version of `HRS.Uniform.IsDualEvolution`: `V(t,u)` on `E_m` is dual to the adjoint propagator,
`⟨V(t,u) z, φ⟩ = ⟨z, U^{u,t} φ⟩` for `0 ≤ u ≤ t ≤ T` and smooth `φ` (NEW definition). -/
def IsDualOn (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) : Prop :=
  ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (z : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
    NegSobolev.eval (V t u z) φ = NegSobolev.eval z (propagator D ρ u t φ)

/-- The evolution input of the proof of Theorem 2.1 at level `m` (NEW definition; it is the common output of the two
evolution packets `gf_ev_grad`, `gf_ev_mat`).  `EV : EvolData E_γ E_m` is an evolution in the sense of Lemma 3.17
satisfying `MaxHyp T K` (either alternative), whose embedding is `embed m`, whose action `EV.VE` on `E_m` is dual to the
adjoint propagator of `(D, ρ_N)`, and the adjoint propagator is the genuine one and bounded in `H^m` with constant `K`.

The last field (`adjoint`) is `AdjointInput` at the single level `m` (`H:eq:matrix-adjoint-input`, L609-616): for the
gradient clause it is the `E_γ`-boundedness of the dual evolution, for the matrix clause it is the hypothesis itself. -/
/- Notes: (N2) in the `Dissipative` alternative the core `D` is `E_{γ-2}`, not the trigonometric polynomials; (N3) `GFEvo` is
unsatisfiable for `m < γ` (harmless, only `m ≥ γ` is used). -/
structure GFEvo (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (N : ℕ) (m K : ℝ)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) : Prop where
  maxHyp : EV.MaxHyp S.T K
  j_eq : ∀ z, EV.j z = NegSobolev.embed m z
  dual : IsDualOn (S.dynM M N) (S.ρ N) m S.T EV.VE
  adjoint : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → MemSobolev m φ →
    (∃ f, IsClassicalAdjointSolution (S.dynM M N) (S.ρ N) t φ f) ∧
      MemSobolev m (propagator (S.dynM M N) (S.ρ N) r t φ) ∧
      sobolevNorm m (propagator (S.dynM M N) (S.ρ N) r t φ) ≤ K * sobolevNorm m φ

/-! ### Small items (PROVED) -/

/-- PROVED.  A (collision-free) strong solution spends no time at contacts: `NullContactOccupation` is the vacuous
`volume ∅ = 0`.  This is the hypothesis `hocc` of `HRS.duality_identity_all`
(`IsStrongSolution.toContact` gives the other hypothesis `IsContactStrongSolution`). -/
theorem nullContactOccupation_of_strong {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : IsStrongSolution P D T X₀ W X) : NullContactOccupation P T X := by
  filter_upwards [h.no_collision] with ω hω
  have : {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ω ∈ collisionSet d N} = ∅ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hs
    exact hω (Real.toNNReal s) (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  rw [this]
  exact measure_empty

open Classical in
/-- Helper (PROVED): the `dite` defining `toPath`/`windowPath`/`flucPath` only depends on the underlying function. -/
theorem dite_continuousMap_congr {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f g : X → E) (hfg : f = g) :
    (if h : Continuous f then (⟨f, h⟩ : C(X, E)) else 0) = (if h : Continuous g then ⟨g, h⟩ else 0) := by
  subst hfg
  rfl

/-- PROVED.  `flucPath` is the path version `windowPath 0 T` of the `E_m`-valued process `flucProc`: both are the same
`dite` on the continuity of the path.  The type ascription is the defeq
`PathSp T (NegSobolev d m) = PathSpace d m T = C(Icc 0 T, E_m)`, used at default transparency by `exact`. -/
theorem flucPath_eq_windowPath {Ω : Type*} {N : ℕ} (m T σ : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ : ℝ → Torus d → ℝ) (ω : Ω) :
    flucPath m T σ X ρ ω = (windowPath 0 T (flucProc m σ X ρ) ω : PathSpace d m T) := by
  unfold flucPath windowPath
  exact dite_continuousMap_congr _ _ (funext fun t => by simp [flucProc])

/-- PROVED.  Same for `toPath` (used for the linear solution `Y_N`). -/
theorem toPath_eq_windowPath {Ω : Type*} (m T : ℝ) (Y : ℝ → Ω → NegSobolev d m) (ω : Ω) :
    toPath m T Y ω = (windowPath 0 T Y ω : PathSpace d m T) := by
  unfold toPath windowPath
  exact dite_continuousMap_congr _ _ (funext fun t => by simp)

/-! ### GF-EV: the evolution inputs -/

/-- **GF-EV-GRAD** (gradient clause; TeX M L2026-2045 (Lemma 3.17, dissipative alternative), L2070-2076 (Lemma 3.18),
L2034-2042 (Galerkin), and the use at L2445-2455).  SORRIED.  Estimated size: XL (3-5 files).

For gradient dynamics (`M = -I`), `inf ρ ≥ c > 0`, `β_N⁻¹ ≤ B_β`, regularity `γ+2d+12`: there is `K`, depending only on `b`,
such that for every setup `S` within `b` and every `N` the dual evolution on `E_γ` exists as `EvolData E_γ E_γ` in the
`Dissipative` alternative of `MaxHyp T K`, with the pairing identity and the adjoint bound `GFEvo` at `m = γ`.

Ingredients: (i) `HRS.Uniform.gradient_energy` (Lemma 3.18, proved, uniform in `ν ∈ [0, ν_max]`; hypothesis `θ ≤ 1 ∨ ρ ≥ m₀`
is the positive density `b.c`) gives `2⟨z, A_r z⟩ ≤ K ‖z‖²` on the core of trigonometric polynomials; (ii) the classical
adjoint solutions and the bound `‖U^{r,t}‖_{H^γ→H^γ} ≤ K` from `adjoint_torus` in the regimes R1 (`s ≤ d-2`) / R2b
(`ρ ≥ c`), both uniform in `β ≥ 0` (NOTE `Q54.evolution_estimates_proof` is at fixed `β > 0` through `ν₀ > 0` and cannot be
used); (iii) strong continuity of `V` on `E_γ`, cocycle, `j` isometric isomorphism (`embed γ = id`), forward equation on an
invariant core and the Galerkin conjunct of `EvolData.Dissipative`.  `K` is independent of `N`, of `C₀` and of `β_N`. -/
theorem gf_ev_grad (b : GeneralBounds d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHyp →
      S.PosDensityWith b.c → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d (S.γ : ℝ)),
        GFEvo S (-1) N (S.γ : ℝ) K EV := by
  sorry

/-- **GF-EV-MAT** (matrix clause; TeX M L609-619 (`H:eq:matrix-adjoint-input`), L2026-2033 (Lemma 3.17, two levels),
L3294-3310).  SORRIED.  Estimated size: L (1-2 files).

For a constant `M` and the adjoint input `AdjointInput M K₀`, there is `K` (depending on `b, M, K₀` only) such that for
every setup `S` within `b` and every `N` the dual evolution is an `EvolData E_γ E_{γ+2}` in the `TwoLevel` alternative of
`MaxHyp T K` with `GFEvo` at `m = γ+2`.  The bounds of `TwoLevel` are exactly the three terms of `AdjointInput` dualised
(`‖V_H‖ = ‖U‖_{γ→γ}`, `‖V_E‖ = ‖U‖_{γ+2→γ+2}`, `‖A_r‖_{E_γ→E_{γ+2}} = ‖𝓛_r‖_{H^{γ+2}→H^γ}`, `‖embed‖ ≤ 1`); what the bounds
do NOT give is `IsEvolution`: the cocycle (`classical_adjoint_unique`), strong continuity of `V` on `E_γ` (needs
`𝓛_r^* e_k ∈ E_γ` from the explicit structure of `forwardGen` with smooth coefficients) and the derivative identity in
`E_{γ+2}`.  The repaired `AdjointInput` (ISSUES "ADJIN") supplies the uniqueness of classical adjoint solutions (cocycle) and the
`MemSobolev` clauses; strong continuity on `E_γ` is no longer required (`IsEvolution.cont_H` was deleted 2026-10-17, ISSUES GFEV-MAT:
it is derived in the dissipative branch, `EvolData.Dissipative.cont_VH`); existence at level `γ+2` comes from the `γ` clause via `H^{γ+2} ⊂ H^γ`.  `hM : Sym M ≤ 0` is carried along although not used by the abstract bounds. -/
theorem gf_ev_mat (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (hM : Torus.SymNonpos M) (K₀ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHypM M →
      S.AdjointInput M K₀ → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d ((S.γ : ℝ) + 2)),
        GFEvo S M N ((S.γ : ℝ) + 2) K EV := by
  sorry

/-! ### GF-CONT: continuity and measurability of the fluctuation path -/

/-- **GF-CONT-0** (measurability of the fluctuation vector).  SORRIED.  Estimated size: S-M.
For `m > d/2` the map `x ↦ ofMeasureDiff m (empirical x) μ` is (Borel) measurable on `Config d N`, indeed continuous
(`x ↦ δ_x ∈ E_m` is continuous for `m > d/2`).  Consequently `flucProc` at fixed time is `ℱ_t`-measurable when `X t` is
(`IsFilteredSolution.adapted`), in particular `Ξ⁰ = flucProc … 0` is `ℱ_0`-measurable, as `smooth_path_comparison_proof`
requires of `X₀`. -/
theorem gf_measurable_ofMeasureDiff {N : ℕ} (m : ℝ) (hm : (d : ℝ) / 2 < m) (μ : Measure (Torus d)) :
    Measurable (fun x : Config d N => NegSobolev.ofMeasureDiff m (empirical x) μ) := by
  sorry

/-- **GF-CONT** (TeX M L2447-2455 uses `Ξ ∈ C([0,T]; E_γ)`; L521-528 defines the path space).  SORRIED.  Estimated size: M.
Under the mean-field hypotheses (`ρ_N` weakly continuous, `C^{γ+2d+12}` bounded) and for a strong solution (continuous
adapted paths), at any level `m` with `γ ≤ m`: almost surely `t ↦ Ξ^t ∈ E_m` is continuous on `[0,T]` (so `flucPath` is
not the junk path `0`), and `flucPath` is a.e.-measurable (the law is a genuine push-forward).
Proof route: `x ↦ δ_x ∈ E_m` is continuous for `m > d/2`; `t ↦ ρ_t` is norm-continuous in `E_m` by weak continuity
(`IsMeanFieldSolution.weak`, cf. `Q54c.weak_continuity`) plus the uniform `C^{γ+2d+12}` bounds (Arzelà–Ascoli);
a.e.-measurability: `windowPath` is a.e. equal to the measurable limit of piecewise-linear interpolants. -/
theorem gf_fluc_continuous (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (m : ℝ) (hm : (S.γ : ℝ) ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X) (σ : ℝ) :
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m σ X (S.ρ N) t ω) ∧
      AEMeasurable (flucPath m S.T σ X (S.ρ N)) P := by
  sorry

end HRS.GF
