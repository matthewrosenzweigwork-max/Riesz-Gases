import HRS.Appendix.CepaFlow

/-!
# Packet B15-A0: statement of the strong branch of B.15, the dispatcher and the cheap bridges

Sources: `HRS_periodic_main_20261008T010000Z.tex`, Proposition B.15 (`M:B:prop:sde-entropy-law`,
L12140-12152) and its proof (L12153-12235); plan entry "2026-10-16 plan for the M external cluster"
in `docs/PROOF_QUEUE.md`.

Contents.
* `b15_fisherInfoGen`: `fisherInfo` with the potential as an argument (`fisherInfo` is the special case
  `U = totalPotential D`, `b15_fisherInfo_eq_gen`, by `rfl`);
* `b15_sde_entropy_law_free`: the statement (sorry) of Proposition B.15 for the collision-free strong
  solution branch of `SelectedFlow`; the target of the later packets;
* `b15_sde_entropy_law_of_free`: the dispatcher, `sde_entropy_law`'s conclusion from the free statement
  (strong branch) and `cepa_entropy_confined` (Cépa-Lépingle branch);
* bridges: the FKE conjunct (`b15_solvesSelectedFKE`), null collision set of the selected law
  (`b15_selectedLaw_collisionSet`), and `gibbsRef = canonicalGibbs` (`b15_gibbsRef_eq_canonicalGibbs`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### (2) Fisher information with a general potential -/

/-- `fisherInfo` with the potential `U` and the inverse temperature factor `invβ` (`β = invβ⁻¹`) as
arguments instead of `totalPotential D`, `D.invβ`: the same variational formula
`B:eq:selected-fisher-variational` (TeX M L12205-12209),
`sup_ζ ∫ (-2 Div ζ + 2 β DU[ζ] - |ζ|²) dP` over `ζ ∈ C_c^∞(Ω_N; ℝ^{dN})`, with `DU[ζ]` computed by
differentiating the lift of `U`.  It allows a regularised potential `U_ε` (B.15, Step 2).
`fisherInfo D N P = b15_fisherInfoGen D.invβ (totalPotential D) P` is `b15_fisherInfo_eq_gen`. -/
def b15_fisherInfoGen (invβ : ℝ) (U : Config d N → ℝ) (P : Measure (Config d N)) : ℝ≥0∞ :=
  ⨆ (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ),
    ENNReal.ofReal (∫ X : Config d N,
      (-2 * configDiv ζ X
        + 2 * invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i)))
            (fun i => Torus.rep (X i)) (ζ X)
        - ∑ i, ‖ζ X i‖ ^ 2) ∂P)

/-- `fisherInfo` is `b15_fisherInfoGen` at the total potential. -/
theorem b15_fisherInfo_eq_gen (D : DynData d) (N : ℕ) (P : Measure (Config d N)) :
    fisherInfo D N P = b15_fisherInfoGen D.invβ (totalPotential D) P := rfl

/-! ### (1) The conclusion of B.15 and the collision-free (strong) branch -/

/-- The conclusion of Proposition B.15 (`M:B:prop:sde-entropy-law`, TeX M L12140-12152), literally the
conclusion of `sde_entropy_law` (CepaFlow.lean): for every deterministic `t ∈ [0,T]` the time marginal
`P_N^t` has a density, the Gibbs entropy inequality `B:eq:selected-gradient-entropy`
`𝓗_G(P_N^t) + β_N⁻¹ ∫_0^t 𝓘_G(P_N^r) dr ≤ 𝓗_G(P_N^0)` holds in `EReal` (`gibbsEntropy`, `fisherInfo`,
`β_N⁻¹ = invβ`, the time integral a `lintegral` over `Icc 0 t`), and the family solves the selected-law
forward equation of B.3 (`SolvesSelectedFKE`, distributional on `Ω_N`).  A named `Prop` so that the
free statement, the CL statement and the dispatcher share one text. -/
def b15_EntropyLawConcl {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (T : ℝ)
    (X : ℝ≥0 → Ω → Config d N) : Prop :=
  (∀ t ∈ Set.Icc 0 T, HasSelectedDensity P X t ∧
    gibbsEntropy D (selectedLaw P X t)
      + ((ENNReal.ofReal D.invβ *
          ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
      ≤ gibbsEntropy D (selectedLaw P X 0)) ∧
  SolvesSelectedFKE D T (selectedLaw P X)

/-- Proposition B.15 (`M:B:prop:sde-entropy-law`, TeX M L12140-12152; proof L12153-12235), the
collision-free (strong-solution) branch only.  STATEMENT, proof open (target of the later packets
C (radial cutoff `g_ε`, `X^ε = X` eventually), B (lower semicontinuity of `klDiv` and of the Fisher
information), D (parabolic theory on `𝕋^{dN}` for the smooth coefficients, Itô duality, entropy
dissipation), E (assembly)).

Representation decisions.
* `SelectedFlow` (`flow` field) is `(IsStrongSolution ∧ PathwiseUnique) ∨ (d = 1 ∧ s = 0 ∧ … CL)`; the
  present statement is the first disjunct, with the four standing fields of `SelectedFlow`
  (`init_meas`, `init_distinct`, `brownian`, `indep`) as the explicit hypotheses `hX₀ hdist hW hind`
  (names as in `cepa_entropy_confined`), so `SelectedFlow P D T X₀ W X` is rebuilt as
  `⟨hX₀, hdist, hW, hind, Or.inl ⟨hS, hU⟩⟩`.  The FKE conjunct then follows from `selected_law_fke`
  (`b15_solvesSelectedFKE`).
* Collision-freeness of `X` is the field `IsStrongSolution.no_collision` (TeX: B:eq:particle-uniform-separation
  for the strong solution, L12163-12165, gives the a.s. positive minimal pair distance);
  `PathwiseUnique` is kept as a hypothesis because it is what the strong disjunct supplies (the TeX
  Step 1 uses *stopped* pathwise uniqueness to show `X^ε = X` on `[0,T]` for `ε` small, L12162-12166).
* All other hypotheses, and the conclusion, are exactly those of `sde_entropy_law`:
  `hN : 2 ≤ N`, `ζ_BM = -I` (`D.M = -1`), `0 < invβ` (`β_N < ∞`), `V ∈ C²`, `0 < T`, the Brownian
  filtration `hF : IsFilteredSolution`, a density at time 0 (`hdens0`), and
  `𝓗_G(P_N^0) < ⊤` (`B:eq:selected-initial-gibbs-entropy`; `gibbsEntropy` is `EReal`-valued).
* Valid for every `d`, including `d = 1` (then both branches of `SelectedFlow` can apply; B.14 covers the
  Cépa-Lépingle one).  The TeX proof states `g_ε ≥ 0` for `s > 0` (L12159; false for the mean-zero torus kernel,
  only the uniform lower bound `b15c_gReg_ge` is used, ISSUES "B15-C") and needs the `d = 1`, `0 < s < 1`
  integrability of the Gibbs weight (see `b15_periodicRiesz_ge_d1`).  It also covers strong collision-free
  solutions for `d = 1`, `s = 0`, which the TeX sends to B.14 (L12154); Step 1 does not use `g_ε ≥ 0`
  when `s = 0`, so this extra case is harmless. -/
theorem b15_sde_entropy_law_free
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hβ : 0 < D.invβ)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X) (hU : PathwiseUnique P D T X₀ W)
    (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    b15_EntropyLawConcl P D T X := by
  sorry

/-! ### (3) The dispatcher -/

/-- Dispatcher for Proposition B.15: `sde_entropy_law`'s conclusion follows from the strong-branch
statement `b15_sde_entropy_law_free` (called directly, so this theorem depends exactly on that statement
and on `cepa_entropy_confined`; statement review 2026-10-16, ISSUES "B15-A0") and from `cepa_entropy_confined` (the
Cépa-Lépingle branch, after `subst d = 1`; `M = -I` there is exactly the `hM` of the statement, so the
constant `a` of the disjunct is not needed). -/
theorem b15_sde_entropy_law_of_free
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
  rcases hX with ⟨hX₀, hdist, hW, hind, hflow⟩
  rcases hflow with ⟨hS, hU⟩ | ⟨hd1, hs0, _, _, hCL⟩
  · exact b15_sde_entropy_law_free hN hM hβ hV hT hX₀ hdist hW hind hS hU hF hdens0 hH0
  · subst hd1
    exact cepa_entropy_confined hN hs0 hβ hM hV hT hX₀ hdist hW hind hCL hF hdens0 hH0

/-! ### (4a), (4b) Cheap bridges -/

/-- The FKE conjunct of B.15 (B.3): for a selected flow, `selectedLaw` solves the forward equation of
`selected_law_fke` (the second conjunct, one line). -/
theorem b15_solvesSelectedFKE
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    SolvesSelectedFKE D T (selectedLaw P X) :=
  (selected_law_fke hN hV hT hX hF).2

/-- A collision-free strong solution has a selected law that does not charge the collision set
`𝔇_N`, at every deterministic time `t ∈ [0,T]`
(`P_N^t(𝔇_N) = 0`, from `IsStrongSolution.no_collision`). -/
theorem b15_selectedLaw_collisionSet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    selectedLaw P X t (collisionSet d N) = 0 := by
  have hcoll : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  unfold selectedLaw
  rw [Measure.map_apply (hS.adapted _) hcoll]
  have hle : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by
    rw [Real.coe_toNNReal t ht0]; exact htT
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hS.no_collision] with ω hω using hω _ hle

end HRS
