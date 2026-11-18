import HRS.PDE.TorusFPSpec
import HRS.Appendix.B15CAux2
import HRS.Stochastic.Ito
import HRS.Stochastic.SelectedLawFKE

/-!
# Packet D2 (specification): Itô duality for the regularised SDE of Proposition B.15

TeX: manuscript M (`source/handoff/sources/HRS_periodic_main_20261008T010000Z.tex`), Proposition B.15,
Step 2 (L12167-12180): "the law of the smooth gradient SDE `dX^ε = -∇U^ε(X^ε) dt + √(2κ) dW` solves the
Fokker–Planck equation `∂_t u = κ Δu + div(u ∇U^ε)` on `𝕋^{N d}`".  Plan entry "2026-10-16 plan for the M
external cluster" (`docs/PROOF_QUEUE.md`), packet D2; ISSUES entries "D1", "B15-C".

## What D2 provides to D3 / E

1. `d1_ito_pathwise` / `d1_ito_expectation` (SPEC): time-dependent Itô for `f(s, Y_s)` along a strong
   solution of the additive-noise SDE with continuous periodic drift `bC ∘ mk`, with mean-zero martingale
   term, on the covering space `(ℝ^d)^N`.
2. `d1_itoGen_eq_configGen` (SPEC, bridging): the Itô drift of `d1_cl (Φ_s ∘ e⁻¹)` is
   `Φt_s + d1_configGen κ bC Φ_s` evaluated at `mk Y` (uses `d1_isC12On_of_isC12Test`).
3. `d1_lawOf_narrow` (proved), `d1_law_eqT` (SPEC), `d1_law_isConfigWeakSolution` (proved from the two):
   `t ↦ Law(mk ∘ Y_t)` is a `D1ConfigWeakSolution κ bC T`.
4. `b15d_*`: specialisation to the regularised SDE of packet C (drift identification
   `b15d_pushField_eq_gradDrift` proved; smoothness / continuity SPEC) and the identification theorem
   `b15d_law_eq_fp` (proved from the above and `d1_config_law_eq`).

## Representation decisions

* The process stays on the covering space `Y : ℝ → Ω → (Fin N → Euc d)` of `IsAdditiveSDESolution`
  (exactly what `b15c_exists_regularised_solution` produces); laws are `d1_lawOf P Y t = P.map (mk ∘ Y t)`
  on `Config d N`, and are mapped to `Torus (N*d)` by `d1_configEquiv` only in the final statements.
* Drift is a continuous `bC : Config d N → Fin N → Euc d` lifted by `d1_liftDrift`; the regularised drift is
  `b15d_configDriftReg D M` (`b15d_liftedDriftReg_eq`, `rfl`).  Noise `d1_noise d N κ = liftedNoise D`
  when `D.invβ = κ` (`d1_noise_eq`, `rfl`).
* SMOOTHNESS: `U^ε` is `C^n` iff `V ∈ C^n` (`b15c_potentialReg_contDiff`).  D1 needs `Torus.IsSmooth U`, so
  the identification theorem `b15d_law_eq_fp` assumes `Torus.IsSmooth D.V`; packet E mollifies `V_δ → V`
  in `C²` (ISSUES "B15-C").  The Itô part (1)-(3) needs only continuity of the drift.
* Test functions are exactly the `IsC12Test` class of `D1ConfigWeakSolution.eqT`; time-dependent so that
  `d1_config_law_eq` (uniqueness by duality) applies without change.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

section D2

variable {d N : ℕ}

/-! ### Definitions -/

/-- Noise coefficients `σ_{(i,j)} = √(2κ) e_{(i,j)}` of `dY = b dt + √(2κ) dW` on `(ℝ^d)^N`
(`liftedNoise D` with `κ = D.invβ`). -/
def d1_noise (d N : ℕ) (κ : ℝ) : Fin N × Fin d → Fin N → Euc d :=
  fun ij => Real.sqrt (2 * κ) • Pi.single ij.1 (EuclideanSpace.single ij.2 1)

theorem d1_noise_eq (D : DynData d) : d1_noise d N D.invβ = liftedNoise D := rfl

/-- The configuration drift `bC` lifted to the covering space: `Y ↦ bC (mk ∘ Y)`. -/
def d1_liftDrift (bC : Config d N → Fin N → Euc d) : (Fin N → Euc d) → Fin N → Euc d :=
  fun Y => bC fun i => Torus.mk (Y i)

/-- Law of the torus projection of the lifted path at time `t`: `Law(X_t)`, `X_t = mk ∘ Y_t`
(for `t ≥ 0`, `= selectedLaw P (b15c_regProcess Y) t`, `d1_lawOf_eq_regProcess`). -/
def d1_lawOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℝ → Ω → Fin N → Euc d) :
    ℝ → Measure (Config d N) :=
  fun t => P.map fun ω i => Torus.mk (Y t ω i)

theorem d1_lawOf_eq_regProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℝ → Ω → Fin N → Euc d) (t : ℝ≥0) :
    d1_lawOf P Y (t : ℝ) = P.map (b15c_regProcess Y t) := rfl

/-- The Itô drift (generator) of the lifted SDE applied to a space-time function `f` on `[0,T]`:
`∂_s f + D f[b] + ½ ∑_k D² f[σ_k, σ_k] = ∂_s f + D f[b] + κ ∑_k D² f[e_k, e_k]`
(shape of `itoDrift`, `HRS/Stochastic/Ito.lean`). -/
def d1_itoGen (κ : ℝ) (bC : Config d N → Fin N → Euc d) (T : ℝ) (f : ℝ → (Fin N → Euc d) → ℝ)
    (s : ℝ) (y : Fin N → Euc d) : ℝ :=
  derivWithin (fun r => f r y) (Set.Icc 0 T) s + fderiv ℝ (f s) y (d1_liftDrift bC y) +
    (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) y (d1_noise d N κ k) (d1_noise d N κ k)

/-! ### (1) Itô duality along a strong solution (SPEC) -/

/-- **SPEC (sorried, D2 core).** Time-dependent Itô formula with mean-zero martingale term (TeX M
L12167-12172, via `B:eq:ito-step`; repo: `ito_formula_additive`).  `Y` is a global strong solution
(`IsAdditiveSDESolution`, `τ = ⊤`) of `dY = bC(mk Y) dt + √(2κ) dW'`, `f ∈ C^{1,2}([0,T] × (ℝ^d)^N)`
with bounded `f, ∂_s f, Df, D²f` on `[0,T] × E` (automatic for `f = d1_cl (Φ_s ∘ e⁻¹)`, periodic:
`bounded_of_periodic`).  Then a.s. for all `t ∈ [0,T]`
`f(t,Y_t) = f(0,Y_0) + ∫_0^t d1_itoGen(s, Y_s) ds + M_t` with `M_t` integrable and `E[M_t] = 0`.
NOTE (statement review 2026-10-16): `M` is quantified per `t`, so this is the Dynkin form with an integrable
mean-zero remainder, equivalent to `d1_ito_expectation`; it is NOT a martingale statement (D3/E need only the
expectation form).  The intended proof takes `M_t = localItoIntegral …` (bounded progressive integrand `k ↦ Df(s,Y_s)[σ_k]`,
`q09b_stopped_mean`/`integral_itoIntegral`).  Size M (~120 lines: convert `ℝ≥0`/`ℝ` time as in
`itoIntegrand_eq_fkeRef`, progressive measurability of `bC ∘ mk ∘ Y`, `IsProgressiveL2`). -/
theorem d1_ito_pathwise {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → (Fin N → Euc d) → ℝ} (hf : IsC12On T Set.univ f)
    (hbd : ∃ C : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ y, |f s y| ≤ C ∧ ‖fderiv ℝ (f s) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (f s)) y‖ ≤ C ∧ |derivWithin (fun r => f r y) (Set.Icc 0 T) s| ≤ C) :
    ∀ t ∈ Set.Icc 0 T, ∃ M : Ω → ℝ, Integrable M P ∧ ∫ ω, M ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, f t (Y t ω) = f 0 (Y 0 ω) +
        (∫ s in Set.Icc (0 : ℝ) t, d1_itoGen κ bC T f s (Y s ω)) + M ω := by
  sorry

/-- **SPEC (sorried, D2 core, expectation form).** Dynkin form of `d1_ito_pathwise`:
`E f(t,Y_t) = E f(0,Y_0) + ∫_0^t E[d1_itoGen(s,Y_s)] ds`, `t ∈ [0,T]`.  Follows from `d1_ito_pathwise`,
the bound `hbd` (so `d1_itoGen ∘ Y` is bounded, continuous in `(s,ω)`) and Fubini.  Size S–M
(~50 lines: joint measurability of `(s,ω) ↦ d1_itoGen κ bC T f s (Y s ω)`; `integral_integral_swap`). -/
theorem d1_ito_expectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → (Fin N → Euc d) → ℝ} (hf : IsC12On T Set.univ f)
    (hbd : ∃ C : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ y, |f s y| ≤ C ∧ ‖fderiv ℝ (f s) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (f s)) y‖ ≤ C ∧ |derivWithin (fun r => f r y) (Set.Icc 0 T) s| ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∫ ω, f t (Y t ω) ∂P = ∫ ω, f 0 (Y 0 ω) ∂P +
      ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, d1_itoGen κ bC T f s (Y s ω) ∂P := by
  sorry

/-! ### (3a) Bridge: Itô drift of the transported test function is `Φt + d1_configGen` (SPEC) -/

/-- **SPEC (sorried, bridge).**  For `IsC12Test τ (Φ_r ∘ e⁻¹) (Φt_r ∘ e⁻¹)` (`0 < τ`), `f_r := d1_cl (Φ_r ∘ e⁻¹)`
(`= configLift Φ r`, `d1_configLift_comp`) and `s ∈ [0,τ]`:
`d1_itoGen κ bC τ f s Y = Φt_s (mk Y) + d1_configGen κ bC (Φ_s) (mk Y)`.
Ingredients: time derivative from `d1_isC12On_of_isC12Test`; `½ ∑_k D²f[σ_k,σ_k] = κ ∑_k D²f[e_k,e_k]`
(`σ_k = √(2κ) e_k`, bilinearity, `Real.sq_sqrt`); `fderiv_configLift_eq_of_mk` to move `D f` from `Y` to
`rep ∘ mk Y` (as `d1_configGen` evaluates at `rep ∘ X`).  Size S–M (~50 lines). -/
theorem d1_itoGen_eq_configGen {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d} {τ : ℝ}
    (hτ : 0 < τ) {Φ Φt : ℝ → Config d N → ℝ}
    (hΦ : IsC12Test τ (fun r => Φ r ∘ (d1_configEquiv d N).symm)
      (fun r => Φt r ∘ (d1_configEquiv d N).symm))
    {s : ℝ} (hs : s ∈ Set.Icc 0 τ) (Y : Fin N → Euc d) :
    d1_itoGen κ bC τ (fun r => d1_cl (Φ r ∘ (d1_configEquiv d N).symm)) s Y =
      Φt s (fun i => Torus.mk (Y i)) + d1_configGen κ bC (Φ s) (fun i => Torus.mk (Y i)) := by
  sorry

/-! ### (2) The law is a `D1ConfigWeakSolution` -/

theorem d1_measurable_proj {Ω : Type*} [MeasurableSpace Ω] {f : Ω → Fin N → Euc d}
    (hm : Measurable f) : Measurable fun ω i => Torus.mk (f ω i) :=
  measurable_pi_iff.2 fun i =>
    Torus.continuous_mk.measurable.comp ((measurable_pi_apply i).comp hm)

/-- The law of `mk ∘ Y_t` is a probability measure for `t ≥ 0` (proved). -/
theorem d1_lawOf_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ℝ → Ω → Fin N → Euc d} {t : ℝ} (hm : Measurable (Y t)) :
    IsProbabilityMeasure (d1_lawOf P Y t) := by
  exact ⟨by
    show (P.map fun ω i => Torus.mk (Y t ω i)) Set.univ = 1
    rw [Measure.map_apply (d1_measurable_proj hm) MeasurableSet.univ]; simp⟩

/-- **Narrow continuity** of `t ↦ Law(mk ∘ Y_t)` on `[0,T]` from path continuity (proved, dominated
convergence; `Config d N` is compact so continuous `ψ` is bounded). -/
theorem d1_lawOf_narrow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℝ → Ω → Fin N → Euc d} {T : ℝ} (hm : ∀ t, 0 ≤ t → Measurable (Y t))
    (hc : ∀ ω, ContinuousOn (fun s => Y s ω) (Set.Icc 0 T)) (ψ : Config d N → ℝ)
    (hψ : Continuous ψ) :
    ContinuousOn (fun t => ∫ X, ψ X ∂(d1_lawOf P Y t)) (Set.Icc 0 T) := by
  have hmeas : ∀ t, 0 ≤ t → Measurable fun ω i => Torus.mk (Y t ω i) := fun t ht =>
    d1_measurable_proj (hm t ht)
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hψ.continuousOn
  have hcongr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ X, ψ X ∂(d1_lawOf P Y t) =
      ∫ ω, ψ (fun i => Torus.mk (Y t ω i)) ∂P := fun t ht =>
    integral_map (hmeas t ht.1).aemeasurable hψ.aestronglyMeasurable
  refine ContinuousOn.congr ?_ hcongr
  refine continuousOn_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const _) ?_
  · intro t ht
    exact (hψ.measurable.comp (hmeas t ht.1)).aestronglyMeasurable
  · intro t _
    exact Eventually.of_forall fun ω => hC _ (Set.mem_univ _)
  · refine Eventually.of_forall fun ω => ?_
    refine hψ.comp_continuousOn ?_
    refine continuousOn_pi.2 fun i => Torus.continuous_mk.comp_continuousOn ?_
    exact (continuousOn_pi.1 (hc ω)) i

/-- **SPEC (sorried).** The `eqT` identity of `D1ConfigWeakSolution` for `ν = d1_lawOf P Y`
(TeX M L12167-12172: apply Itô to `Φ(s, X^ε_s)` and take expectations).  Proof: `f_r = d1_cl (Φ_r ∘ e⁻¹)`
is `IsC12On τ univ` by `d1_isC12On_of_isC12Test`; bounded with bounded derivatives by periodicity
(`bounded_of_periodic`, using `IsC12Test.cont_c2` on the compact fundamental domain); apply
`d1_ito_expectation` with `T := τ` and rewrite the drift by `d1_itoGen_eq_configGen` and `integral_map`
(`d1_lawOf` is a push-forward).  Case `τ = 0` is trivial.  Size S (~40 lines of assembly). -/
theorem d1_law_eqT {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (τ : ℝ) (hτ : τ ∈ Set.Icc 0 T) (Φ Φt : ℝ → Config d N → ℝ)
    (hΦ : IsC12Test τ (fun r => Φ r ∘ (d1_configEquiv d N).symm)
      (fun r => Φt r ∘ (d1_configEquiv d N).symm)) :
    ∫ X, Φ τ X ∂(d1_lawOf P Y τ) = ∫ X, Φ 0 X ∂(d1_lawOf P Y 0) +
      ∫ s in Set.Icc 0 τ, ∫ X, (Φt s X + d1_configGen κ bC (Φ s) X) ∂(d1_lawOf P Y s) := by
  sorry

/-- **Identification, configuration-space form** (proved from `d1_lawOf_narrow`, `d1_law_eqT`):
`t ↦ Law(mk ∘ Y_t)` is a `D1ConfigWeakSolution κ bC T` for a strong solution `Y` of
`dY = bC(mk Y) dt + √(2κ) dW'` (`bC` continuous on the lift, `κ ≥ 0`, `T ≥ 0`). -/
theorem d1_law_isConfigWeakSolution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    (T : ℝ) :
    D1ConfigWeakSolution κ bC T (d1_lawOf P Y) where
  finite t ht :=
    haveI := d1_lawOf_isProbabilityMeasure (P := P) (Y := Y)
      ((hY.adapted t).mono (ℱ.le t) le_rfl)
    inferInstance
  narrow ψ hψ :=
    d1_lawOf_narrow (fun t _ => (hY.adapted t).mono (ℱ.le t) le_rfl)
      (fun ω => by
        by_cases hT : 0 ≤ T
        · exact hY.cont ω T hT (WithTop.coe_lt_top _)
        · simp [Set.Icc_eq_empty (not_le.2 (not_le.1 hT))]) _ hψ
  eqT τ hτ Φ Φt hΦ := d1_law_eqT hW' hκ hbC hY₀ hY τ hτ Φ Φt hΦ

/-! ### (3) Specialisation to the regularised SDE of packet C -/

/-- Configuration-space form of the regularised drift `b15c_liftedDriftReg D M`:
`b_i(X) = N⁻¹ ∑_{j≠i} M ∇g_M(X_i - X_j) - ∇V(X_i)`. -/
def b15d_configDriftReg (D : DynData d) (M : ℝ) : Config d N → Fin N → Euc d :=
  fun X i => (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
      Torus.matVec D.M (Torus.grad (b15c_gReg d D.s M) (X i - X j)) - Torus.grad D.V (X i)

theorem b15d_liftedDriftReg_eq (D : DynData d) (M : ℝ) :
    (b15c_liftedDriftReg D M : (Fin N → Euc d) → Fin N → Euc d) =
      d1_liftDrift (b15d_configDriftReg D M) := rfl

/-- The regularised potential `U^ε` on the big torus `𝕋^{N d}` (through the adapter). -/
def b15d_U (D : DynData d) (M : ℝ) : Torus (N * d) → ℝ :=
  fun x => b15c_potentialReg D M ((d1_configEquiv d N).symm x)

theorem b15d_cl_U (D : DynData d) (M : ℝ) :
    d1_cl (b15d_U (N := N) D M) =
      fun Y : Fin N → Euc d => b15c_potentialReg D M (fun i => Torus.mk (Y i)) := by
  funext Y
  simp [d1_cl, b15d_U]

/-- `U^ε` is smooth on `𝕋^{N d}` when `V` is (D1 needs `Torus.IsSmooth U`; `V ∈ C²` alone is not enough,
packet E mollifies). -/
theorem b15d_U_isSmooth (D : DynData d) (hV : Torus.IsSmooth D.V) (M : ℝ) :
    Torus.IsSmooth (b15d_U (N := N) D M) := by
  sorry

/-- **Drift identification `hb`** of `d1_config_law_eq`, abstract form (proved): if the derivative of the
lift of `U` is `-⟨bC, ·⟩`, then the transported drift is `-∇U`. -/
theorem d1_pushField_eq_gradDrift_of_fderiv {bC : Config d N → Fin N → Euc d}
    {U : Torus (N * d) → ℝ}
    (h : ∀ (X : Config d N) (v : Fin N → Euc d),
      fderiv ℝ (d1_cl U) (fun i => Torus.rep (X i)) v = -∑ i, inner ℝ (bC X i) (v i)) :
    ∀ x, d1_pushField bC x = d1_gradDrift U x := by
  intro x
  obtain ⟨X, rfl⟩ := (d1_configEquiv d N).surjective x
  refine ext_inner_right ℝ fun w => ?_
  obtain ⟨v, rfl⟩ := (d1_eucEquiv d N).surjective w
  have h1 : d1_pushField bC (d1_configEquiv d N X) = d1_eucEquiv d N (bC X) := by
    simp [d1_pushField]
  rw [h1, d1_inner_eucEquiv]
  have h2 := d1_fderiv_cl_eq_inner U X v
  rw [h X v] at h2
  simp only [d1_gradDrift, inner_neg_left]
  linarith

/-- **Drift identification for the regularised SDE** (proved from `b15c_fderiv_potentialReg_proof`,
which needs the antisymmetric interaction `M = -1`): `d1_pushField (b15d_configDriftReg D M) = -∇U^ε`. -/
theorem b15d_pushField_eq_gradDrift (D : DynData d)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    ∀ x, d1_pushField (b15d_configDriftReg (N := N) D M) x = d1_gradDrift (b15d_U D M) x := by
  refine d1_pushField_eq_gradDrift_of_fderiv fun X v => ?_
  rw [b15d_cl_U, b15c_fderiv_potentialReg_proof D hM hV M]
  have hmk : (fun i => Torus.mk (Torus.rep (X i))) = X := funext fun i => Torus.mk_rep (X i)
  simp only [b15d_configDriftReg, b15c_liftedDriftReg, b15c_liftedDriftOf, Torus.mk_rep]

/-- The regularised drift is continuous on the covering space (from the Lipschitz property
`b15c_liftedDriftReg_isLipschitz`, packet C). -/
theorem b15d_liftedDriftReg_continuous (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    Continuous (d1_liftDrift (b15d_configDriftReg (N := N) D M)) := by
  sorry

/-- **Identification theorem (SPEC-complete modulo the sorried pieces above).**  Let `V` be smooth,
`M = -1` (gradient structure), `κ = D.invβ > 0`, `N d ≥ 1`, `Y` a global strong solution of the
regularised SDE `dY = b^M(Y) dt + √(2κ) dW'` (e.g. from `b15c_exists_regularised_solution`), and `μ` a
`D1WeakSolution` for `-∇U^ε` on `𝕋^{N d}` with `μ 0 = Law(e(X^ε_0))` (e.g. from `d1_fp_exists`).  Then
for all `t ∈ [0,T]`, `Law(e(X^ε_t)) = μ t`; in particular `Law(X^ε_t)` inherits the smoothness,
comparison and entropy statements of D1 (`d1_fp_smooth`, `d1_fp_comparison`, `d1_fp_entropy`). -/
theorem b15d_law_eq_fp (hNd : 1 ≤ N * d) (D : DynData d) {κ : ℝ} (hκ : 0 < κ) (hDκ : D.invβ = κ)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hV : Torus.IsSmooth D.V) (M : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} {μ : ℝ → Measure (Torus (N * d))}
    (hμ : D1WeakSolution κ (d1_gradDrift (b15d_U D M)) T μ)
    (h0 : μ 0 = (d1_lawOf P Y 0).map (d1_configEquiv d N)) :
    ∀ t ∈ Set.Icc 0 T, (d1_lawOf P Y t).map (d1_configEquiv d N) = μ t := by
  have hV2 : Torus.IsCk 2 D.V := (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift D.V) from hV).of_le (by first | exact WithTop.coe_le_coe.2 le_top | (norm_cast; exact le_top) | simp)
  have hY' : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift (b15d_configDriftReg D M))
      (d1_noise d N κ) Y₀ (fun _ => ⊤) Y := by
    rw [← b15d_liftedDriftReg_eq, ← hDκ]; exact hY
  have hν := d1_law_isConfigWeakSolution hW' hκ.le (b15d_liftedDriftReg_continuous D hV2 M) hY₀ hY' T
  exact d1_config_law_eq hNd hκ (b15d_U_isSmooth D hV M) (b15d_pushField_eq_gradDrift D hM hV2 M)
    hν hμ h0

end D2

end HRS
