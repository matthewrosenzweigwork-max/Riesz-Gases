import HRS.MC.CepaDefs
import HRS.Appendix.CepaFlow
import HRS.Stochastic.ParticleLog

/-!
# Packet CEPA-SPEC: statement skeleton for the four Cépa–Lépingle externals of Appendix B

SPECIFICATION FILE: every theorem below is `sorry`; no proofs.  The companion plan is
`HRS/MC/CepaPlan.md` (verdicts on the four frozen statements, packets, routes, size estimates, workers, critical
path, TeX gaps).

Frozen targets (`HRS/Appendix/CepaFlow.lean`): `HRS.cepa_noncollision_iff_threshold` (B.13, TeX M L11977-11985),
`HRS.cepa_entropy_confined` (B.14, L12020-12032), `HRS.cepa_log_flow` (B.2, L11662-11670),
`HRS.selected_law_smoothing` (B.4, L11694-11702).

The definitions of this file live in `HRS/MC/CepaDefs.lean` (imported here), so that proof modules can import the
vocabulary without the `sorry` theorems.
Naming: all new objects carry the prefix `cep_`; namespace `HRS.MC.Cepa`.
Packet letters: `K` kernel/analytic facts, `U` uniqueness (B.2, 2nd half), `C` agreement with the maximal solution
(shared by B.13 and B.2/B.14), `S` sufficiency (B.13, `⇐`), `N` necessity (B.13, `⇒`), `E` existence (B.2, 1st half),
`H` entropy (B.14), `P` smoothing (B.4).
Statements flagged `SUSPECT` in their docstrings are true but their provability by the stated route is uncertain.
Statements that deliberately weaken a frozen hypothesis (fewer hypotheses than the frozen theorem) say so.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Cepa

open HRS

/-! ## Part K: kernel and deterministic analytic inputs -/

section Kernel

/-- **K1 (circular decomposition of the periodic logarithmic force)**.  On `𝕋¹` the force of the periodic
logarithmic kernel (`s = 0`) is `-π cot(π u)` plus a smooth odd 1-periodic function, for every `u ∉ ℤ`.
This is the TeX decomposition `g = g_circ + smooth`, `g_circ(r) = -log(2|sin(π r)|)` (L12041), at the level
of the force.  Inputs: `KernelD1Facts.periodicRieszGrad_local_singularity_d1` (`HRS/Kernel/D1.lean:1351`,
`s = 0`: `∇g = eucRieszGrad + r` near `0`, `r` smooth), `periodicRieszGrad_smoothOffZero_d1`
(`D1.lean:1336`), oddness `periodicRieszGrad_neg`, smoothness of `u ↦ π cot(π u) - 1/u` near `0`. -/
theorem cep_K1_force_decomp :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ (∀ u, ρ (u + 1) = ρ u) ∧ (∀ u, ρ (-u) = -ρ u) ∧
      ∀ y : Euc 1, (∀ n : ℤ, y 0 ≠ n) →
        (periodicRieszGrad 1 0 (Torus.mk y)) 0 =
          -(Real.pi * (Real.cos (Real.pi * y 0) / Real.sin (Real.pi * y 0))) + ρ (y 0) := by
  sorry

/-- **K2 (dissipativity of the ordered drift)**.  On the closed cyclic chamber (common order `π`, no contact)
the drift `Y ↦ liftedDrift D Y` is one-sided Lipschitz: `⟨y - y', b(y) - b(y')⟩ ≤ Λ |y - y'|²`.  Reason: for
`M = -a`, `a ≥ 0`, the interaction part is minus the gradient of the convex function
`(a/N) ∑_{k<l} g_circ(z_l - z_k)` on the open alcove (`g_circ'' = π² csc² > 0`, K1), the smooth correction `ρ` and
`∇V` are Lipschitz.  `N` arbitrary (for `N ≤ 1` the sum is the `∇V` term alone).  No Brownian input. -/
theorem cep_K2_drift_dissipative {N : ℕ} {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 ≤ a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V) :
    ∃ Λ : ℝ, ∀ (π : Equiv.Perm (Fin N)) (y y' : Fin N → Euc 1),
      CyclicallyOrdered π y → CyclicallyOrdered π y' →
      (fun i => Torus.mk (y i)) ∉ collisionSet 1 N → (fun i => Torus.mk (y' i)) ∉ collisionSet 1 N →
      ∑ i, inner ℝ (y i - y' i) (liftedDrift D y i - liftedDrift D y' i) ≤ Λ * ∑ i, ‖y i - y' i‖ ^ 2 := by
  sorry

/-- **K3 (Gronwall for absolutely continuous differences)**.  Deterministic: if `Z(t) = ∫_0^t F` with `F` integrable
and `⟨Z, F⟩ ≤ Λ |Z|²` a.e. on `[0,T]`, then `Z ≡ 0`.  (Route: `|Z|²` is absolutely continuous with derivative
`2⟨Z,F⟩` a.e.; integral Gronwall, `HRS/Stochastic/SDE.lean:98 eq_zero_of_integral_bound` is the template.) -/
theorem cep_K3_gronwall_ac {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Z F : ℝ → E}
    {T Λ : ℝ} (hT : 0 ≤ T) (hF : IntervalIntegrable F volume 0 T)
    (hZ : ∀ t ∈ Set.Icc 0 T, Z t = Z 0 + ∫ s in (0 : ℝ)..t, F s) (h0 : Z 0 = 0)
    (hdiss : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)), inner ℝ (Z s) (F s) ≤ Λ * ‖Z s‖ ^ 2) :
    ∀ t ∈ Set.Icc 0 T, Z t = 0 := by
  sorry

end Kernel

/-! ## Part U: uniqueness in the class `IsCepaLepingleFlow` (second half of `cepa_log_flow`) -/

section Uniqueness

/-- **U1 (continuous lifts differ by a constant lattice vector)**.  Two continuous lifts of the same torus path on
`[0,T]` differ by a time-independent element of `ℤ^{N d}` (a continuous map into a discrete set is constant). -/
theorem cep_U1_lift_const {d N : ℕ} {T : ℝ} (hT : 0 ≤ T) {Y Y' : ℝ≥0 → Fin N → Euc d}
    (hY : Continuous Y) (hY' : Continuous Y')
    (h : ∀ t : ℝ≥0, (t : ℝ) ≤ T → (fun i => Torus.mk (Y t i)) = fun i => Torus.mk (Y' t i)) :
    ∃ v : Fin N → Euc d, IsLatticeVec v ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T → Y' t = Y t + v := by
  sorry

/-- **U1b (chambers are identified by one interior point)**.  If `y` is strictly ordered by `π` and `y + v` strictly
ordered by `π'` (`v` a lattice vector), then the closed chamber `{z | CyclicallyOrdered π z}` equals the lattice
translate of the closed chamber of `π'`: `CyclicallyOrdered π' (z + v) → CyclicallyOrdered π z`.  This removes the
ambiguity of the anchor (rotation `π ↦ π ∘ rot`) in `IsCepaLepingleFlow.ordered`. -/
theorem cep_U1b_chamber_unique {N : ℕ} {π π' : Equiv.Perm (Fin N)} {y v : Fin N → Euc 1}
    (hv : IsLatticeVec v) (hy : cep_StrictlyOrdered π y) (hy' : cep_StrictlyOrdered π' (y + v)) :
    ∀ z : Fin N → Euc 1, CyclicallyOrdered π' (z + v) → CyclicallyOrdered π z := by
  sorry

/-- **U2 (pathwise uniqueness among cyclically ordered contact flows)** = the second conjunct of `cepa_log_flow`.
Hypotheses are those of the frozen statement minus the ones the argument does not use (no Brownian input: the
noise cancels exactly in the difference of the two integrated equations; `hdist` fixes the cyclic order).  Route:
`cep_U1_lift_const` (+ `cep_U1b_chamber_unique`) puts both lifts in one closed chamber with the same initial lift;
`Z = Y - Y'` is `∫ (b(Y) - b(Y'))`; a.e. time both configurations are contact-free (`occupation`), so `cep_K2` gives
`⟨Z, Z'⟩ ≤ Λ |Z|²`; `cep_K3` gives `Z = 0`; then `X = X'` by `mk`. -/
theorem cep_U2_flow_unique {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V)
    {X₀ : Ω → Config 1 N} (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {T : ℝ} {X X' : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hX' : IsCepaLepingleFlow P D T X₀ W X') :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X' t ω := by
  sorry

end Uniqueness

/-! ## Part C: agreement with the maximal collision-free solution (shared by B.13, B.2, B.14) -/

section Agreement

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- **C0 (local Lipschitz drift under `C^{1,1}` potentials)**.  `Particle.lean:2039 liftedDrift_locLipschitz`
assumes `Torus.IsCk 2 D.V`; only the local Lipschitz property of `∇V` is used (the singular pair part is smooth off
the diagonal, `hK`).  Needed because `cepa_log_flow` / `cepa_noncollision_iff_threshold` assume only
`C¹` with Lipschitz gradient. -/
theorem cep_C0_locLipschitz (D : DynData d) (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s))
    (hV : cep_IsC11 D.V) : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) := by
  sorry

/-- **C1 (a contact-allowing integrated solution coincides with the maximal solution until its first contact)**.
Pathwise uniqueness of the additive-noise ODE on the open region `liftedFree` (`ode_additive_unique`,
`HRS/Stochastic/SDE.lean:127`) applied to the two lifts after a lattice shift of the initial lift
(template: `pathwiseUnique_of_locLipschitz`, `HRS/Stochastic/Bridge.lean:329`, where both processes are
collision-free on all of `[0,T]`; here only up to `σ`).  No adaptedness of `X` is used. -/
theorem cep_C1_agree_until_contact [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z))
    {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hW : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j)
    (hW'c : ∀ ω, Continuous fun t => W' t ω)
    (hX : IsContactStrongSolution P D T X₀ W X)
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (hY₀ : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω) :
    ∀ᵐ ω ∂P, ∀ σ : WithTop ℝ, cep_NoContactBefore X ω σ → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (((t : ℝ)) : WithTop ℝ) < σ → (((t : ℝ)) : WithTop ℝ) < τ ω →
        X t ω = fun i => Torus.mk (Y (t : ℝ) ω i) := by
  sorry

/-- **C3 (collision alternative under `C^{1,1}`)**.  `IsMaximalParticleSolution.collision_alternative`
(`Particle.lean:2174`) with `cep_IsC11` in place of `Torus.IsCk 2`. -/
theorem cep_C3_collision_alternative [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (D : DynData d) (hK : KernelLocal d D.s)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    ∀ᵐ ω ∂P, τ ω < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, 0 ≤ t₀ → (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧
        ∃ i j : Fin N, i ≠ j ∧ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < ε := by
  sorry

/-- **C2 (noncollision of a contact flow on `[0,T]` is non-explosion of the maximal solution)**.  Both directions
use `cep_C1` (agreement before the first contact) and continuity of `X`; `(→)` uses the collision alternative
`hcol` (`cep_C3`) at the explosion time, `(←)` the continuity of `Y` on `[0,τ)`. -/
theorem cep_C2_noncollision_iff_nonexplosion [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z))
    {T : ℝ} (hT : 0 ≤ T) {X₀ : Ω → Config d N} (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hW : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) (hW'c : ∀ ω, Continuous fun t => W' t ω)
    (hX : IsContactStrongSolution P D T X₀ W X) (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t => X t ω i)
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (hY₀ : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω)
    (hcol : ∀ᵐ ω ∂P, τ ω < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, 0 ≤ t₀ → (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧
        ∃ i j : Fin N, i ≠ j ∧ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < ε) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet d N) ↔
      ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) < τ ω := by
  sorry

end Agreement

/-! ## Part S: sufficiency in B.13 (`N β⁻¹ ≤ a` implies noncollision) -/

section Sufficiency

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **S1 (barrier chain under `C^{1,1}`; mechanical adaptation)**.  `particle_no_collision_d1_log`
(`HRS/Stochastic/ParticleLog.lean`) for the maximal solution, with `cep_IsC11 D.V` instead of `Torus.IsCk 2 D.V`.
The hypothesis `Torus.IsCk 2` of `Particle.lean` is used only (i) for the Lipschitz constant of `∇V`
(`rem_exists_lipschitz_gradient`, L1405, used in `clusterRemainder_bound` L1766), (ii) for the local Lipschitz /
boundedness of the drift (`contDiffOn_liftedDrift` L2007, `liftedDrift_locLipschitz` L2039,
`liftedDrift_bounded_of_sep` L2131); all other theorems of the chain (`ito_along_solution` L3168,
`barrier_level_estimate`, `cluster_hitting_*`, `cluster_barrier*`, `collision_alternative`) pass `hV` along.  Worker:
copy `Particle.lean` L1400-4100 into a new module under `HRS/MC/` (namespace `HRS.MC.Cepa.C11`), change the hypothesis
and re-prove the five places above. -/
theorem cep_S1_no_explosion_log [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (D : DynData 1) (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hthr : (N : ℝ) * D.invβ ≤ a)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc 1)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) : ∀ᵐ ω ∂P, τ ω = ⊤ := by
  sorry

/-- **S2 (existence of the maximal solution under `C^{1,1}`)**: `particle_maximal` (`Particle.lean:2082`) with
`cep_C0_locLipschitz` in place of `liftedDrift_locLipschitz` (the proof is `exists_sde_solution_maximal`
applied to the local Lipschitz drift; ten lines once C0 is available). -/
theorem cep_S2_maximal_c11 [IsProbabilityMeasure P] {d : ℕ} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (D : DynData d) (hK : KernelLocal d D.s)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W') (Y₀ : Ω → (Fin N → Euc d))
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) (hY₀U : ∀ ω, Y₀ ω ∈ liftedFree d N) :
    ∃ (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → (Fin N → Euc d)), IsMaximalParticleSolution P ℱ W' D Y₀ τ Y := by
  sorry

/-- **S3 (B.13, sufficiency)**: for the flow of B.2, `N invβ ≤ a` gives a.s. noncollision on `[0,T]`.
Route: Brownian filtration from `exists_isBrownianFiltration_of_isVectorBrownian` (`Bridge.lean:75`),
`Y₀ = rep ∘ X₀`, maximal solution `S2`, `τ = ⊤` a.s. by `S1`, then `C2 (←)`. -/
theorem cep_S3_noncollision_of_threshold [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X)
    (hthr : (N : ℝ) * D.invβ ≤ a) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet 1 N := by
  sorry

end Sufficiency

/-! ## Part N: necessity in B.13 (`a < N invβ` gives contact with positive probability on every `[0,T]`) -/

section Necessity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **N1 (Brownian tube; positivity of small tube probabilities)**.  For every continuous `w` with `w 0 = 0`,
`P(sup_{t ≤ T'} |W_t - w t| < η) > 0`.  Route (no Cameron–Martin, no reflection principle): piecewise-linear
approximation of `w`; on one piece with slope `c` the process `X_t = B_t - c t` stays in `(-η,η)` with probability
`≥ exp(-(λ + c²/2) t - |c| η)`, `λ = π²/(8η²)`, by Itô for `M_t = e^{(λ+c²/2)(t∧τ)} e^{-c X} cos(π X/(2η))`
(a martingale, `M = 0` at the exit time, `E M_t = 1`; `ito_formula_additive`, `Ito.lean:3632`); independent
increments (`IsVectorBrownian`) multiply the piece probabilities; independent coordinates multiply. -/
theorem cep_N1_bm_tube [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    {w : ℝ → Fin N → Euc 1} (hw : Continuous w) (hw0 : w 0 = 0) {T' η : ℝ} (hT' : 0 < T') (hη : 0 < η) :
    0 < P {ω | ∀ t : ℝ≥0, (t : ℝ) ≤ T' → ‖W t ω - w t‖ < η} := by
  sorry

/-- **N2 (deterministic tube stability for the additive-noise ODE on `liftedFree`)**.  If `c` solves the noisy
integral equation for the noise path `v` inside the open region `liftedFree`, there is a tube radius `r` such that
for every `ε ≤ r` there is `η > 0` with: any continuous `y` solving the same equation with initial value and noise
`η`-close, and staying in `liftedFree` up to time `s ≤ T'`, stays `ε`-close to `c` on `[0,s]`.  Route: Gronwall
(`SDE.lean:98 eq_zero_of_integral_bound` pattern) with the Lipschitz constant of `liftedDrift` on the
`r`-neighbourhood of the compact `c([0,T'])` (`cep_C0_locLipschitz`, `Particle.lean:2131 liftedDrift_bounded_of_sep`),
continuity argument in `s`. -/
theorem cep_N2_tube_stability {D : DynData 1} (hs : D.s = 0) (hV : cep_IsC11 D.V)
    {T' : ℝ} (hT' : 0 < T') {c v : ℝ → Fin N → Euc 1} (hc : Continuous c) (hv : Continuous v) (hv0 : v 0 = 0)
    (hcfree : ∀ t ∈ Set.Icc 0 T', c t ∈ liftedFree 1 N)
    (hceq : ∀ t ∈ Set.Icc 0 T', c t = c 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (c u)) + v t) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∃ η : ℝ, 0 < η ∧
      ∀ (y V : ℝ → Fin N → Euc 1) (s : ℝ), 0 ≤ s → s ≤ T' → Continuous y →
        ‖y 0 - c 0‖ < η → (∀ t ∈ Set.Icc 0 s, ‖V t - v t‖ < η) →
        (∀ t ∈ Set.Icc 0 s, y t ∈ liftedFree 1 N) →
        (∀ t ∈ Set.Icc 0 s, y t = y 0 + (∫ u in (0 : ℝ)..t, liftedDrift D (y u)) + V t) →
        ∀ t ∈ Set.Icc 0 s, ‖y t - c t‖ < ε := by
  sorry

/-- **N3 (steering)**.  (Statement repaired after a worker found the counterexample `invβ = 0`, `N = 2`, `V = 0`, symmetric start: no noise, no motion; hence the hypothesis `0 < D.invβ`, which N6 has.)  From an arbitrary strictly ordered initial lift, with positive probability the maximal
solution reaches, at a time `t₁ ≤ T'`, a configuration in which the pair `(π 0, π 1)` has gap in `(0, ε/2]` and
is isolated at scale `r = 1/(8N)`, and the remaining particles are mutually `r`-separated on the circle (added after the N6 worker
found that the Kolmogorov step of N6 needs a lower bound on the mutual distances of the other particles; the tube around the target
configuration gives it uniformly in `ε`).  Route: convex combination `c(s) = (1-s) y₀ + s y*` of two strictly `π`-ordered
configurations is strictly ordered (the closed alcove is convex), hence in `liftedFree`; the noise path
`v(t) = c(t) - c(0) - ∫ b(c)` is `C⁰` (indeed `C¹`); apply `cep_N1_bm_tube` to `(W - v)/√(2 invβ)`, `cep_N2`
(deterministic stability), and the collision alternative to continue the maximal solution to `t₁`.  The initial lift
`Y₀` is arbitrary (no regularity of the law is used), so the event depends on `Y₀` only through `ε` and a
`Y₀`-dependent control; the positive lower bound is *conditional on `ℱ₀`* and is used with `A ∈ ℱ_{t₁}`. -/
theorem cep_N3_steering [IsProbabilityMeasure P] (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) (hπ0 : ∀ ω, cep_StrictlyOrdered (π ω) (Y₀ ω))
    {T' : ℝ} (hT' : 0 < T') {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ T' ∧ ∃ A : Set Ω, MeasurableSet[ℱ t₁] A ∧ 0 < P A ∧
      ∀ ω ∈ A, ((t₁ : ℝ) : WithTop ℝ) < τ ω ∧ cep_StrictlyOrdered (π ω) (Y t₁ ω) ∧
        0 < Y t₁ ω (π ω (cep_i1 hN)) 0 - Y t₁ ω (π ω (cep_i0 hN)) 0 ∧ Y t₁ ω (π ω (cep_i1 hN)) 0 - Y t₁ ω (π ω (cep_i0 hN)) 0 ≤ ε / 2 ∧
        cep_PairIsolated hN (π ω) (Y t₁ ω) (1 / (8 * (N : ℝ))) ∧
        (∀ k l : Fin N, k ≠ l → k ≠ π ω (cep_i0 hN) → k ≠ π ω (cep_i1 hN) →
          l ≠ π ω (cep_i0 hN) → l ≠ π ω (cep_i1 hN) → ∀ m : ℤ,
            1 / (8 * (N : ℝ)) ≤ |Y t₁ ω k 0 - Y t₁ ω l 0 - m|) := by
  sorry

/-- **N4 (gap dynamics while the pair is isolated)**.  Let `G = Y_{π 1} - Y_{π 0}` and `B = (W'_{π 1} - W'_{π 0})/√2`
(an `ℱ`-Brownian motion since `π` is `ℱ₀`-measurable).  There is a constant `C` (depending on `a, N, invβ, L, r`) and a
bounded adapted perturbation `c` (`|c| ≤ C`) with
`G_t - G_s = ∫_s^t ((2a/N)/G_u + c_u) du + 2√invβ (B_t - B_s)` on every interval on which the pair is `r`-isolated,
`0 < G < 1/4` and the solution exists.  `κ = 2a/N` is the coefficient of the Bessel drift; Bessel dimension
`δ = 1 + κ/(2 invβ) = 1 + a/(N invβ)`.  Route: `cep_K1_force_decomp` (`π cot(πG) - 1/G` is bounded for `G ≤ 1/4`),
the integral equation of `IsAdditiveSDESolution`, boundedness of the pair-external forces on `r`-isolated
configurations (`ρ`, `∇V`, the other `cot` terms are bounded by `C(r)`). -/
theorem cep_N4_gap_dynamics [IsProbabilityMeasure P] (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → Fin N → Euc 1} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → Fin N → Euc 1}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ}) {r : ℝ} (hr : 0 < r) :
    ∃ (C : ℝ) (c : ℝ → Ω → ℝ), 0 ≤ C ∧ (∀ u ω, |c u ω| ≤ C) ∧ (∀ u, 0 ≤ u → Measurable[ℱ u] (c u)) ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        (∀ u ∈ Set.Icc s t, ((u : ℝ) : WithTop ℝ) < τ ω ∧ cep_StrictlyOrdered (π ω) (Y u ω) ∧
          cep_PairIsolated hN (π ω) (Y u ω) r ∧
          0 < Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0 ∧ Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0 < 1 / 4) →
        (Y t ω (π ω (cep_i1 hN)) 0 - Y t ω (π ω (cep_i0 hN)) 0) - (Y s ω (π ω (cep_i1 hN)) 0 - Y s ω (π ω (cep_i0 hN)) 0) =
          (∫ u in s..t, ((2 * a / N) / (Y u ω (π ω (cep_i1 hN)) 0 - Y u ω (π ω (cep_i0 hN)) 0) + c u ω))
            + 2 * Real.sqrt D.invβ *
              (((W' (Real.toNNReal t) ω (π ω (cep_i1 hN), 0) - W' (Real.toNNReal t) ω (π ω (cep_i0 hN), 0)) -
                (W' (Real.toNNReal s) ω (π ω (cep_i1 hN), 0) - W' (Real.toNNReal s) ω (π ω (cep_i0 hN), 0))) / Real.sqrt 2) := by
  sorry

/-- **N5 (one-dimensional Bessel-type hitting estimate; the only place the threshold enters)**.  Let `G > 0`
satisfy `dG = (κ/G + c) dt + σ dB` on `[t₁, (t₁ + dur) ∧ ρ]`, `|c| ≤ C`, `κ < σ²/2` (Bessel dimension `< 2`),
`ε ≤ κ/C` (or `C = 0`).  Then for every `ℱ_{t₁}`-set `A` on which `G_{t₁} ∈ (0, ε/2]` and every `δ > 0`
`P(A ∩ {G reaches δ before time t₁+dur and before ρ}) ≥ (1 - S(ε/2)/S(ε) - ε²/(σ² dur)) P(A) - P(A ∩ {ρ < t₁+dur})`,
with `S = cep_scale (2κ/σ²) (2C/σ²)`.  Route: Itô for `S(G)` (a positive supermartingale away from `0`, since
`L S = S'·(c - C) ≤ 0`; `S` is `C²` on `[δ,∞)` and the localisation at `inf G ≤ δ` removes the singularity), optional
stopping at the exit of `(δ, ε)`, giving `P(top before bottom) ≤ S(x)/S(ε)`; the time-out bound from
`d(G²) ≥ σ² dt` below level `ε` (Itô, `E[τ ∧ dur] ≤ ε²/σ²`, Markov).  Positivity of `1 - S(ε/2)/S(ε)`: `S` is strictly
increasing; and `ε²/(σ² dur) → 0` as `ε → 0` for fixed `dur`.  `G > 0` on the interval is the contradiction
hypothesis of N6. -/
theorem cep_N5_bessel_hitting [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianFiltration P ℱ (fun t ω (_ : Fin 1) => B t ω))
    {G c : ℝ → Ω → ℝ} {κ σ C : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hκσ : κ < σ ^ 2 / 2) (hC : 0 ≤ C)
    {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime ℱ ρ) {t₁ dur : ℝ} (ht₁ : 0 ≤ t₁) (hdur : 0 < dur)
    (hG : ∀ ω, Continuous fun t => G t ω) (hGad : ∀ t, 0 ≤ t → Measurable[ℱ t] (G t))
    (hc : ∀ u ω, |c u ω| ≤ C) (hcad : ∀ u, 0 ≤ u → Measurable[ℱ u] (c u))
    (hpos : ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω → 0 < G u ω)
    (hdyn : ∀ᵐ ω ∂P, ∀ s t : ℝ, t₁ ≤ s → s ≤ t → t ≤ t₁ + dur → ((t : ℝ) : WithTop ℝ) ≤ ρ ω →
      G t ω - G s ω = (∫ u in s..t, (κ / G u ω + c u ω)) + σ * (B (Real.toNNReal t) ω - B (Real.toNNReal s) ω))
    {ε δ : ℝ} (hε : 0 < ε) (hεC : C * ε ≤ κ) (hδ : 0 < δ) (hδε : δ < ε / 2)
    {A : Set Ω} (hA : MeasurableSet[ℱ t₁] A) (hA0 : ∀ ω ∈ A, 0 < G t₁ ω ∧ G t₁ ω ≤ ε / 2) :
    (1 - cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) (ε / 2) / cep_scale (2 * κ / σ ^ 2) (2 * C / σ ^ 2) ε
        - ε ^ 2 / (σ ^ 2 * dur)) * (P A).toReal - (P (A ∩ {ω | ρ ω < ((t₁ + dur : ℝ) : WithTop ℝ)})).toReal
      ≤ (P (A ∩ {ω | ∃ u ∈ Set.Icc t₁ (t₁ + dur), ((u : ℝ) : WithTop ℝ) ≤ ρ ω ∧ G u ω ≤ δ})).toReal := by
  sorry

/-- **N5' (the scale-function ratio is `< 1`, uniformly as `ε ↓ 0`)**: for `θ < 1` and `λ ≥ 0` there are
`ε₀, q > 0` with `S(ε/2)/S(ε) ≤ 1 - q` for all `0 < ε ≤ ε₀`.  (Explicitly `S(ε/2)/S(ε) → 2^{-(1-θ)}`.)
Calculus only. -/
theorem cep_N5b_scale_ratio {θ lam : ℝ} (hθ : θ < 1) (hlam : 0 ≤ lam) :
    ∃ ε₀ q : ℝ, 0 < ε₀ ∧ 0 < q ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → cep_scale θ lam (ε / 2) / cep_scale θ lam ε ≤ 1 - q := by
  sorry

/-- **N6 (B.13, necessity)**: below the threshold, contacts occur with positive probability on `[0,T]`, for every
initial law and every `T > 0`.  Assembly: suppose a.s. noncollision on `[0,T]`; by `cep_C2` the maximal solution has
`τ > T` a.s.; choose `r = 1/(8N)`, `ε, dur` small (constants of N4, N5b; also `P(sup_{[t₁,t₁+dur]} |ΔW| > r/4) ≤
dur·N/(r/4)²` by Doob/Kolmogorov so the other particles stay `r`-away, which makes `P(A ∩ {ρ < t₁+dur})` small);
N3 gives `A` with `P A > 0`; N4+N5 give `P(A ∩ {G ≤ δ}) ≥ p·P(A) > 0` for all `δ`; but `G` is continuous and `> 0`
on the compact `[t₁, t₁+dur]`, so `P(inf G ≤ δ) → 0`: contradiction. -/
theorem cep_N6_contact_below_threshold [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X)
    (hbelow : a < (N : ℝ) * D.invβ) :
    ¬ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet 1 N := by
  sorry

end Necessity

/-! ## Part E: existence in B.2 (Moreau–Yosida regularisation in chamber coordinates) -/

section Existence

/-- **E0 (measurable sorting of the initial configuration)**: a measurable choice `π` of strictly ordered labelling
of `rep ∘ x` for `x` collision-free (sort the representatives in `[0,1)^N`). -/
theorem cep_E0_sort (N : ℕ) : ∃ π : Config 1 N → Equiv.Perm (Fin N),
    (∀ σ, MeasurableSet {x | π x = σ}) ∧
      ∀ x : Config 1 N, x ∉ collisionSet 1 N → cep_StrictlyOrdered (π x) (fun i => Torus.rep (x i)) := by
  sorry

/-- **E1 (the drift in chamber coordinates)**.  For `M = -a`, `s = 0`, the lifted drift read in the ranks of a strictly
ordered lift is `-∇Φ - ∇Ψ`, where `Ψ` is `C^{1,1}` and diagonally `ℤ`-periodic: `Ψ(z) = (a/N) ∑_{k<l} r(z_l - z_k) +
∑_k V(z_k)` with `r` the antiderivative of the smooth odd periodic remainder `ρ` of K1.  For `a = 1` the total potential
`totalPotential D` of the Gibbs weight is `Φ + Ψ` in chamber coordinates (this is what the entropy chain H needs).
The formula holds for every strictly ordered pair `(π, y)`. -/
theorem cep_E1_chamber_drift {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 ≤ a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V) (N : ℕ) :
    ∃ (Ψ : Ch N → ℝ) (L : ℝ≥0), ContDiff ℝ 1 Ψ ∧ LipschitzWith L (gradient Ψ) ∧
      (∀ z, Ψ (z + WithLp.toLp 2 fun _ : Fin N => (1 : ℝ)) = Ψ z) ∧
      (∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y → ∀ k : Fin N,
        liftedDrift D y (π k) 0 =
          -(gradient (cep_chamberPot a N) (cep_toCh π y)) k - (gradient Ψ (cep_toCh π y)) k) ∧
      (a = 1 → ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
        totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y)) := by
  sorry

/-- **E2 (Moreau–Yosida kit for `Φ`)**: `Φ` is convex, lsc with `Φ → ∞` at the boundary of the alcove, so its
Moreau envelopes `Φ_n` are `C^{1,1}`; the resolvent `J_n` (proximal map) maps into the alcove and the Yosida
inequality holds.  Convex analysis (`ConvexOn` of `-log sin` on `(0,1)`, existence of the prox by coercivity,
Euler–Lagrange, firm nonexpansiveness).  Also: `Φ_n ≤ Φ` on the alcove, `Φ_n ↑ Φ`. -/
theorem cep_E2_moreau_yosida (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ), cep_Yosida a N J ∧
      (∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) ∧
      (∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot a N z) ∧
      (∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot a N z))) := by
  sorry

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **E3 (global strong solutions of the regularised chamber SDE)**: Lipschitz drift on `Ch N`, adapted initial
condition, `ℱ₀`-measurable labelling `π`.  `exists_sde_solution_global_nonneg` (`B15EAux1.lean:139` is the template). -/
theorem cep_E3_regularised_sde [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {B : Ch N → Ch N} {L : ℝ≥0} (hB : LipschitzWith L B) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) :
    ∃ Z : ℝ → Ω → Ch N, cep_IsChamberSolution P ℱ W' π σ' B z₀ Z := by
  sorry

/-- **E4 (uniform `L¹` a priori bound on the singular force)**.  Let `Z^n` solve the chamber SDE with drift
`-G_n + F` (`G_n = n (· - J_n ·)`, `F` Lipschitz with `ΣF`-structure of E1) from an initial point in the alcove.
Then `sup_n E ∫_0^T ∑_k |G_n(Z^n_s)_k| ds < ∞`.  Route: translation invariance of `Φ` gives `Σ_k ∂_kΦ = 0`, so the
centre of mass `Σ Z^n_k` is Gaussian-controlled.  REPAIR (2026-10-18, found by the E4 worker): the linear
functional `Σ_k k Z^n_k` does NOT work (for `N = 2` its drift `(a/2) π cot π(x_1-x_0)` tends to `-∞` at the wrap-around
contact `x_1 - x_0 → 1`).  Use the Lyapunov function `V(z) = ½ |z - ρ|²`, `ρ_k = k/N`: on the alcove
`⟨x - ρ, ∇Φ(x)⟩ = -(a/N) ∑_{k<l} (d_{kl} - (l-k)/N) π cot π d_{kl} ≥ (a/N)(c ∑ 1/dist_circle - C)`, `d_{kl} = x_l - x_k`
(checked numerically for `N = 3..6`, to be proved), with `|∇Φ|_1 ≤ C ∑ 1/dist`; Itô for `V(Z^n)` (martingale term has
mean zero) and expectations give the bound, of order `E|z₀|²`.  The hypothesis `hz₀b` (bounded initial point; the
centre of mass of `z₀` is not controlled by the alcove) was added for this reason; it holds in the application because
the sorted representatives lie in `[0,1)^N` (E0).  The same hypothesis is added to E5b, E5c, E6. -/
theorem cep_E4_L1_bound [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∫ ω, (∫ s in (0 : ℝ)..T, ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|) ∂P ≤ C := by
  sorry

/-- **E5a (pathwise Yosida–Gronwall estimate; deterministic)**.  For two solutions with the same initial point and
the same noise path (the noise cancels in the difference),
`|Z^m_t - Z^n_t|² ≤ e^{2Lt} · 2(1/m + 1/n) ∫_0^t |⟨G_m(Z^m_s), G_n(Z^n_s)⟩| ds`. -/
theorem cep_E5a_pathwise_yosida {a : ℝ} {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) {m n : ℝ} (hm : 0 < m) (hn : 0 < n)
    {z₀ : Ch N} {Zm Zn : ℝ → Ch N} {noise : ℝ → Ch N} (hZm : Continuous Zm) (hZn : Continuous Zn)
    (hm_eq : ∀ t, 0 ≤ t → Zm t = z₀ + (∫ s in (0 : ℝ)..t, (-(m • (Zm s - J m (Zm s))) + F (Zm s))) + noise t)
    (hn_eq : ∀ t, 0 ≤ t → Zn t = z₀ + (∫ s in (0 : ℝ)..t, (-(n • (Zn s - J n (Zn s))) + F (Zn s))) + noise t) :
    ∀ t, 0 ≤ t → ‖Zm t - Zn t‖ ^ 2 ≤ Real.exp (2 * L * t) * (2 * (1 / m + 1 / n)) *
      ∫ s in (0 : ℝ)..t, |inner ℝ (m • (Zm s - J m (Zm s))) (n • (Zn s - J n (Zn s)))| := by
  sorry

/-- **E5b (vanishing Yosida defect; SUSPECT in cost, true by the Bessel occupation scaling)**.
`E ∫_0^T (1/n) |G_n(Z^n_s)|² ds → 0` (REPAIR 2026-10-18: `0 ≤ T` added; for `T < 0` and `N ≥ 2` the statement is false, the integral tends to `-∞`; the occupation route below has a gap at distances `≪ n^{-1/2}`, the proof uses Itô on the Moreau envelope `Φ_n` and gives the rate `O(n^{-1/3})`).  Original route: pointwise `(1/n)|G_n(z)|² = n|z - J_n z|²` is `≲ n^{-1} ∑_p dist_p(J_n z)^{-2}`
(pairs `p`) and `≲ 1` on the region `dist_p ≲ n^{-1/2}`; the `L¹` bound E4 gives the occupation bound
`E ∫ 1_{dist_p(J_n Z^n) < r} ds ≤ C r`; integrating by parts against this occupation measure,
`n^{-1} ∫_{n^{-1/2}}^1 g^{-2} dν(g) ≲ n^{-1} n^{1/2}`, so the defect is `O(n^{-1/2})`. -/
theorem cep_E5b_yosida_defect [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) (hT : 0 ≤ T) :
    Filter.Tendsto (fun n : ℕ =>
      ∫ ω, (∫ s in (0 : ℝ)..T, (1 / (n : ℝ)) * ‖(n : ℝ) • (Z n s ω - J n (Z n s ω))‖ ^ 2) ∂P)
      Filter.atTop (𝓝 0) := by
  sorry

/-- **E5c (the Yosida approximations are Cauchy, uniformly on `[0,T]`, in probability)**: from E4, E5a, E5b and
Cauchy–Schwarz. -/
theorem cep_E5c_cauchy [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ ≤ m → n₀ ≤ n →
      P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z m t ω - Z n t ω‖} < ENNReal.ofReal ε := by
  sorry

/-- **E6 (the limit is a contact-allowing chamber solution; no reflection term)**.  The uniform limit `Z` of
`Z^n` lies in the closed alcove, `∑_{k<l} 1/dist(Z_k,Z_l)` is locally integrable in time a.s., its contact set has
Lebesgue measure `0`, and `Z_t = z₀ + ∫(-∇Φ(Z_s) + F(Z_s)) ds + σ' noise_t` with the principal (pointwise)
force.  SUSPECT: this is the step where an extra singular (local-time / Skorokhod) term could appear in the limit
of the integrals `∫ G_n(Z^n)`; excluding it needs the *improved occupation estimate* `E ∫ 1_{dist_p < r} ds ≤
C r^{1+θ}`, `θ > 0` (Bessel dimension `δ > 1`), for pair distances AND for triple clusters (Cépa–Lépingle 1997,
Thm 2.1-2.2; the TeX only cites this). -/
theorem cep_E6_limit_solution [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) :
    ∃ Zl : ℝ → Ω → Ch N, (∀ ω, Continuous fun t => Zl t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t)) ∧
      (∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N)) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Set.Icc 0 T)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Zl t ω = z₀ ω +
        (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot a N) (Zl s ω)) + F (Zl s ω))) + σ' • cep_noise π W' t ω) := by
  sorry

/-- **E7 (B.2, existence conjuncts)**: the first half of `HRS.cepa_log_flow`, verbatim hypotheses.  Route: canonical
Brownian filtration (`exists_isBrownianFiltration_of_isVectorBrownian`, `Bridge.lean:75`); sort `X₀` (E0); read the
dynamics in chamber coordinates (E1); E3 for each `n`, E5c, E6; `X = mk ∘ unrank_π ∘ Zl`; contact flow, cyclic order
(lift `Y_t = unrank Zl_t` is `π`-ordered by closure of the alcove), `NullContactOccupation` and local integrability of
the pair forces from E6; adaptedness to every Brownian filtration `ℱ` with `X₀` `ℱ₀`-measurable from pathwise uniqueness
of the Lipschitz regularised SDEs (so the strong solution built on the canonical filtration coincides a.s. with the
one built on `ℱ`, and `ℱ` is complete and contains the canonical one).  REPAIR (2026-10-18, E7 worker): the hypothesis
`Measurable[ℱ 0] X₀` of the third conjunct is replaced by `∀ t : ℝ, Measurable[ℱ t] X₀`: `IsFilteredSolution.progressive` is
`IsProgressive ℱ (ofNNRealTime X)` over `Filtration ℝ`, which contains `Measurable[ℱ t] (X 0)` for every NEGATIVE `t`; with `ℱ t` the null-set
algebra for `t < 0` (allowed by `IsBrownianFiltration`) and a non-degenerate initial law no `X` works.  The frozen `HRS.cepa_log_flow`
(HRS/Appendix/CepaFlow.lean:97) has the same defect (see ISSUES `MC: request CEPA-LOG-FLOW`). -/
theorem cep_E7_existence [IsProbabilityMeasure P]
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ))) (hV : cep_IsC11 D.V)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    ∃ X : ℝ≥0 → Ω → Config 1 N,
      (∀ T : ℝ, 0 ≤ T → IsCepaLepingleFlow P D T X₀ W X) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ᵐ ω ∂P, ∀ i j : Fin N, i ≠ j →
        IntegrableOn (fun r : ℝ => periodicRieszGrad 1 D.s
          (X (Real.toNNReal r) ω i - X (Real.toNNReal r) ω j)) (Set.Icc 0 T)) ∧
      (∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ),
        IsBrownianFiltration P ℱ W' → (∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) →
        (∀ t : ℝ, Measurable[ℱ t] X₀) → IsFilteredSolution P ℱ W' W X) := by
  sorry

end Existence

/-! ## Part H: entropy admissibility on the circle (B.14) -/

section Entropy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- **H1 (the FKE conjunct is a corollary of `selected_law_fke`)**.  The hypotheses of B.14 give
`SelectedFlow P D T X₀ W X` (right disjunct of `flow`: `d = 1`, `s = 0`, `0 < invβ`, `a = 1`, `hX`), and
`selected_law_fke` (`SelectedLawFKE.lean:813`, needs `Torus.IsCk 2 D.V`) is literally `SolvesSelectedFKE`. -/
theorem cep_H1_fke [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    SolvesSelectedFKE D T (selectedLaw P X) := by
  sorry

/-- **H0 (additivity of the Fisher information over the cyclic components)**.  Let `C c` be pairwise disjoint open
sets covering `collisionSetᶜ` (the cyclic-order components of the labelled collision-free configuration space) and
`ν c` probability measures with `ν c (C c)ᶜ = 0`.  Then `𝓘_G(∑ p c ν c) = ∑ p c 𝓘_G(ν c)` (the Fisher test fields split over
the components since their supports are compact in the open collision-free set), and the Gibbs entropy splits as
`𝓗_G(∑ p c ν c) = ∑ p c 𝓗_G(ν c) + ∑ p c log p c` (disjoint supports of the densities; EReal bookkeeping).  Used to condition
on the `ℱ₀`-measurable cyclic order, so that the Yosida chamber construction applies to each conditional flow. -/
theorem cep_H0_component_additivity {D : DynData 1} {ι : Type*} [Fintype ι] (C : ι → Set (Config 1 N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (collisionSet 1 N)ᶜ) (ν : ι → Measure (Config 1 N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    fisherInfo D N (∑ c, ENNReal.ofReal (p c) • ν c) = ∑ c, ENNReal.ofReal (p c) * fisherInfo D N (ν c) ∧
    gibbsEntropy D (∑ c, ENNReal.ofReal (p c) • ν c) =
      ∑ c, ((p c : ℝ) : EReal) * gibbsEntropy D (ν c) + ∑ c, (((p c * Real.log (p c)) : ℝ) : EReal) := by
  sorry

/-- **H2 (entropy dissipation for the regularised chamber flow; the largest single new packet)**.  For a `C²`,
diagonally periodic potential `U` with a quadratic transverse confinement, a strong solution of
`dZ = -∇U(Z) dt + √(2 invβ) dW` (in the chamber coordinates `cep_noise`) whose reduced initial law has finite
cylinder entropy satisfies `𝓗_U(μ_t) + invβ ∫_0^t 𝓘_U(μ_r) dr ≤ 𝓗_U(μ_0)`, `μ_r = Law(reduce Z_r)`.
Route: the torus FP chain (`HRS/PDE/TorusFP*`, `d1_*`, `b15d_*`, `b15e_regularised_entropy`, B15EAux7.lean:21) re-done on
`S¹ × ℝ^{N-1}`: mollify `U` to `C^∞` with `C^{1,1}` control; FP solution by the heat kernel of `ℝ^N` with Picard
iteration for the Lipschitz drift (or Hermite/OU expansion in the confined transverse variables); Itô duality
(`d1_law_eqT_proof` pattern) to identify `μ_r` with the FP solution; free-energy dissipation with the
Gaussian-weight integrability bookkeeping; Gronwall for the mollification parameter and lower semicontinuity
(`b15e_limit_core`) for the removal of the mollifier. -/
theorem cep_H2_cylinder_entropy [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 2 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {invβ : ℝ} (hβ : 0 < invβ) {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀)
    {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * invβ)) (fun z => -(gradient U z)) z₀ Z)
    (hfin : cep_cylEntropy invβ U (P.map fun ω => cep_reduce (z₀ ω)) < ⊤) :
    ∀ t : ℝ, 0 ≤ t →
      cep_cylEntropy invβ U (P.map fun ω => cep_reduce (Z t ω))
        + ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) t,
            cep_cylFisher invβ U (P.map fun ω => cep_reduce (Z r ω)) : ℝ≥0∞) : EReal)
        ≤ cep_cylEntropy invβ U (P.map fun ω => cep_reduce (z₀ ω)) := by
  sorry

/-- **H3 (passage to the limit `n → ∞`: lower semicontinuity and identification of the references)**.
Single cyclic component (`π ≡ σ₀`), `a = 1`.  Let `Z^n` be the Yosida chamber flows with potential
`U_n = Φ_n + Ψ` (`Φ_n` the Moreau envelope of E2, `Ψ` from E1), `Zl` their limit (E6), and
`X = mk ∘ unrank_{σ₀} ∘ Zl`.  Then, for every `t ≥ 0`,
(a) `𝓗_G(Law X_t) ≤ liminf_n 𝓗_{U_n}(Law reduce Z^n_t)` (Donsker–Varadhan lsc: `Z^n_t → Zl_t` in probability, the
    potentials increase to `totalPotential` on the alcove, `b15b_klDiv_liminf_le`, B15BAux1; the bijection
    `cell ∩ alcove ≅ C_{σ₀}` identifies Lebesgue measure and Gibbs weights, `Z_G = K Z_C`),
(b) `∫_0^t 𝓘_G(Law X_r) dr ≤ liminf_n ∫_0^t 𝓘_{U_n}(Law reduce Z^n_r) dr` (sup over `ζ ∈ C_c^∞(Ω_N)` of continuous
    functionals, `∇U_n → ∇U` locally uniformly on the alcove, `𝓘_{U_n} ≥` the `ζ`-functional, Fatou in `r`;
    `b15b_fisherInfoGen_liminf_le`),
(c) `limsup_n 𝓗_{U_n}(Law reduce z₀) ≤ 𝓗_G(Law X_0)` (`U_n ≤ U` on the alcove, monotone limit of partitions).
REPAIR (2026-10-18, H3 worker): two hypotheses were missing, `hΦlim` (pointwise convergence `Φn n → cep_chamberPot` on the
alcove; without it a shift `Φn n - c_n` gives entropy `-n/invβ → -∞`) and `hZlc` (continuity of `Zl` in `t`; `⨆` over `Set.Icc` is a junk `0` on
unbounded families, so `hZl` says nothing there).  Both are outputs of E2 and E6. -/
theorem cep_H3_limit_semicontinuity [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ))
    (hV : cep_IsC11 D.V) (σ₀ : Equiv.Perm (Fin N))
    {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida 1 N J) {Φn : ℝ → Ch N → ℝ}
    (hΦ : ∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z)
    (hΦle : ∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot 1 N z)
    (hΦlim : ∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot 1 N z)))
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨ : ContDiff ℝ 1 Ψ) (hΨL : LipschitzWith L (gradient Ψ))
    (hΨtot : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y →
      totalPotential D (fun i => Torus.mk (y i)) = cep_chamberPot 1 N (cep_toCh π y) + Ψ (cep_toCh π y))
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' (fun _ => σ₀) (Real.sqrt (2 * D.invβ))
      (fun z => -(gradient (fun w => Φn n w + Ψ w) z)) z₀ (Z n))
    {Zl : ℝ → Ω → Ch N}
    (hZl : ∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0))
    (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlA : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hZlnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) :
    ∀ t : ℝ, 0 ≤ t →
      gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) t)
        ≤ Filter.liminf (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
            (P.map fun ω => cep_reduce (Z n t ω))) Filter.atTop ∧
      (∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N
          (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) r))
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ r in Set.Icc (0 : ℝ) t, cep_cylFisher D.invβ (fun w => Φn n w + Ψ w)
            (P.map fun ω => cep_reduce (Z n r ω))) Filter.atTop ∧
      Filter.limsup (fun n : ℕ => cep_cylEntropy D.invβ (fun w => Φn n w + Ψ w)
            (P.map fun ω => cep_reduce (z₀ ω))) Filter.atTop
        ≤ gibbsEntropy D (selectedLaw P (fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i)) 0) := by
  sorry

/-- **H4a (finite Gibbs entropy gives a density)**: `𝓗_G(μ) < ⊤` for a probability measure `μ` on `Config 1 N` implies
`μ ≪ volume` (`relEntropy` finite ⇒ `μ ≪ gibbsRef ≪ volume`).  Mathlib `klDiv_ne_top_iff`. -/
theorem cep_H4a_density_of_entropy {D : DynData 1} (hβ : 0 < D.invβ) (μ : Measure (Config 1 N))
    [IsProbabilityMeasure μ] (h : gibbsEntropy D μ < ⊤) : μ ≪ (volume : Measure (Config 1 N)) := by
  sorry

/-- **H4 (entropy inequality for a flow on one cyclic component)**: assembly of E7 (the flow is `mk ∘ unrank ∘ Zl`, by
uniqueness U2), H2 for every `n`, H3 and H4a.  Hypothesis `hcomp`: the initial configuration lies a.s. in a single
cyclic component with anchor `σ₀`, i.e. it has a lift strictly ordered along `σ₀` (REPAIR 2026-10-18: the first draft asked for the
sorted representatives in `[0,1)` to be ordered along `σ₀`, which selects only one of the `N` rotations of a cyclic class and would
make the decomposition in H5 mix classes). -/
theorem cep_H4_single_component [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (σ₀ : Equiv.Perm (Fin N))
    (hcomp : ∀ᵐ ω ∂P, ∃ y : Fin N → Euc 1, (fun i => Torus.mk (y i)) = X₀ ω ∧ cep_StrictlyOrdered σ₀ y)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0) (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    cep_EntropyConcl P D T X := by
  sorry

/-- **H5 (B.14, assembly)**: the frozen statement `HRS.cepa_entropy_confined`.  Route: H1 for the FKE conjunct;
for the entropy conjunct decompose the (finite-entropy) initial law over the finitely many cyclic components
`C_c` (the `ℱ₀`-measurable class of `X₀`), apply H4 to the conditional flows `P(· | X₀ ∈ C_c)` (hypotheses of
B.14 are stable under conditioning on an `X₀`-event: independence of `X₀` and `W`, the Brownian filtration),
and recombine with H0 (entropy and Fisher information are additive with the stated mixing constant, which is the
same at time `0` and at time `t`). -/
theorem cep_H5_entropy_confined [IsProbabilityMeasure P]
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
    cep_EntropyConcl P D T X ∧ SolvesSelectedFKE D T (selectedLaw P X) := by
  sorry

end Entropy

/-! ## Part P: smoothing of the selected law on the collision-free space (B.4) -/

section Smoothing

/-- **P2 (parabolic Weyl lemma for measures)**.  Let `O ⊆ ℝ × ℝⁿ` be open, `b : O → ℝⁿ` smooth, `invβ > 0`, and `ρ` a
measure on `ℝ × ℝⁿ`, finite on compact subsets of `O`, solving
`∂_t ρ = invβ Δ_x ρ - div_x(b ρ)` in `𝒟'(O)`.  Then `ρ|_O` has a `C^∞` density.  This is the only genuinely PDE
statement of B.4 (the TeX appeals to "interior parabolic regularity"/hypoellipticity).  Route (no kernel
theory needed): localise by a cutoff `χ`; `χρ` solves `(∂_t - invβ Δ)(χρ) = ` (first-order derivatives of `ρ`
against smooth coefficients) in `𝒟'(ℝ^{n+1})`; Fourier transform in `(t,x)` (Mathlib `Fourier`, Schwartz
space), the symbol `iτ + invβ|ξ|²` gains two `x`-derivatives (one in the anisotropic Sobolev scale
`H^{s}_{par}`); start from `ρ ∈ H^{-s₀}` (a finite compactly supported measure lies in `H^{-s}` for `s > (n+1)/2`),
bootstrap to all `s`, Sobolev embedding to `C^∞`.  Nonnegativity of `f` from positivity of `ρ` and continuity. -/
theorem cep_P2_parabolic_weyl {n : ℕ} {O : Set (ℝ × EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    {b : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b O) {invβ : ℝ} (hβ : 0 < invβ)
    {ρ : Measure (ℝ × EuclideanSpace ℝ (Fin n))} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    (heq : ∀ Φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ →
        HasCompactSupport Φ → tsupport Φ ⊆ O →
        ∫ p, (fderiv ℝ Φ p (1, 0)
              + invβ * ∑ k : Fin n, fderiv ℝ (fderiv ℝ Φ) p (0, EuclideanSpace.single k 1) (0, EuclideanSpace.single k 1)
              + fderiv ℝ Φ p (0, b p)) ∂ρ = 0) :
    ∃ f : ℝ × EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O ∧ (∀ p ∈ O, 0 ≤ f p) ∧
      ρ.restrict O = ((volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))).restrict O).withDensity
        (fun p => ENNReal.ofReal (f p)) := by
  sorry

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- **P3 (local-to-global: smooth space-time density on `(0,T) × Ω_N`)**.  Hypotheses of B.4.  Route:
(i) the distributional equation of the space-time measure `ρ(dt,dx) = (selectedLaw P X t)(dx) dt` on `(0,T) × Ω_N`
from `selected_law_fke` (test functions supported in `(0,T) × Ω_N` have vanishing `t = 0` term, `IsFKETest`
is exactly this class with `time_support`/`space_support`); (ii) in a local chart of the covering `(Fin N → Euc d) → Config d N`
(a ball of radius `< 1/2`, a homeomorphism onto its image) transfer `ρ` and the drift
`b = particleDrift` (smooth off collisions: `smoothOffZero_of_dim`, `SelectedLawFKE.lean:212`; `V` smooth) to a measure on a
Euclidean open set and apply `cep_P2_parabolic_weyl` (identify `Fin N → Euc d` with `EuclideanSpace ℝ (Fin (N d))`
through `configBasis`); (iii) the local densities agree on overlaps (a.e. equal continuous functions are equal), so they
patch to a smooth `f`, defined as `0` on the collisions. -/
theorem cep_P3_spacetime_density [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ f : ℝ → Config d N → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}) ∧
      (∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x) ∧
      ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) := by
  sorry

/-- **P4 (every time slice, not only a.e.)**: if `f` is a smooth space-time density as in P3 then for every
`t ∈ (0,T)` the restriction of `selectedLaw P X t` to the collision-free set has density `f t`.  Route:
a.e. `t` by Fubini/disintegration (`P3` with `S = {t'} × B` sets, Tonelli), then both sides are narrowly continuous in
`t` against test functions compactly supported in `Ω_N` (`selectedLaw_narrow_continuous`, `Stochastic/SelectedLawFKE.lean`,
and dominated convergence for `∫ ψ f(t,·)`), so equality extends from a dense set of times to all times. -/
theorem cep_P4_time_slices [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {f : ℝ → Config d N → ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N)))) :
    ∀ t ∈ Set.Ioo 0 T, (selectedLaw P X t).restrict (collisionSet d N)ᶜ =
      ((volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ).withDensity
        (fun x => ENNReal.ofReal (f t x)) := by
  sorry

/-- **P5 (the density solves the classical forward equation)**: pointwise `∂_r f = fkeForward D f r` on
`(0,T) × Ω_N`.  Route: for a smooth compactly supported test `Φ` in `(0,T) × Ω_N`, the distributional equation
(P3 (i)) with `ρ = f dt dx` and integration by parts (smooth `f`, compactly supported `Φ`) gives
`∫ Φ·(∂_t f - fkeForward f) = 0`; the fundamental lemma
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` (Mathlib) and continuity give the pointwise identity; `HasDerivAt`
in `r` from `ContDiffOn`.  REPAIR (2026-10-18, P3-P6 worker): the hypothesis `hf0 : 0 ≤ f` was added (as in P4):
`hρ` only constrains `ENNReal.ofReal f`, so on an empty cyclic chamber (d = 1, N ≥ 3) `f` could be any smooth
negative function, for which the classical equation fails. -/
theorem cep_P5_forward_equation [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {f : ℝ → Config d N → ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N)))) :
    ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, HasDerivAt (fun r' => f r' x) (fkeForward D f r x) r := by
  sorry

/-- **P6 (B.4, assembly)**: the frozen statement `HRS.selected_law_smoothing`.  The last conjunct is elementary:
under a.s. noncollision, `selectedLaw P X t (collisionSet) = P(X_t ∈ collisionSet) = 0` (the collision set is closed,
`isClosed_collisionSet`), so `selectedLaw P X t` equals its restriction to the complement. -/
theorem cep_P6_selected_law_smoothing [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
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

end Smoothing

end HRS.MC.Cepa
