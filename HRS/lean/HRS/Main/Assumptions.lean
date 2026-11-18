import HRS.Dynamics.Setup
import HRS.PDE.ForwardEq
import HRS.PDE.Convention
import HRS.PDE.Fourier
import HRS.Stochastic.SelectedFlow
import HRS.Energy.Coercivity

/-!
# Appendix A (main manuscript): the standing assumptions of the torus fluctuation theorems

Specification file SPEC-A.  Sources (`HRS_periodic_main_20261008T010000Z.tex`, "M"):
* Assumption A.1 `M:B:ass:sde` (L10127-10143);
* Assumption A.2 `M:B:ass:regime` (L10168-10180; already `HRS.PDE.Regime`, `Regime.Holds`);
* Assumption A.3 `M:B:ass:mf-reg` (L10201-10203);
* Assumption A.4 `M:B:ass:init` (L10207-10218);
* Assumption A.5 `M:B:ass:init-field` (L10221-10232);
* Assumption A.6 `M:B:ass:MF` (L10235-10247);
* Assumption A.7 `M:B:ass:MF2` (L10249-10259);
* the global notation of the section (L10156-10164): `m_* = ⌊d/2⌋ + 3`, `γ = m_* + d + 3`
  (`B:eq:gamma-def`, L10333), the coefficient discrepancy `Δ_N^{(m)}` (`B:eq:deltaN`, L10412-10418).

## Representation decisions (all checked by the orchestrator against the TeX)

* **Sequences.**  The TeX works with a sequence in `N` of coefficients and of particle systems.  The
  deterministic data (`d, s, M, V, T, μ°, β_N⁻¹, κ_N`, and the mean-field solutions `μ_{β_N}`) is the
  structure `MainData`; the random data at particle number `N` (probability space, `X_N^0`, the
  Brownian motions, the particle flow `X_N`, and the initial fluctuation functional `η°`) is the
  structure `Realization d N`, and a sequence is `R : ∀ N, Realization d N` (the probability space
  may depend on `N`, as the couplings do).  Every per-`N` assumption is imposed for `1 ≤ N` only
  (for `N = 0` the empirical measure is the zero measure and the assumptions could not hold).
* `β_N = ∞` is `invβ N = 0` (`DynData`), exactly as in `HRS/Dynamics/Setup.lean`.
* **`η°`** is a *random real-linear functional on `Y_0 = H^{m_0}`* (A.4, "random real-linear functional
  `η°` on the test class `Y_0`"): `Realization.η : Ω → (Torus d → ℝ) → ℝ`, jointly measurable (the
  product σ-algebra), real-linear on `{ψ | MemSobolev m₀ ψ}`.  It is *not* an element of
  `NegSobolev d m₀`, because `m₀ ≤ m_*` may be `≤ d/2`.  In the field-level assumption A.5 the
  same `η°` is `H^{-γ}`-valued: `ηF : Ω → NegSobolev d γ` with `η ω ψ = eval (ηF ω) ψ` for mean-zero
  `ψ ∈ H^γ` (the project's zero-total-mass convention `E_γ = H^{-γ}_0`; the zero mode of `η°` is not
  recorded, as `⟨1, Ξ_N⟩ = 0`).
* **Expectations** of possibly non-integrable quantities are `lintegral`s of `ENNReal.ofReal`
  (as in `HRS/Dynamics/InitialData.lean`), so that no junk Bochner value can make a bound vacuous.
* **`o_N(Λ)`** of A.6 is `HRS.oNΛ d s C₀ Λ N` (`B:eq:hrs-coercivity-exact-correction`, L2882) with a
  completion constant `C₀` as in Proposition 3.34 (`IsCoercivityPair`); the corrected energy is
  `HRS.correctedEnergy`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Global notation of Appendix A -/

/-- `γ = m_* + d + 3` (`B:eq:gamma-def`, TeX L10333), with `m_* = ⌊d/2⌋ + 3` (`PDE.mStar`,
`B:eq:mstar-def`, L10158). -/
def gammaIdx (d : ℕ) : ℕ := PDE.mStar d + d + 3

/-! ### The deterministic data -/

/-- The deterministic data of Appendix A, "Throughout this section" (TeX L10156): `d ≥ 1`,
`0 ≤ s < d`, the constant matrix `M`, the periodic potential `V`, the horizon `T > 0`, the datum
`μ°` (a probability measure, independent of `N`), the inverse temperatures `β_N⁻¹ ∈ [0,∞)`
(`0` means `β_N = ∞`) with the standing bound `sup_N β_N⁻¹ < ∞` (`invβ_bdd`, TeX L539), the scales `κ_N > 0`, and the mean-field solutions
`μ_{β_N}^t = ρ N t dx` (A.3 prescribes which properties they have). -/
structure MainData (d : ℕ) where
  s : ℝ
  hs0 : 0 ≤ s
  hsd : s < d
  hd : 1 ≤ d
  M : Matrix (Fin d) (Fin d) ℝ
  V : Torus d → ℝ
  T : ℝ
  hT : 0 < T
  μ0 : Measure (Torus d)
  hμ0 : IsProbabilityMeasure μ0
  invβ : ℕ → ℝ
  hinvβ : ∀ N, 0 ≤ invβ N
  /-- the standing bound `sup_N β_N⁻¹ < ∞` of `H:subsec:general` (TeX L539), imported by L10156 -/
  invβ_bdd : ∃ B : ℝ, ∀ N, invβ N ≤ B
  κ : ℕ → ℝ
  hκ : ∀ N, 0 < κ N
  ρ : ℕ → ℝ → Torus d → ℝ

namespace MainData

variable (S : MainData d)

/-- The dynamics data at particle number `N` (`HRS.DynData`). -/
def dyn (N : ℕ) : DynData d := ⟨S.s, S.M, S.V, S.invβ N, S.hs0, S.hsd, S.hinvβ N⟩

/-- `σ_N = min{κ_N, √(Nβ_N)}` (`H:eq:intro-scales`; `(σ_N,A_N,q_N) = (κ_N,1,0)` if `β_N = ∞`). -/
def sigma (N : ℕ) : ℝ := sigmaScale N (S.κ N) (S.invβ N)

/-- `A_N = σ_N / κ_N`. -/
def AN (N : ℕ) : ℝ := Ascale N (S.κ N) (S.invβ N)

/-- `q_N = σ_N² / (N β_N)`; the noise covariance of `B:eq:surrogate-cov` is `2 q_N ∫ ...`. -/
def qN (N : ℕ) : ℝ := qScale N (S.κ N) (S.invβ N)

/-- Assumption A.2 `M:B:ass:regime` for the whole sequence: in the regime `Rg` (with `ν₀` for R3)
every trajectory `μ_{β_N}` satisfies `HRS.PDE.Regime.Holds` (TeX L10168-10180: "one of the following
holds", with `inf_N inf μ_{β_N} ≥ λ₀` in R2b and `inf_N β_N⁻¹ = ν₀ > 0` in R3). -/
def RegimeHolds (Rg : PDE.Regime) (ν₀ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → Rg.Holds d S.s S.M (S.invβ N) ν₀ S.T (S.ρ N)

end MainData

/-! ### The random data at particle number `N` -/

/-- The random objects at particle number `N`: a probability space, the initial configuration `X_N^0`,
the Brownian motions `(W_i)_{i ≤ N}`, the selected empirical flow `X_N`, and the initial fluctuation
functional `η°` (a random real-linear functional on the test class, see the module docstring). -/
structure Realization (d N : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [isProb : IsProbabilityMeasure P]
  X₀ : Ω → Config d N
  W : ℝ≥0 → Ω → (Fin N → Euc d)
  X : ℝ≥0 → Ω → Config d N
  η : Ω → (Torus d → ℝ) → ℝ

attribute [instance] Realization.mΩ Realization.isProb

/-! ### Assumption A.1 -/

/-- Assumption A.1 `M:B:ass:sde` (TeX L10127-10143), selected empirical semimartingale flow at one
`N`: `X_N^0` is a.s. pairwise distinct and independent of `(W_i)`, and the flow is one of
(a)/(d) the pathwise unique collision-free strong solution (the TeX cases (a) "its canonical
collision-free strong solution" and (d) "a pathwise unique collision-free strong solution has been
selected" are the same notion and collapse into one disjunct, as in `HRS.SelectedFlow`),
(b) `d = 1`, `s = 0`, `β_N < ∞`, `M = -a` (`a > 0`): the Cépa–Lépingle flow,
(c) `d = 1`, `s = 0`, `β_N < ∞`, `M = 0`: the ordinary system of independent confined diffusions
(a contact-allowing strong solution; with `M = 0` the drift has no singular term).
This extends `HRS.SelectedFlow`, which omits case (c) (`M = 0`, L10132); the law `P_N^t` and the
density `f_N^t` of `B:eq:selected-particle-law` are `HRS.selectedLaw`, `HRS.HasSelectedDensity`,
`HRS.selectedDensity`. -/
structure SelectedFlowA1 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (D : DynData d)
    (T : ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  init_meas : Measurable X₀
  init_distinct : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ω => fun t => W t ω) P
  flow :
    (IsStrongSolution P D T X₀ W X ∧ PathwiseUnique P D T X₀ W) ∨
    (d = 1 ∧ D.s = 0 ∧ 0 < D.invβ ∧ (∃ a : ℝ, 0 < a ∧ D.M = -(a • 1)) ∧
      IsCepaLepingleFlow P D T X₀ W X) ∨
    (d = 1 ∧ D.s = 0 ∧ 0 < D.invβ ∧ D.M = 0 ∧ IsContactStrongSolution P D T X₀ W X)

/-- `HRS.SelectedFlow` (cases (a),(b),(d) of A.1) implies `SelectedFlowA1`. -/
theorem SelectedFlow.toA1 {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : SelectedFlow P D T X₀ W X) : SelectedFlowA1 P D T X₀ W X :=
  ⟨h.init_meas, h.init_distinct, h.brownian, h.indep, h.flow.elim Or.inl fun h' => Or.inr (Or.inl h')⟩

/-- Assumption A.1 for a sequence of realizations: for every `N ≥ 1`. -/
def SelectedFlows (S : MainData d) (R : ∀ N, Realization d N) : Prop :=
  ∀ N : ℕ, 1 ≤ N → SelectedFlowA1 (R N).P (S.dyn N) S.T (R N).X₀ (R N).W (R N).X

/-! ### Assumption A.3 -/

/-- Assumption A.3 `M:B:ass:mf-reg` (TeX L10201-10203) at the derivative index `r`
(`r ≥ r(m) = m + 3` for the largest index `m` used, `B:ass:mf-reg`; the theorems display `r`):
for each `N` the datum is `μ°`, `μ_{β_N}` solves the mean-field equation with viscosity `β_N⁻¹`
(`HRS.IsMeanFieldSolution`, including the weak formulation `B:eq:mf-weak` and the continuity into
`𝒫(𝕋^d)`), is `(r,Λ)`-regular in the sense of `B:eq:mf-regularity` *including* the proviso for
`d-1 ≤ s < d` (`HRS.PDE.IsRegularMFProviso`), and `∂_t μ_{β_N} ∈ C([0,T]; C^0_b)` uniformly in `N`
(the time derivative exists on `[0,T]` (one-sided at the endpoints), is jointly continuous, and is
bounded by a constant `B` independent of `N`). -/
structure MeanFieldRegularity (S : MainData d) (r : ℕ) (Λ : ℝ) : Prop where
  solution : ∀ N : ℕ, 1 ≤ N → IsMeanFieldSolution (S.dyn N) S.T (S.ρ N)
  datum : ∀ N : ℕ, 1 ≤ N → withDensityReal (S.ρ N 0) = S.μ0
  regular : ∀ N : ℕ, 1 ≤ N → PDE.IsRegularMFProviso S.s r Λ S.T (S.ρ N)
  time_derivative : ∃ (B : ℝ) (ρt : ℕ → ℝ → Torus d → ℝ), ∀ N : ℕ, 1 ≤ N →
    (∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Torus d,
      HasDerivWithinAt (fun u => S.ρ N u x) (ρt N t x) (Set.Icc (0 : ℝ) S.T) t) ∧
    ContinuousOn (fun p : ℝ × Torus d => ρt N p.1 p.2) (Set.Icc (0 : ℝ) S.T ×ˢ Set.univ) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Torus d, |ρt N t x| ≤ B

/-! ### Assumption A.4 (initial fluctuation, statistics level) -/

/-- Assumption A.4 `M:B:ass:init` (TeX L10207-10218).  The finite family of terminal tests and
times of the conclusion enters through the sets `Ψ N` of *transported terminal tests* (the
finite-dimensional span in L10208; for the pair `(φ,t)` the transported test is `U_N^{0,t}φ`,
see `transportedTests`), and the coupling `(X_N^0, η°)` (the realization `R`) may depend on this
family.  Data: `m₀ ∈ {1,…,m_*}` (`Y_0 = Y_0' = H^{m₀}`, norm `sobolevNorm m₀`), `C_in ≥ 1`,
`ε_N ↓ 0` (hence `ε_N ≥ 0`).  `η°` is a random real-linear functional on `Y_0`, one functional of
fixed law (`fixed_law`); only the coupling depends on `N`.
* (I1) `E|⟨ψ,κ_N Ξ_N^0⟩ - ⟨ψ,η°⟩| ≤ ε_N ‖ψ‖_{Y_0}` for `ψ ∈ span (Ψ N)` (with `ψ ∈ Y_0`),
  `Ξ_N^0 = μ_N^0 - μ°`;
* (I2) `E|⟨ψ,κ_N Ξ_N^0⟩|² + E|⟨ψ,η°⟩|² ≤ C_in² ‖ψ‖²_{Y_0'}` for every real `ψ ∈ Y_0`
  (**Technical hypothesis**: restricted to continuous `ψ`, because for an `H^{m₀}` class without a
  continuous representative the pairing with an empirical measure is not defined);
* (I3) `X_N^0` and `η°` are independent of the Brownian motions (jointly: `(X_N^0, η°) ⫫ (W_i)_i`).
Expectations are `lintegral`s of `ofReal`. -/
structure InitialFluctuation (S : MainData d) (R : ∀ N, Realization d N) (m₀ : ℕ) (Cin : ℝ)
    (ε : ℕ → ℝ) (Ψ : ℕ → Set (Torus d → ℝ)) : Prop where
  m₀_pos : 1 ≤ m₀
  m₀_le : m₀ ≤ PDE.mStar d
  Cin_ge : 1 ≤ Cin
  eps_anti : Antitone ε
  eps_tendsto : Tendsto ε atTop (𝓝 0)
  family_finite : ∀ N, (Ψ N).Finite
  linear : ∀ N : ℕ, ∀ ω, ∀ ψ χ : Torus d → ℝ, ∀ c : ℝ, MemSobolev (m₀ : ℝ) ψ → MemSobolev (m₀ : ℝ) χ →
    (R N).η ω (c • ψ + χ) = c * (R N).η ω ψ + (R N).η ω χ
  η_meas : ∀ N : ℕ, ∀ ψ : Torus d → ℝ, Measurable fun ω => (R N).η ω ψ
  /-- A.4 fixes *one* random functional `η°` (L10208: "there is a random real-linear functional `η°`";
  only the coupling with `X_N^0` depends on `N` and on the family): its law does not depend on `N`. -/
  fixed_law : ∃ νη : Measure ((Torus d → ℝ) → ℝ), ∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη
  I1 : ∀ N : ℕ, 1 ≤ N → ∀ ψ ∈ Submodule.span ℝ (Ψ N), MemSobolev (m₀ : ℝ) ψ →
    ∫⁻ ω, ENNReal.ofReal |S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ|
        ∂(R N).P ≤
      ENNReal.ofReal (ε N * sobolevNorm (m₀ : ℝ) ψ)
  I2 : ∀ N : ℕ, 1 ≤ N → ∀ ψ : Torus d → ℝ, MemSobolev (m₀ : ℝ) ψ → Continuous ψ →
    ∫⁻ ω, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ)) ^ 2)
        ∂(R N).P +
      ∫⁻ ω, ENNReal.ofReal (((R N).η ω ψ) ^ 2) ∂(R N).P ≤
    ENNReal.ofReal (Cin ^ 2 * sobolevNorm (m₀ : ℝ) ψ ^ 2)
  I3 : ∀ N : ℕ, 1 ≤ N →
    IndepFun (fun ω => ((R N).X₀ ω, (R N).η ω)) (fun ω => fun t => (R N).W t ω) (R N).P

/-! ### Assumption A.5 (initial fluctuation, field level) -/

/-- Assumption A.5 `M:B:ass:init-field` (TeX L10221-10232), "in addition to A.4" (the same coupling
`(X_N^0, η°)`), with `Γ = γ` an index: on `𝕋^d`, `η°` is `H^{-Γ}`-valued (`ηF`, compatible with the
functional `η` on mean-zero `H^Γ` tests, zero-mass convention of `NegSobolev`) and
`E‖κ_N Ξ_N^0 - η°‖_{H^{-Γ}} ≤ ε_N^f` (`ε_N^f ≥ 0`), `η°` of fixed law `νin`, `E‖κ_N Ξ_N^0‖² + E‖η°‖² ≤ C_in²`
(norms in `NegSobolev d Γ`; expectations as `lintegral`s). -/
structure InitialFluctuationField (S : MainData d) (R : ∀ N, Realization d N) (Γ : ℕ) (Cin : ℝ)
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (Γ : ℝ))
    (νin : Measure (NegSobolev d (Γ : ℝ))) : Prop where
  ηF_meas : ∀ N, Measurable (ηF N)
  /-- `η°` is one random field: it has the fixed law `νin`, independent of `N` (L10208, L10285). -/
  law_eq : ∀ N : ℕ, 1 ≤ N → law (R N).P (ηF N) = νin
  /-- the errors `ε_N^f` are nonnegative (they bound an expectation of a norm). -/
  εf_nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ εf N
  compat : ∀ N : ℕ, ∀ ω, ∀ ψ : Torus d → ℝ, MemSobolev (Γ : ℝ) ψ → Torus.mean ψ = 0 →
    (R N).η ω ψ = NegSobolev.eval (ηF N ω) ψ
  first_moment : ∀ N : ℕ, 1 ≤ N →
    ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (Γ : ℝ) (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ
        ∂(R N).P ≤ ENNReal.ofReal (εf N)
  second_moment : ∀ N : ℕ, 1 ≤ N →
    ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (Γ : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
        ∂(R N).P +
      ∫⁻ ω, ‖ηF N ω‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2)

/-! ### Assumptions A.6, A.7 (modulated-energy smallness) -/

/-- `C₀` is a valid heat-kernel completion constant with coercivity constant `C` for the torus
Riesz energy: the conclusion of Proposition 3.34 (`HRS.periodic_coercivity`, TeX L2879-2897) holds
with `(C₀, C)`: `F_N(X,μ) + o_N(Λ) ≥ 0` and the linear-statistic bound, for all `Λ ≥ 1`, `N ≥ 2`,
densities `μ ≤ Λ`, collision-free `X`.  This is "`C₀` as in `H:eq:energy-completion`" (TeX L546-555,
with the `Λ`-dependent correction `B:eq:hrs-coercivity-exact-correction`); `C₀` and `C` depend only
on `d, s`, so the constants of the theorems may depend on them. -/
def IsCoercivityPair (d : ℕ) (s C₀ C : ℝ) : Prop :=
  0 ≤ C₀ ∧ 0 < C ∧
    ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
    ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
    ∀ X : Config d N, X ∉ collisionSet d N →
      0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
      ∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
        HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
        |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
          C * smearScale d N Λ * L +
            C * homSobolev (((d : ℝ) - s) / 2) ψ *
              Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)

/-- Such a pair exists for every `d ≥ 1`, `0 ≤ s < d` (this is `HRS.periodic_coercivity`). -/
theorem exists_coercivityPair (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, IsCoercivityPair d s C₀ C := by
  obtain ⟨C₀, C, hC₀, hC, h⟩ := periodic_coercivity hd hs0 hsd
  exact ⟨C₀, C, hC₀, hC, h⟩

/-- Assumption A.6 `M:B:ass:MF` (TeX L10235-10247): with `𝔬_N(Λ) = HRS.oNΛ d s C₀ Λ N` (a completion
constant `C₀` with coercivity constant `Cc`, `IsCoercivityPair`, recorded by `completion`; `C₀, Cc`
depend only on `d, s`, so the constants of the theorems may depend on them) and `Λ` from A.3, there is a
sequence `𝔈_N > 0` with
`sup_{t ≤ T} E[F_N(X_N^t, μ_{β_N}^t) + 𝔬_N] ≤ 𝔈_N` and `σ_N 𝔈_N → 0`.
(Expectation: `lintegral` of `ofReal` of `HRS.correctedEnergy`, which is a.s. nonnegative by the
coercivity bound.) -/
structure EnergySmallness (S : MainData d) (R : ∀ N, Realization d N) (C₀ Cc Λ : ℝ)
    (𝔈 : ℕ → ℝ) : Prop where
  completion : IsCoercivityPair d S.s C₀ Cc
  pos : ∀ N : ℕ, 1 ≤ N → 0 < 𝔈 N
  bound : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ∫⁻ ω, ENNReal.ofReal
        (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
      ENNReal.ofReal (𝔈 N)
  small : Tendsto (fun N => S.sigma N * 𝔈 N) atTop (𝓝 0)

/-- Assumption A.7 `M:B:ass:MF2` (TeX L10249-10259), the second-moment strengthening (only for the
`W₂` variants): `sup_{t ≤ T} E[(F_N(X_N^t, μ_{β_N}^t) + 𝔬_N)²] ≤ (𝔈'_N)²`, `σ_N 𝔈'_N → 0`, and (I1)
of A.4 holds in `L²`: `E|⟨ψ,κ_N Ξ_N^0⟩ - ⟨ψ,η°⟩|² ≤ (ε_N^{(2)})² ‖ψ‖²_{Y_0}` (for `ψ` in the same
class as (I1): the span of the transported tests `Ψ N`, `ψ ∈ Y_0 = H^{m₀}`). -/
structure EnergySmallness2 (S : MainData d) (R : ∀ N, Realization d N) (C₀ Λ : ℝ) (m₀ : ℕ)
    (Ψ : ℕ → Set (Torus d → ℝ)) (𝔈' ε2 : ℕ → ℝ) : Prop where
  /-- `𝔈'_N` and `ε_N^{(2)}` are nonnegative (they bound norms of random variables; without this the
  `ofReal`-clipped bounds below could hold with negative values). -/
  𝔈'_nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ 𝔈' N
  ε2_nonneg : ∀ N : ℕ, 1 ≤ N → 0 ≤ ε2 N
  bound : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
    ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2)
        ∂(R N).P ≤ ENNReal.ofReal ((𝔈' N) ^ 2)
  small : Tendsto (fun N => S.sigma N * 𝔈' N) atTop (𝓝 0)
  I1_L2 : ∀ N : ℕ, 1 ≤ N → ∀ ψ ∈ Submodule.span ℝ (Ψ N), MemSobolev (m₀ : ℝ) ψ →
    ∫⁻ ω, ENNReal.ofReal
        ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ) ^ 2)
        ∂(R N).P ≤
      ENNReal.ofReal ((ε2 N) ^ 2 * sobolevNorm (m₀ : ℝ) ψ ^ 2)

/-! ### The common package of the torus theorems -/

/-- The hypotheses shared by the torus theorems A.8-A.11: A.1, A.2 (regime `Rg`, `ν₀`), A.3 at
`r = m + 3` with `‖μ‖_{C^r} ≤ Λ`, the bounds `|M| ≤ MB` (entrywise, `HRS.PDE.MatBound`) and
`V ∈ C^{m+3}`, `‖V‖_{C^{m+3}} ≤ VB` (TeX B:sec:conv-confinement, L10074-10076; "the confinement is
used through the same derivative level"), and A.6 with `Λ`.  Here `m` is the adjoint index
(`m = m_*` in A.8; `m = γ` in A.9; `m = γ+2` in A.11, i.e. `r = m_*+3, γ+3, γ+5`).

The field `filtered` is the strong-solution adaptedness of A.1 (a Brownian filtration carrying `W` to which `X` is
adapted, `IsFilteredSolution`), which the Itô/duality identity behind every torus theorem needs and `SelectedFlowA1`
(measurability only, ISSUES D1) does not record; it mirrors `RdStanding.filtered`.  Statement repair, ISSUES.md
entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …", final entry "Filtered strong solutions …"; `SelectedFlowA1`
already has `indep : IndepFun X₀ W`, so only the filtration is added. -/
structure TorusStanding (S : MainData d) (R : ∀ N, Realization d N) (Rg : PDE.Regime)
    (ν₀ MB Λ VB : ℝ) (m : ℕ) (C₀ Cc : ℝ) (𝔈 : ℕ → ℝ) : Prop where
  flow : SelectedFlows S R
  regime : S.RegimeHolds Rg ν₀
  mean_field : MeanFieldRegularity S (m + 3) Λ
  matrix_bound : PDE.MatBound MB S.M
  potential : PDE.VHyp m VB S.V
  energy : EnergySmallness S R C₀ Cc Λ 𝔈
  /-- Strong-solution adaptedness of the selected flows (A.1, "strong solution"; ISSUES.md, filtered-solution repairs). -/
  filtered : ∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
    (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
    IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X

/-! ### Convergence of the coefficients (`B:eq:deltaN`) -/

/-- The limiting coefficient quadruple `(β_∞, μ_{β_∞}, A, 2/β_*)` of TeX L10285-10290 (`invβ = β_∞⁻¹`,
`invβstar = β_*⁻¹`, so the limiting noise covariance is `2 β_*⁻¹ ∫ ...`). -/
structure LimitCoeffs (d : ℕ) where
  invβ : ℝ
  hinvβ : 0 ≤ invβ
  ρ : ℝ → Torus d → ℝ
  A : ℝ
  hA : 0 ≤ A
  invβstar : ℝ
  hinvβstar : 0 ≤ invβstar

/-- The limiting dynamics data. -/
def LimitCoeffs.dyn (L : LimitCoeffs d) (S : MainData d) : DynData d :=
  ⟨S.s, S.M, S.V, L.invβ, S.hs0, S.hsd, L.hinvβ⟩

/-- The full coefficient discrepancy `Δ_N^{(m)}` of `B:eq:deltaN` (TeX L10412-10418):
`|β_N⁻¹ - β_∞⁻¹| + |2σ_N²/(Nβ_N) - 2/β_*| + |A_N - A| + sup_{r ≤ T} ‖μ_{β_N}^r - μ_{β_∞}^r‖_{𝒞^{m+2}}`
with the coefficient norm `𝒞^{m+2}` of Proposition 3.15 (`Torus.cbNorm (m+2)`, as in
`HRS.PDE.propagator_stability`). -/
def MainData.coeffDiscrepancy (S : MainData d) (L : LimitCoeffs d) (m N : ℕ) : ℝ :=
  |S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| + |S.AN N - L.A| +
    ⨆ r : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (m + 2) (S.ρ N r - L.ρ r)

/-- "Assume common adjoint regimes and constants and `Δ_N^{(m)} → 0`" (`B:cor:true-limit`,
TeX L10420-10421): the limit trajectory `μ_{β_∞}` solves the mean-field equation with viscosity
`β_∞⁻¹` and datum `μ°`, and the adjoint hypotheses of Proposition 3.9 (`HRS.PDE.AdjointData`: same
regime `Rg`, same `ν₀, MB, Λ, VB`, same `M, V`) hold at the level `lvl` for the limit and for every
`N`; and `Δ_N^{(m)} → 0`.  (The level `lvl` of the common adjoint regime is not specified by the TeX:
the theorems use `lvl = m` (A.9) or `lvl = m + 2` (A.11), the level of their own regularity
hypothesis.) -/
structure CoeffConvergence (S : MainData d) (L : LimitCoeffs d) (Rg : PDE.Regime)
    (ν₀ MB Λ VB : ℝ) (lvl m : ℕ) : Prop where
  limit_solution : IsMeanFieldSolution (L.dyn S) S.T L.ρ
  limit_datum : withDensityReal (L.ρ 0) = S.μ0
  limit_adjoint : PDE.AdjointData S.s lvl Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ
  seq_adjoint : ∀ N : ℕ, 1 ≤ N → PDE.AdjointData S.s lvl Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N)
  tendsto : Tendsto (fun N => S.coeffDiscrepancy L m N) atTop (𝓝 0)

end Main

end HRS
