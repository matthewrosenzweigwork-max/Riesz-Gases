import HRS.Whole.Moving
import HRS.Whole.MovtrAux10
import HRS.Whole.RegMF

/-!
# Whole-space supplement, Sections S6.2-S6.3 (`W:subsec:r2mov-entropy`, `W:subsec:r2mov-adjoint`,
`W:sec:r2mov-translation`) and `W:cor:r2-translated-particle-paths`: statements S6.6 - S6.11
(rows `S:W:thm:r2mov-entropy`, `S:W:lem:r2mov-global-adjoint`, `S:W:prop:r2mov-translation`,
`S:W:cor:r2mov-moving-reference`, `S:W:prop:r2mov-translation-relax`,
`S:W:cor:r2-translated-particle-paths`)

Source: HRS whole-space supplement (S), lines 4544-4952, 5189-5207.

Standing assumptions: as in `HRS/Whole/Moving.lean`; in S6.8-S6.11 (S L4855-4860) `g(x) = |x|^{-s}`,
`0 < s < d`, or `-log|x|`, i.e. `0 ≤ s < d`, and `a_t = e^{-qt} a_0` (in S6.11 the confinement
constant is called `a`, the shift `b`; here `q` and `b`).

## Objects reused from the S2-S5 packet (W1, `Dynamics.lean`, `Orbits.lean`, `Headline.lean`)

`quadraticGradientDyn` (gradient dynamics `V = q|x|²/2`, `M = -I`, `ν = β⁻¹`), `IsWholeStrongSolution`
(particle SDE, pathwise, collision-free), `IsWholeMeanFieldSolution`, `WholeDyn.coeff`,
`IsClassicalAdjointW` (classical adjoint solution `U(r,t)φ`), `IsLinearGaussianEvolutionW`,
`flucPathW`, `zetaPathW`, `processWindow`, `iN`, `jN`, `eucCollisionSet`, `convGradConvW`, `cbNormVecE`;
from the foundations `localizationRate`, `oN`, `deltaN`, `modulatedGibbs`, `gibbsNormalizer`,
`susceptibilityCov`, `wholeSpaceIndex`, `relEntropy`, `smoothDist`, `wassersteinE`.
The only objects defined here are those specific to the moving reference (`Mov*`).

## Representation decisions

* The adjoint `U(r,t)φ` of S6.7 is the classical adjoint solution (W1's `IsClassicalAdjointW`
  along `ρ`, whose generator is `νΔ + (-qx - ∇g*ρ^t)·∇ + ∑_j ∂_jg*(ρ^t ∂_j ·)`, exactly
  `(νΔ+b·∇) - F_t·∇ + J_t` of S L4796-4802 by the thermal equation `b = ν∇log ρ_*`).  The estimate
  is asserted for every classical adjoint solution (existence is S5, not part of S6.7).
* "One of the nonlinear trajectories of Theorem 6.3" is: some choice of the regularity indices
  `(j,m)` allowed by S6.3 (the source says "the finitely many regularity indices required by the
  particle realization" without naming them: AMBIGUITY) and the constants `(ε_*,r,c₀,c,C)` of
  `MovNonlinearConclusion`, with all initial data of the class and the (unique) solution in the small
  class.  All constants of S6.6 and S6.7 are uniform over this class.
* Moving reference `Q_N^t = Q_{N,β}(μ^t)`; its source `R_N^t` (S6.9) is written as the pointwise
  forward Kolmogorov equation `∂_t q_N^t = 𝓛_N^* q_N^t` for the explicit density `q_N^t` of `Q_N^t`
  (`movFP`, `movQDensity`), `R_N^t = (𝓛_N^*q_N^t - ∂_tq_N^t)/q_N^t`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### Particle hypotheses and preparations -/

/-- The canonical particle solution in the quadratic potential at physical inverse temperature
`β` driven by independent Brownian motions `W`, with initial configuration `X₀` independent of `W`,
on every `[0,T]` (S L4864-4868 "canonical particle solution", `W:r2:particle-equation`).
Statement repair `Supplement repair P7` (docs/ISSUES.md): the solution is moreover filtered (`filtered`: some filtration
makes `W` Brownian and `X` adapted and progressive; the completed filtration of `(X₀, W)` is one). -/
structure MovParticleSetup {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (d : ℕ) (s q β : ℝ) (N : ℕ)
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ζ t => W t ζ) P
  sol : ∀ T : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s q β) T X₀ W X
  filtered : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
    IsWholeFilteredSolution P ℱ W' W X

/-- The preparations of S6.6 (S L4560-4564): `γ = 0` is the iid preparation `(μ⁰)^{⊗N}`, `γ > 0` the
modulated Gibbs preparation `Q_{N,γ}(μ⁰)`. -/
def MovPrepared (d : ℕ) (s : ℝ) (N : ℕ) (γ : ℝ) (μ0 : Measure (Euc d))
    (f : Measure (EucConfig d N)) : Prop :=
  (γ = 0 ∧ f = Measure.pi fun _ => μ0) ∨
    (0 < γ ∧ f = modulatedGibbs (rieszKernel d s) N γ μ0)

/-- The normalized second particle moment `N⁻¹ ∑_i |x_i|²`. -/
def movSecondMoment {N : ℕ} (X : EucConfig d N) : ℝ := (1 / (N : ℝ)) * ∑ i, ‖X i‖ ^ 2

/-- The conclusions of S6.6 for the preparations (S L4559-4571), uniform in `t ≥ 0`, for the particle
law `f_N^t = P∘(X_t)⁻¹` and the moving reference `Q_N^t = Q_{N,β}(μ^t)`, `μ^t = ρ^t dx`:
`H(f_N^t|Q_N^t) ≤ C N δ_N` (`W:r2mov:H-bound`), `E_{f_N^t}|F_N^g(X_N,μ^t)| ≤ C δ_N`
(`W:r2mov:F-bound`), `H(f_N^t|(μ^t)^{⊗N}) ≤ C N δ_N` (`W:r2mov:product-bound`),
`E_{f_N^t} e_N ≤ C o_N` (`e_N = F_N^g + o_N`, "in particular"), and the normalized second moment is
at most `C`.  Expectations of nonnegative quantities are lower integrals in `ℝ≥0∞` (no junk). -/
def MovParticleBounds (d : ℕ) (s q β C₀ C : ℝ) (ρ : ℝ → Euc d → ℝ) (N : ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    relEntropy (P.map (X t.toNNReal))
        (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t))) ≤
      ENNReal.ofReal (C * N * deltaN d s N) ∧
    ∫⁻ Z, ENNReal.ofReal |rieszModulatedEnergy d s Z (withDensityReal (ρ t))|
        ∂(P.map (X t.toNNReal)) ≤ ENNReal.ofReal (C * deltaN d s N) ∧
    relEntropy (P.map (X t.toNNReal)) (Measure.pi fun _ => withDensityReal (ρ t)) ≤
      ENNReal.ofReal (C * N * deltaN d s N) ∧
    ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (withDensityReal (ρ t)) + oN d s C₀ N)
        ∂(P.map (X t.toNNReal)) ≤ ENNReal.ofReal (C * oN d s C₀ N) ∧
    ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal C

section Entropy

variable {s : ℝ}

/-- Theorem 6.6 (S:W:thm:r2mov-entropy, TeX S L4552-4578).  Let `ρ^t` be one of the nonlinear
trajectories of Theorem 6.3 (see the module docstring), `f_N^t` the law of the canonical particle
solution in the quadratic potential at physical temperature `β` from an initial law `f_N^0`,
`Q_N^t = Q_{N,β}(μ^t)`.  There is `C₀` (the completion constant, chosen for the class: `e_N =
F_N^g + o_N ≥ 0` off collisions, S L5095-5099) such that, with constants `C` independent of `N, t` and
of the trajectory:
(1) `sup_{t≥0} H(f_N^t|Q_N^t) ≤ C{H(f_N^0|Q_N^0) + Nδ_N}` for every initial law
(`W:r2mov:entropy-general`);
(2) for the iid preparation `(μ⁰)^{⊗N}` and each fixed `γ > 0` and the preparation `Q_{N,γ}(μ⁰)`
(`C` may depend on `γ`): `MovParticleBounds` (the three displayed bounds, `E e_N ≤ C o_N`, bounded
normalized second moment);
(3) on every window of fixed length `T`, `E sup_{t∈[b,b+T]} N⁻¹∑|x_i(t)|² ≤ C_T` uniformly in the
window start `b ≥ 0` and `N` (same preparations).
Statement change M1b (2026-10-22): each of (1)-(3) is conditional on `GibbsEntropyContraction d s q β N` (relative entropy with respect to the invariant canonical
Gibbs law `ℙ_{N,β}` does not increase along the particle dynamics; the proof uses `H(f_N^t|ℙ_{N,β}) ≤ H(f_N^0|ℙ_{N,β})` for the a priori entropy and second-moment
localizations, S L4640-4650).  In (1) the initial law is arbitrary, which is why the contraction (and not mere invariance) is the right hypothesis.
Technical hypotheses: `N ≥ 2` (the rates are defined for `N ≥ 2`).  AMBIGUITY: the indices `(j,m)`
(S L4553-4554); the expected supremum is read as that of the normalized second moment
(S L4718-4737, the quantity bounded in the proof). -/
theorem mov_entropy (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        ∃ C₀ : ℝ,
          (∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
              0 ≤ rieszModulatedEnergy d s X (withDensityReal (ρ t)) + oN d s C₀ N) ∧
          (∃ C : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
            ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
            ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
            ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
              MovParticleSetup P d s q β N X₀ W X →
              ∀ t : ℝ, 0 ≤ t →
                relEntropy (P.map (X t.toNNReal))
                    (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ t))) ≤
                  ENNReal.ofReal C *
                    (relEntropy (P.map X₀)
                        (modulatedGibbs (rieszKernel d s) N β (withDensityReal (ρ 0))) +
                      ENNReal.ofReal (N * deltaN d s N))) ∧
          ∀ γ : ℝ, 0 ≤ γ →
            (∃ C : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
              ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
              ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
              ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
                [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
                (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
                MovParticleSetup P d s q β N X₀ W X →
                MovPrepared d s N γ (withDensityReal (ρ 0)) (P.map X₀) →
                MovParticleBounds d s q β C₀ C ρ N P X) ∧
            (∀ T : ℝ, 0 < T → ∃ CT : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
              ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
              ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
              ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
                [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
                (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
                MovParticleSetup P d s q β N X₀ W X →
                MovPrepared d s N γ (withDensityReal (ρ 0)) (P.map X₀) →
                ∀ b : ℝ, 0 ≤ b →
                  ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T),
                      ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤
                    ENNReal.ofReal CT) := by
  sorry

end Entropy


/-! ### S6.7 `W:lem:r2mov-global-adjoint` (S L4779-4794) -/

section GlobalAdjoint

variable {s : ℝ}

/-- Lemma 6.7 (S:W:lem:r2mov-global-adjoint, TeX S L4779-4794), stationary case (`ρ^t ≡ ρ_*`, `F_t = 0`).
Fix an integer `j ≥ 0` and an integer `M > d/2 + j + 5`.  There are `C, c > 0` such that for all
`0 ≤ r ≤ t` and every classical adjoint solution `f = U(·,t)φ` (terminal datum `φ`):
`‖∇U(r,t)φ‖_{C_b^j} ≤ C e^{-c(t-r)}(‖∇φ‖_{C_b^j} + ‖√ρ_* Πφ‖_{Σ^M})`,
`Πφ = φ - ∫φρ_*` (`W:r2mov:global-adjoint-decay`).  The constants are chosen before `t, r, φ`
(uniform over `0 ≤ r ≤ t`, independent of the support of `φ`).  No zeroth-order decay is asserted.
Technical hypotheses: `φ ∈ C^{j+1}` and `√ρ_*Πφ ∈ Σ^M` (so that the right side is the source's
finite quantity; for `∇φ ∉ C_b^j` the `C_b^j` norm is undefined); the adjoint solution is a
hypothesis (existence is Section S5). -/
theorem mov_global_adjoint_stationary (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (j M : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) :
    ∃ C c : ℝ, 0 < c ∧ ∀ (t : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ t →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ₀)) t φ f →
      ContDiff ℝ (j + 1) φ →
      MemOsc (M : ℝ) (fun x => Real.sqrt (ρ₀ x) * (φ x - ∫ y, φ y * ρ₀ y)) →
      ∀ r ∈ Set.Icc (0 : ℝ) t,
        ContDiff ℝ j (fun x => gradient (f r) x) ∧
        cbNormVecE j (fun x => gradient (f r) x) ≤
          ENNReal.ofReal (C * Real.exp (-c * (t - r))) *
            (cbNormVecE j (fun x => gradient φ x) +
              ENNReal.ofReal (oscNorm (M : ℝ)
                (fun x => Real.sqrt (ρ₀ x) * (φ x - ∫ y, φ y * ρ₀ y)))) := by
  sorry

/-- Lemma 6.7, nonlinear case (S L4780-4782 "along the small nonlinear trajectories above when
their initial regularity is taken larger than `M+4`"): for Theorem 6.3 with indices `(j', m)`,
`m > M + 4` (and `m > d/2 + j' + 6`), there are the constants of `MovNonlinearConclusion` and
`C, c > 0` (uniform over the class) such that the adjoint along `μ^t = ρ^t dx`
(`IsClassicalAdjointW` for `(quadraticGradientDyn d s q β).coeff ρ`) satisfies the same estimate
as in the stationary case.  AMBIGUITY: the index `j'` of the `C_b` part of Theorem 6.3 is not
specified in S L4780-4782 (any `j' ≥ 1`; the force regularity is governed by `m`).  Technical
hypotheses as in `mov_global_adjoint_stationary`. -/
theorem mov_global_adjoint_nonlinear (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (j M : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) (j' m : ℕ) (hj' : 1 ≤ j')
    (hm : (d : ℝ) / 2 + j' + 6 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ εstar r c₀ c' C' : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c' ∧ 0 < C' ∧
      MovNonlinearConclusion d s q β ρ₀ j' m εstar r c₀ c' C' ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j' m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
        ∀ (t : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ t →
          IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) t φ f →
          ContDiff ℝ (j + 1) φ →
          MemOsc (M : ℝ) (fun x => Real.sqrt (ρ₀ x) * (φ x - ∫ y, φ y * ρ₀ y)) →
          ∀ r' ∈ Set.Icc (0 : ℝ) t,
            ContDiff ℝ j (fun x => gradient (f r') x) ∧
            cbNormVecE j (fun x => gradient (f r') x) ≤
              ENNReal.ofReal (C * Real.exp (-c * (t - r'))) *
                (cbNormVecE j (fun x => gradient φ x) +
                  ENNReal.ofReal (oscNorm (M : ℝ)
                    (fun x => Real.sqrt (ρ₀ x) * (φ x - ∫ y, φ y * ρ₀ y)))) := by
  sorry

end GlobalAdjoint

/-! ### S6.8 `W:prop:r2mov-translation` (S L4864-4881) -/

section Translation

variable {s : ℝ}

/-- The shift `a_t = e^{-qt} a_0` (S L4860). -/
def movShift (q : ℝ) (a₀ : Euc d) (t : ℝ) : Euc d := Real.exp (-q * t) • a₀

/-- `T_a μ = (τ_a)_# μ`, `τ_a(x) = x + a` (S L4860). -/
def movTranslate (a : Euc d) (μ : Measure (Euc d)) : Measure (Euc d) := μ.map (fun x => x + a)

/-- Proposition 6.8 (S:W:prop:r2mov-translation, TeX S L4864-4881).  `g = |x|^{-s}` (`0 < s < d`) or
`-log|x|` (`s = 0`), `V = q|x|²/2`, `a_t = e^{-qt}a_0`, `β > 0`.
(1) If `Y_N` is a canonical particle solution (any initial law, driven by `W`), then
`x_i(t) = y_i(t) + a_t` is the solution with the translated initial configuration and the same
Brownian motions (`W:r2mov:particle-translation`).
(2) If `μ^t = ρ^t dx` solves the mean-field equation, so does `T_{a_t}μ^t`, i.e. the density
`x ↦ ρ^t(x - a_t)`.  (Added hypothesis, approved by the author after review: `ρ` is `(3,Λ)`-regular on `[0,T]`,
`IsRegularMFRd s 3 Λ T ρ`, as the main text requires of a regular solution; it is what makes the time-dependent weak
form available, `HRS.MH.mf_time_dependent_proof`.)
(3) For every preparation temperature `β₀ > 0`: `Q_{N,β₀}(T_aμ) = (τ_a^{⊗N})_# Q_{N,β₀}(μ)`
(`W:r2mov:Q-translation`), for probability measures `μ`.
(4) The modulated energy (original deleted diagonal, factor `1/2`) and the partition function
`K_{N,β₀}` are unchanged by the joint translation.
Technical hypotheses: `μ` a probability measure in (3), (4) (the standing setting of `Q_{N,β₀}(μ)`). -/
theorem mov_translation (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (a₀ : Euc d) :
    (∀ (N : ℕ) (T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (Y₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (Y : ℝ≥0 → Ω → EucConfig d N),
      IsWholeStrongSolution P (quadraticGradientDyn d s q β) T Y₀ W Y →
      IsWholeStrongSolution P (quadraticGradientDyn d s q β) T (fun ζ i => Y₀ ζ i + a₀) W
        (fun t ζ i => Y t ζ i + movShift q a₀ (t : ℝ))) ∧
    (∀ (T Λ : ℝ) (ρ : ℝ → Euc d → ℝ), HRS.Whole.AppendixA.IsRegularMFRd s 3 Λ T ρ →
      IsWholeMeanFieldSolution (quadraticGradientDyn d s q β) T ρ →
      IsWholeMeanFieldSolution (quadraticGradientDyn d s q β) T
        (fun t x => ρ t (x - movShift q a₀ t))) ∧
    (∀ (N : ℕ) (β₀ : ℝ), 0 < β₀ → ∀ (μ : Measure (Euc d)), IsProbabilityMeasure μ →
      modulatedGibbs (rieszKernel d s) N β₀ (movTranslate a₀ μ) =
        (modulatedGibbs (rieszKernel d s) N β₀ μ).map (fun X i => X i + a₀)) ∧
    (∀ (N : ℕ) (β₀ : ℝ) (μ : Measure (Euc d)), IsProbabilityMeasure μ →
      (∀ X : EucConfig d N, rieszModulatedEnergy d s (fun i => X i + a₀) (movTranslate a₀ μ) =
        rieszModulatedEnergy d s X μ) ∧
      gibbsNormalizer (rieszKernel d s) N β₀ (movTranslate a₀ μ) =
        gibbsNormalizer (rieszKernel d s) N β₀ μ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N T Ω _ P Y₀ W Y h
    exact movtr_strong_translate P s q β T Y₀ W Y h a₀
  · -- Clause (2) (time-dependent test functions): see the report; open.
    sorry
  · intro N β₀ _ μ hμ
    exact movtr_modulatedGibbs_translate (rieszKernel d s) N β₀ μ a₀
  · intro N β₀ μ hμ
    exact ⟨fun X => movtr_modulatedEnergy_translate (rieszKernel d s) μ a₀ X,
      movtr_gibbsNormalizer_translate (rieszKernel d s) N β₀ μ a₀⟩

/-! ### S6.9 `W:cor:r2mov-moving-reference` (S L4902-4921) -/

/-- The translated equilibrium density `ρ^t(x) = ρ_*(x - a_t)` (`μ^t = T_{a_t}μ_*`). -/
def movTranslatedDensity (q : ℝ) (a₀ : Euc d) (ρ₀ : Euc d → ℝ) (t : ℝ) (x : Euc d) : ℝ :=
  ρ₀ (x - movShift q a₀ t)

/-- `∂_i` of a function of the configuration along coordinate `k` of particle `i`. -/
def movPartial {N : ℕ} (f : EucConfig d N → ℝ) (i : Fin N) (k : Fin d) (X : EucConfig d N) : ℝ :=
  deriv (fun τ : ℝ => f (Function.update X i (X i + τ • EuclideanSpace.single k 1))) 0

/-- The forward Kolmogorov operator of the particle system,
`𝓛_N^* f = ∑_i [ν Δ_{x_i} f + div_{x_i}(f (qx_i + N⁻¹∑_{j≠i}∇g(x_i-x_j)))]`, `ν = β⁻¹`
(`dx_i = -(qx_i + N⁻¹∑_{j≠i}∇g(x_i-x_j))dt + √(2/β)dB_i`). -/
def movFP (d : ℕ) (s q β : ℝ) (N : ℕ) (f : EucConfig d N → ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ k, (β⁻¹ * movPartial (movPartial f i k) i k X +
    movPartial (fun Y => f Y * (q * Y i k + (1 / (N : ℝ)) *
      ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k)) i k X)

/-- The Lebesgue density `q_N^t` of `Q_N^t = Q_{N,β}(μ^t)`, `μ^t = ρ^t dx`:
`K_{N,β}(μ^t)⁻¹ e^{-βN F_N^g(X_N,μ^t)} ∏_i ρ^t(x_i)`. -/
def movQDensity (d : ℕ) (s β : ℝ) (N : ℕ) (ρ : Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  (gibbsNormalizer (rieszKernel d s) N β (withDensityReal ρ))⁻¹ *
    Real.exp (-β * N * rieszModulatedEnergy d s X (withDensityReal ρ)) * ∏ i, ρ (X i)

/-- Corollary 6.9 (S:W:cor:r2mov-moving-reference, TeX S L4902-4921).  Let `μ_*` be the thermal
equilibrium for `V = q|x|²/2` and `μ^t = T_{a_t}μ_*` (`ρ^t = ρ_*(·-a_t)`).  Then:
(1) `u^t(x) = ν∇log ρ^t + qx + ∇g*ρ^t = q a_t` (`W:r2mov:translation-velocity`), and
`∂_tρ^t = div(ρ^t u^t)` holds pointwise;
(2) `q_N^t` is the Lebesgue density of `Q_N^t = Q_{N,β}(μ^t)`, which is exactly the law at time `t` of the
particle solution with initial law `Q_N^0`;
(3) the source `(𝓛_N^*q_N^t - ∂_tq_N^t)/q_N^t` is identically zero, i.e. `∂_tq_N^t = 𝓛_N^*q_N^t`
off collisions (and `q_N^t > 0`);
(4) for any initial law, `H(f_N^t|Q_N^t) ≤ H(f_N^0|Q_N^0)`, `t ≥ 0`
(`W:r2mov:entropy-contraction`; it contains the iid preparation from `T_{a_0}μ_*` and the preparations
`Q_{N,β₀}(T_{a_0}μ_*)`, `β₀ > 0`; the non-claim "for `β₀ ≠ β` the latter need not be the canonical
invariant law" is prose).
Statement change M1 (2026-10-22): the dynamical part of (2) (the law at time `t` of the solution started from `Q_N^0`) is
conditional on `GibbsInvariant d s q β N`; the density identity in (2), and (1), (3), are unconditional.
Statement change M1b (2026-10-22): clause (4) (entropy contraction against the moving reference) is conditional on `GibbsEntropyContraction d s q β N`
(proof: translate by S6.8(1) to the process `X - movShift q a₀ ·` and apply the contraction against the invariant `ℙ_{N,β}`; the initial law is arbitrary, so
invariance alone would not suffice).  Proof of (2): translate by S6.8(1) (`mov_translation_proof`) to a
solution started from `ℙ_{N,β}`, apply the hypothesis, translate back (`movtr_modulatedGibbs_translate`).
Technical hypotheses: `N ≥ 1`.  The positivity and smoothness of `ρ_*` used in (1), (3) are the
conclusions of S3.4/S4.1 (not hypotheses). -/
theorem mov_moving_reference (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (a₀ : Euc d) :
    (∀ t : ℝ, 0 ≤ t → ∀ x : Euc d,
      movU d s q β (movTranslatedDensity q a₀ ρ₀ t) x = q • movShift q a₀ t ∧
      HasDerivAt (fun τ => movTranslatedDensity q a₀ ρ₀ τ x)
        (movDiv (fun y => movTranslatedDensity q a₀ ρ₀ t y •
          movU d s q β (movTranslatedDensity q a₀ ρ₀ t) y) x) t) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t →
      modulatedGibbs (rieszKernel d s) N β (withDensityReal (movTranslatedDensity q a₀ ρ₀ t)) =
        (volume : Measure (EucConfig d N)).withDensity (fun X =>
          ENNReal.ofReal (movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ t) X)) ∧
      (GibbsInvariant d s q β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        MovParticleSetup P d s q β N X₀ W X →
        P.map X₀ = modulatedGibbs (rieszKernel d s) N β
          (withDensityReal (movTranslatedDensity q a₀ ρ₀ 0)) →
        P.map (X t.toNNReal) = modulatedGibbs (rieszKernel d s) N β
          (withDensityReal (movTranslatedDensity q a₀ ρ₀ t)))) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      0 < movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ t) X ∧
      HasDerivAt (fun τ => movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ τ) X)
        (movFP d s q β N (movQDensity d s β N (movTranslatedDensity q a₀ ρ₀ t)) X) t) ∧
    (∀ N : ℕ, 1 ≤ N → GibbsEntropyContraction d s q β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      MovParticleSetup P d s q β N X₀ W X → ∀ t : ℝ, 0 ≤ t →
        relEntropy (P.map (X t.toNNReal))
            (modulatedGibbs (rieszKernel d s) N β (withDensityReal (movTranslatedDensity q a₀ ρ₀ t))) ≤
          relEntropy (P.map X₀)
            (modulatedGibbs (rieszKernel d s) N β (withDensityReal (movTranslatedDensity q a₀ ρ₀ 0)))) := by
  sorry

/-! ### S6.10 `W:prop:r2mov-translation-relax` (S L4936-4952) -/

/-- The Sobolev norm `‖f‖_{W^{k,p}} = ∑_{i≤k} ‖ ‖D^if‖ ‖_{L^p}` (`p ∈ [1,∞]`), valued in `ℝ≥0∞`. -/
def movWNormE (k : ℕ) (p : ℝ≥0∞) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1), eLpNorm (fun x => ‖iteratedFDeriv ℝ i f x‖) p volume

/-- Proposition 6.10 (S:W:prop:r2mov-translation-relax, TeX S L4936-4952).  Suppose the thermal density
`ρ_*` is smooth with Gaussian tails (hypotheses `hsmooth`, `hgauss`: every derivative is bounded by
`C e^{-c|x|²}`; the polynomial factor of the logarithmic case is absorbed by decreasing `c`).  For `ρ^t =
ρ_*(·-a_t)`: for all `k, ℓ ≥ 0`, `1 ≤ p ≤ ∞` there is `C_{k,ℓ,p,a_0}` with
`‖⟨x⟩^ℓ(ρ^t-ρ_*)‖_{W^{k,p}} ≤ C|a_0|e^{-qt}`, `t ≥ 0` (`W:r2mov:translation-smooth`); a common Gaussian
moment `sup_{t≥0}∫e^{b|x|²}ρ^t < ∞` for some `b > 0`; `∫_0^∞‖u^t‖_{C_b^k}dt = |a_0|` for every `k`
(`u^t` as in S6.3); the free energy gap `𝓕_β(μ^t) - 𝓕_β(μ_*) = (q/2)|a_0|²e^{-2qt}`
(`W:r2mov:translation-free-energy`, both free energies finite).  The "weighted derivative bounds" of
S L4946 are the first display (`ℓ, k` arbitrary). -/
theorem mov_translation_relax (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀)
    (hsmooth : ContDiff ℝ ∞ ρ₀)
    (hgauss : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ₀ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (a₀ : Euc d) :
    (∀ (k ℓ : ℕ) (p : ℝ≥0∞), 1 ≤ p → ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      movWNormE k p (fun x => movBracket x ^ ℓ * (movTranslatedDensity q a₀ ρ₀ t x - ρ₀ x)) ≤
        ENNReal.ofReal (C * ‖a₀‖ * Real.exp (-q * t))) ∧
    (∃ b : ℝ, 0 < b ∧ ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ x, ENNReal.ofReal (Real.exp (b * ‖x‖ ^ 2) * movTranslatedDensity q a₀ ρ₀ t x) ≤
        ENNReal.ofReal C) ∧
    (∀ k : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
      cbNormVecE k (movU d s q β (movTranslatedDensity q a₀ ρ₀ t)) = ENNReal.ofReal ‖a₀‖) ∧
    (∀ t : ℝ, 0 ≤ t →
      HasFiniteFreeEnergy (rieszKernel d s) (confinement q) (movTranslatedDensity q a₀ ρ₀ t) ∧
      HasFiniteFreeEnergy (rieszKernel d s) (confinement q) ρ₀ ∧
      freeEnergy (rieszKernel d s) (confinement q) β (movTranslatedDensity q a₀ ρ₀ t) -
          freeEnergy (rieszKernel d s) (confinement q) β ρ₀ =
        q / 2 * ‖a₀‖ ^ 2 * Real.exp (-2 * q * t)) := by
  have hd1 : 1 ≤ d := by omega
  have hρc : Continuous ρ₀ := hsmooth.continuous
  obtain ⟨C0, c0, hC0, hc0, h0, _⟩ := movtr_gauss01 hgauss
  have hshift : ∀ t : ℝ, ‖movShift q a₀ t‖ = ‖a₀‖ * Real.exp (-q * t) := by
    intro t
    unfold movShift
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  have hshift_le : ∀ t : ℝ, 0 ≤ t → ‖movShift q a₀ t‖ ≤ ‖a₀‖ := by
    intro t ht
    rw [hshift]
    have : Real.exp (-q * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc ‖a₀‖ * Real.exp (-q * t) ≤ ‖a₀‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖a₀‖ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k ℓ p hp
    obtain ⟨C, hC⟩ := movtr_sobolev hd1 hsmooth hgauss k ℓ p hp ‖a₀‖
    refine ⟨C, fun t ht => ?_⟩
    have h := hC (movShift q a₀ t) (hshift_le t ht)
    unfold movWNormE
    simp only [movTranslatedDensity]
    refine h.trans (le_of_eq ?_)
    rw [hshift]
    congr 1
    ring
  · obtain ⟨b, hb, C, hC⟩ := movtr_gauss_moment hd1 hc0 hρc h0 ‖a₀‖
    refine ⟨b, hb, C, fun t ht => ?_⟩
    simpa only [movTranslatedDensity] using hC (movShift q a₀ t) (hshift_le t ht)
  · intro k
    have hforce := fun y => movtr_thermal_force hd hs0 hsd hβ hρ hsmooth hgauss y
    have hU : ∀ t : ℝ, movU d s q β (movTranslatedDensity q a₀ ρ₀ t) =
        fun _ => q • movShift q a₀ t := by
      intro t
      funext x
      exact movtr_movU_translate s q β ρ₀ hforce (movShift q a₀ t) x
    simp_rw [hU, movtr_cbNormVecE_const]
    simpa only [movShift] using movtr_lintegral_decay hq a₀
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := movtr_freeEnergy_translate hq hρ (movShift q a₀ t)
    refine ⟨h1, h2, ?_⟩
    have e : movTranslatedDensity q a₀ ρ₀ t = fun x => ρ₀ (x - movShift q a₀ t) := rfl
    rw [e, h3, hshift, mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf

end Translation


/-! ### S6.11 `W:cor:r2-translated-particle-paths` (S L5189-5207) -/

section Paths

variable {s : ℝ}

/-- Corollary S6.11 (S:W:cor:r2-translated-particle-paths, TeX S L5189-5207), first paragraph.
Fix `b ∈ ℝ^d`, `b_t = e^{-at}b` (`a = q` the confinement constant), `ϑ_t = (x ↦ x + b_t)_#μ`,
`μ = μ_β` the thermal equilibrium.  In Theorem S2.1(ii) (S L368-386; `0 ≤ s < 2d/3`, `m = 24d+240`,
`T < ∞`, window starts `a₀ ≥ 0`) replace the two preparations by `ϑ_0^{⊗N}` (`γ = 0`) and
`Q_{N,γ}(ϑ_0)` (`γ > 0`) and center the fluctuations at `ϑ_t`: `η_N^t = √N(μ_N^t - ϑ_t)`.  Then, with
`C = C(b)` and the completion `C₀` chosen first, for the particle path from the preparation and any
Gaussian process `Z` solving the linearized equation along `ϑ_t` (noise level `β⁻¹`) with the
initial covariance `C_γ(φ,ψ) = ⟨P_{ϑ_0}φ, (I+γK_{ϑ_0})⁻¹P_{ϑ_0}ψ⟩_{L²(ϑ_0)}` of the translated
preparation (`susceptibilityCov` at `ϑ_0, γ`; at `γ = 0` it is `ϑ_0(φψ) - ϑ_0(φ)ϑ_0(ψ)`),
`d_2^𝒳(η_N^{a₀+·}, Z^{a₀+·}) ≤ C(√Nδ_N + w_N + i_N)`,
`W_1^𝒳(η_N^{a₀+·}, Z^{a₀+·}) ≤ C(√Nδ_N + √w_N + j_N)` with `i_N, j_N` as in S2.1(ii)
(`iN`, `jN`, with `β₀ = γ`), uniformly in `a₀ ≥ 0`.
Statement change M1b (2026-10-22): the second conjunct is conditional on `GibbsEntropyContraction d s q β N` (the untranslated dynamics; used through S2.1(ii) at `ε = 0`).
Technical: `N ≥ 2`; measurability of the two
path maps is part of the conclusion (so that the laws are genuine). -/
theorem mov_translated_prepared (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (T : ℝ) (hT : 0 < T) (b : Euc d) (γ : ℝ) (hγ : 0 ≤ γ)
    (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ C₀ C : ℝ,
      (∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        0 ≤ rieszModulatedEnergy d s X (withDensityReal (movTranslatedDensity q b ρ₀ t)) +
          oN d s C₀ N) ∧
      ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction d s q β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        MovParticleSetup P d s q β N X₀ W X →
        MovPrepared d s N γ (withDensityReal (movTranslatedDensity q b ρ₀ 0)) (P.map X₀) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
          (∀ T' : ℝ, IsLinearGaussianEvolutionW P'
            ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρ₀))
            (wholeSpaceIndex d) β⁻¹ T'
            (susceptibilityCov (rieszKernel d s)
              (withDensityReal (movTranslatedDensity q b ρ₀ 0)) γ) Z) →
          ∀ a₀ : ℝ, 0 ≤ a₀ →
            AEMeasurable (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X
              (movTranslatedDensity q b ρ₀)) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
            smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X
                (movTranslatedDensity q b ρ₀)))
                (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
              C * (Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s γ N) ∧
            wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X
                (movTranslatedDensity q b ρ₀)))
                (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
              ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N +
                Real.sqrt (localizationRate d s C₀ N) + jN d s γ N)) := by
  sorry

/-- Corollary S6.11, second paragraph (S L5203-5205): if the initial law is the translate of
`ℙ_{N,β}` (`(x ↦ x + b)_#` of the canonical Gibbs law, equivalently `Q_{N,β}(ϑ_0)`), exact centering at
the moving first marginal `(x ↦ x + b_t)_#m_N` (= the actual first marginal `E μ_N^t` of the translated
process) gives the rates of S2.1(i) (S L353-361) throughout `0 ≤ s < d`:
`d_2^𝒳(ζ_N, Z) ≤ C(√δ_N + w_N)`, `W_1^𝒳(ζ_N, Z) ≤ C(δ_N^{3/20} + √w_N)`.  AMBIGUITY: the comparator is
not named in the source; it is the push-forward `T_{b_t}Z_β` of the stationary Gaussian field
(S L5212-5214), i.e. the linearized Gaussian process along `ϑ_t` with the susceptibility initial
covariance at `(ϑ_0, β)` (the same as in the first paragraph with `γ = β`).  The window is `a₀ = 0`
as in S2.1(i).  The completion constant `C₀` is the one for the stationary reference `μ_β`.  "Not
called stationary" is prose.
Statement change M1 (2026-10-22): the second conjunct is conditional on `GibbsInvariant d s q β N` (the stationary law of the
untranslated process; used through S2.1(i)). -/
theorem mov_translated_stationary (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (T : ℝ) (hT : 0 < T) (b : Euc d)
    (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ C₀ C : ℝ,
      (∀ N : ℕ, 2 ≤ N → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        0 ≤ rieszModulatedEnergy d s X (withDensityReal ρ₀) + oN d s C₀ N) ∧
      ∀ N : ℕ, 2 ≤ N → GibbsInvariant d s q β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        MovParticleSetup P d s q β N X₀ W X →
        P.map X₀ = (canonicalGibbs (rieszKernel d s) (confinement q) N β).map
          (fun Y i => Y i + b) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
          (∀ T' : ℝ, IsLinearGaussianEvolutionW P'
            ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρ₀))
            (wholeSpaceIndex d) β⁻¹ T'
            (susceptibilityCov (rieszKernel d s)
              (withDensityReal (movTranslatedDensity q b ρ₀ 0)) β) Z) →
          AEMeasurable (zetaPathW (wholeSpaceIndex d) T 0 P X) P ∧
          AEMeasurable (processWindow (wholeSpaceIndex d) T 0 Z) P' ∧
          smoothDist 2 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
              (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
            C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ∧
          wassersteinE 1 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
              (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
            ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
              Real.sqrt (localizationRate d s C₀ N))) := by
  sorry

end Paths

end HRS.Whole
