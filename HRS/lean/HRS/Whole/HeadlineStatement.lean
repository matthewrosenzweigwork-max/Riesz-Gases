import HRS.Whole.Orbits

/-!
# Whole-space preparations, field remainder, varying-temperature paths, and the headline theorem
(package S-DYN-01): Sections S3.2, S5.3, S5.6 and S2.1

Source: HRS whole-space supplement (S).

* S3.2 `W:cor:euclidean-preparations` (S lines 814-845);
* S3.6 `W:rem:r2-log-scope` (S lines 1968-1977): **no_formal_content** (a scope remark: it says
  which hypotheses the (already stated) logarithmic static theorem S3.5 uses and that it supplies no
  adjoint estimate by itself; it contains no further mathematical claim);
* S5.3 `W:r2:field-remainder` (3466-3487);
* S5.6 `W:thm:r2-general-paths` (3971-3997);
* S2.1 `H:thm:whole-space` (348-396).

## Dependencies of S2.1 (reported to the orchestrator)

`H:thm:whole-space` (S L348-396) depends on later rows of the supplement:
* the nonlinear relaxation theorem S6.3 `W:thm:r2mov-nonlinear` (S L4345-4371), which supplies the
  solution `μ^t` ("the resulting nonlinear mean-field solution") and its comparability/decay bounds,
  encoded here as the hypothesis predicate `IsResultingSolution` (the constants of S6.3 are
  quantified before the constants of S2.1);
* S9.9/S10.x/S11.x (the static and window Edgeworth expansions) for part (iii), whose coordinate
  formula `H:eq:cubic-formula` is `cubicFormula`;
* the critical-case Proposition `S:prop:critical-whole` (S8), mentioned in (i) at `s = d/2`, which is
  NOT part of this statement (it gives a *stronger* bound at `s = d/2`);
* S5.6 (this file) and S4.5-S4.7 (`HRS.Whole.quadratic_static_field_osc`, the fixed-time sharper
  smooth estimate `C√δ_N` mentioned at S L379-382, is that existing statement).

## Representation decisions

* The particle path law is that of a strong solution `X` of the whole-space particle system
  (`IsWholeStrongSolution`) on a probability space with an independent vector Brownian motion,
  with a prescribed initial law; every statement is "for every such realization".  `C^k`-regularity,
  existence and the invariant laws are inputs, not asserted.
* `ε_N`, `E_{N,p}`, `ε_{N,p}` are `ℝ≥0∞`-valued (`⊤` when the moment is infinite), so the finiteness
  hypotheses of the source ("stated initial and energy moments") are not needed: a bound with an
  infinite right side is trivial.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-! ### S3.2 -/

section Preparations

variable {s : ℝ}

/-- Corollary S3.2 (S:W:cor:euclidean-preparations, TeX S L814-845), first assertion
`W:eq:euclidean-preparation-bounds` (L814-820, 833-835): under the hypotheses of S3.1
(`d ≥ 2`, `0 ≤ s < d`, `μ = ρdx` a probability measure with `‖ρ‖_∞ ≤ M` and, for `s = 0`,
`∫log(2+|x|)dμ ≤ L`) and for fixed `b, b₀ > 0`:
`H(μ^{⊗N} | Q_{N,b}^g) + H(Q_{N,b₀}^g | Q_{N,b}^g) ≤ C N δ_N`, `N ≥ 2`; `C` depends on
`d, s, M, L, b, b₀` only (quantified before `ρ`).  Relative entropies are `ℝ≥0∞`-valued
(finiteness is part of the claim). -/
abbrev EuclideanPreparationsBoundsStatement : Prop :=
  ∀ {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M L b b₀ : ℝ)
    (hb : 0 < b) (hb₀ : 0 < b₀),
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
        relEntropy (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) +
          relEntropy (modulatedGibbs (rieszKernel d s) N b₀ (withDensityReal ρ))
            (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * N * deltaN d s N)

/-- Corollary S3.2 (S:W:cor:euclidean-preparations, TeX S L814-845), stationary-reference
transfer (L821-845): suppose `μ = ρdx` (as in S3.1)
is a thermal equilibrium measure for a confining potential `V` and inverse temperature `b`
(`IsThermalDensity g V b ρ`, the thermal equation), and that the canonical gradient particle
semigroup (the whole-space particle system with `M = -1`, potential `V`, `ν = b⁻¹`) has invariant law
`Q_{N,b}^g(μ)` (hypothesis `hInv`: started from `Q_{N,b}^g(μ)` its time marginals equal
`Q_{N,b}^g(μ)`).  For either initial law `μ^{⊗N}` or `Q_{N,b₀}^g` the actual time marginal `f_N^t`
satisfies, for every `t ≥ 0`: (1) `H(f_N^t | Q_{N,b}^g(μ)) + H(f_N^t | μ^{⊗N}) ≤ C N δ_N`
(`W:eq:euclidean-stationary-entropy`); (2) `E_{f_N^t}|μ_N(a) - μ(a)| ≤ C‖a‖_∞√δ_N` for every
bounded measurable `a` (`W:eq:euclidean-linear-bound`); (3)
`E_{f_N^t}|𝖢_N(v;μ)| ≤ C‖∇v‖_∞ δ_N` for every globally Lipschitz `v` (`‖∇v‖_∞` is its Lipschitz
constant; the vector field may grow linearly), `𝖢_N(v;μ) = 2𝖥_N^{h_v}(X_N,μ) = Comm_N(v;X_N,μ)`
(`W:eq:euclidean-comm-bound`).  `C` as in the first assertion.  Technical hypothesis: the
initial configuration is independent of the Brownian motion (the usual setting of a strong
solution), and `T` is any finite horizon with `t ≤ T`. -/
abbrev EuclideanPreparationsStationaryStatement : Prop :=
  ∀ {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (M L b b₀ : ℝ) (hb : 0 < b) (hb₀ : 0 < b₀),
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (withDensityReal ρ) L) → ∀ V : Euc d → ℝ,
      IsThermalDensity (rieszKernel d s) V b ρ → ∀ N : ℕ, 2 ≤ N →
      (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (T : ℝ) (X₀' : Ω' → EucConfig d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d))
          (X' : ℝ≥0 → Ω' → EucConfig d N), IsVectorBrownian P' W' →
          IndepFun X₀' (fun ζ t => W' t ζ) P' →
          law P' X₀' = modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ) →
          IsWholeStrongSolution P' (⟨s, -1, V, b⁻¹⟩ : WholeDyn d) T X₀' W' X' →
          ∀ t : ℝ≥0, (t : ℝ) ≤ T →
            law P' (X' t) = modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
        (law P X₀ = Measure.pi (fun _ : Fin N => withDensityReal ρ) ∨
          law P X₀ = modulatedGibbs (rieszKernel d s) N b₀ (withDensityReal ρ)) →
        IsWholeStrongSolution P (⟨s, -1, V, b⁻¹⟩ : WholeDyn d) T X₀ W X →
        ∀ t : ℝ≥0, (t : ℝ) ≤ T →
          (relEntropy (law P (X t)) (modulatedGibbs (rieszKernel d s) N b (withDensityReal ρ)) +
            relEntropy (law P (X t)) (Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
              ENNReal.ofReal (C * N * deltaN d s N)) ∧
          (∀ (a : Euc d → ℝ) (A : ℝ), Measurable a → (∀ x, |a x| ≤ A) →
            Integrable (fun ζ => |pair (empirical (X t ζ)) a - pair (withDensityReal ρ) a|) P ∧
            ∫ ζ, |pair (empirical (X t ζ)) a - pair (withDensityReal ρ) a| ∂P ≤
              C * A * Real.sqrt (deltaN d s N)) ∧
          (∀ (v : Euc d → Euc d) (Λ : ℝ≥0), LipschitzWith Λ v →
            Integrable (fun ζ => |commN d s v (X t ζ) (withDensityReal ρ)|) P ∧
            ∫ ζ, |commN d s v (X t ζ) (withDensityReal ρ)| ∂P ≤ C * Λ * deltaN d s N)

end Preparations

/-! ### S5.3 -/

/-- The `α`-th Hermite coordinate of the instantaneous nonlinear forcing at time `r` for the terminal
time `t`: `D_μ(h_{U_{t-r}φ_α})(X_N^r)`, `h_f = (∇f(x)-∇f(y))·∇g(x-y)`,
`D_μ(h) = ∬_{x≠y} h d(μ_N-μ)^{⊗2}` (no factor `1/2`, S lines 3455-3461), with the adjoint evolution
`U_{t-r} = propagatorW C r t` of the coefficients `C`, and `φ_α = λ_α^{-m/2} h_α`. -/
def commForcing {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (s m : ℝ) (μ : Measure (Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) (α : MultiIndex d) (t r : ℝ) (ζ : Ω) : ℝ :=
  centeredPairFunctional
    (commutatorKernel d s (fun x => gradient (propagatorW C r t (oscTestFun m α)) x))
    (X (Real.toNNReal r) ζ) μ

/-- Proposition S5.3 (S:W:r2:field-remainder, TeX S L3466-3487), first assertion: in the setting of
S5.1 (`d ≥ 2`, `0 ≤ s < d`, quadratic potential, `ρ` a Schwartz probability density, gradient
dynamics `M = -1` along the time-independent reference `μ = ρ dx`; indices `k > d/2 + 6`,
`J = 2k+2d+20`, `m > J+3d+4`), suppose under the actual time marginals that
`sup_{r≤T} E|D_μ(h_f)| ≤ C_A δ_N ‖D²f‖_∞` for every `f ∈ C_b²` (`W:r2:pressure-input`).  Then the
simultaneous Duhamel remainder satisfies
`E sup_{t≤T} ‖(-(√N/2)∫_0^t D_μ(h_{U_{t-r}φ_j})(X_N^r) dr)_j‖_{ℓ²} ≤ C_T √N δ_N`
(`W:r2:field-remainder-L1`), `C_T` independent of `N` (depends on `C_A` and the data).  The
pathwise time integrals exist (a.s.; part of the conclusion).  `U_{t-r}` is the classical adjoint
evolution (`propagatorW`) of the quadratic-gradient dynamics with the stationary reference. -/
abbrev FieldRemainderStatement : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : IsSchwartzDensity ρ) (CA : ℝ),
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N), IsVectorBrownian P W →
      IsWholeStrongSolution P (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) T X₀ W X →
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ f : Euc d → ℝ, MemCb 2 f →
        Integrable (fun ζ => |centeredPairFunctional (commutatorKernel d s (fun x => gradient f x))
            (X (Real.toNNReal r) ζ) (withDensityReal ρ)|) P ∧
        ∫ ζ, |centeredPairFunctional (commutatorKernel d s (fun x => gradient f x))
            (X (Real.toNNReal r) ζ) (withDensityReal ρ)| ∂P ≤
          CA * deltaN d s N * ⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) →
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntegrableOn (fun r => commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
          s m (withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
              s m (withDensityReal ρ) X α t r ζ)) ∂P ≤
        ENNReal.ofReal (CT * Real.sqrt N * deltaN d s N)

/-- Proposition S5.3 (S:W:r2:field-remainder, TeX S L3466-3487), centered assertion
(L3480-3487, `W:r2:centered-input`): if instead the
actual particle law is stationary and `N Var[D_μ(h_f)] ≤ C_A δ_N ‖D²f‖²_∞` for every `f ∈ C_b²`, the
same centered remainder, with `D_μ - E D_μ`, is bounded in `L²(C_tB_m)` by `C_T √δ_N`:
`(E sup_{t≤T}‖(-(√N/2)∫_0^t (D_μ - E D_μ)(h_{U_{t-r}φ_j})(X_N^r) dr)_j‖²_{ℓ²})^{1/2} ≤ C_T√δ_N`.
Variances are `evariance` (`ℝ≥0∞`, includes square integrability). -/
abbrev FieldRemainderCenteredStatement : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ)
    (hk : (d : ℝ) / 2 + 6 < k) (m : ℝ) (hm : ((2 * k + 2 * d + 20 : ℕ) : ℝ) + 3 * d + 4 < m)
    (T ν : ℝ) (hT : 0 ≤ T) (hν : 0 < ν) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ)
    (hρ : IsSchwartzDensity ρ) (CA : ℝ),
    ∃ CT : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → EucConfig d N), IsVectorBrownian P W →
      IsWholeStrongSolution P (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) T X₀ W X →
      (∀ t ∈ Set.Icc (0 : ℝ) T, law P (X (Real.toNNReal t)) = law P (X 0)) →
      (∀ f : Euc d → ℝ, MemCb 2 f →
        N * evariance (fun ζ => centeredPairFunctional
            (commutatorKernel d s (fun x => gradient f x)) (X 0 ζ) (withDensityReal ρ)) P ≤
          ENNReal.ofReal (CA * deltaN d s N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2)) →
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        IntegrableOn (fun r => commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
          s m (withDensityReal ρ) X α t r ζ) (Set.Icc 0 t)) ∧
      (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
          -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
            (commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
                s m (withDensityReal ρ) X α t r ζ -
              ∫ ζ', commForcing ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ))
                s m (withDensityReal ρ) X α t r ζ' ∂P))) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (CT * Real.sqrt (deltaN d s N))

/-! ### S5.6 -/

/-- Theorem S5.6 (S:W:thm:r2-general-paths, TeX S L3971-3997): quantitative whole-field paths at
varying temperature.  For a setup `S` of Section S5 (`WholeSetup b`, standing constraints
`WholeBounds.Valid`): `Ξ_N = σ_N(μ_N - ρ_N)` and `Y_N` the linearized process with initial field
`a_N η_N⁰` (a random functional `η₀` coupled with the particle initial configuration), noise factor
`q_N` and coefficients `ρ_N, ν_N`, one has on `𝒴 = C([0,T];B_m)`:
`d_{C_b²}(Ξ_N,Y_N) ≤ C_T(a_N ε_{N,1} + σ_N E_{N,1} + q_N w_N)`,
`W_1(Ξ_N,Y_N) ≤ C_T(a_N ε_{N,1} + σ_N E_{N,1} + √(q_N w_N))`,
`W_2(Ξ_N,Y_N) ≤ C_T(a_N ε_{N,2} + σ_N E_{N,2} + √(q_N w_N))`,
`w_N = inf_{R≥1}{R^{d/2}(N^{-1/d} + √E_{N,1}) + (1+M₂)R^{-2}}` (`generalLocalizationRate`),
`M₂` any bound for the actual and mean-field second moments on `[0,T]`.  `C_T` is independent of
`N`, of the setup within the bounds `b`, of `M₂` and of the realization.  The smooth metric is
`smoothDist 2` (sum of the function and first two derivative sup norms), `W_p` use the sup norm
(`OscPath`).  At zero noise (`β_N = ∞`, `q_N = 0`) the covariance terms vanish exactly (they are
`q_N w_N` and `√(q_N w_N)`).  A.e. measurability of both path maps (`AEMeasurable` with respect to `P`) is part of the
conclusion (so the laws are not junk; `Measurable` is false on a non-complete σ-algebra).  The noise of `Y_N` is not required independent of the particle initial data:
the three quantities depend only on the laws of `Ξ_N` and `Y_N`.  Technical hypotheses: `N ≥ 2`;
the particle process is a strong solution whose initial data `(X₀, η₀)` are independent of the
Brownian motion (the "initial coupling" is independent of the noise).  The second-moment bound `M₂`
is stated in `ℝ≥0∞` (`E μ_N^t(|x|²) ≤ M₂`, `ρ_N^t(|x|²) ≤ M₂`).  Statement repairs P6, P7, P8, P10
(docs/ISSUES.md, `Supplement repair`): `C_T` may depend on the completion constant `C₀ = b.C₀ ≥ C₀min` (all other
bounds those of `b₀`); the strong solution is moreover filtered (`IsWholeFilteredSolution` for some filtration);
`OscAdjointInput` (Duhamel identity for the orbit features, to be derived from `UlAdjointInput`, temporary
hypothesis); `AEMeasurable`. -/
abbrev GeneralPathsStatement : Prop :=
  ∀ {d : ℕ} (b₀ : WholeBounds d) (hb : b₀.Valid),
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ S : WholeSetup b, ∀ (N : ℕ), 2 ≤ N →
      OscAdjointInput (S.coeff N) b.m b.T → ∀ (M₂ : ℝ)
      {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)), IsVectorBrownian P W →
      ∀ X : ℝ≥0 → Ω → EucConfig d N, IsWholeStrongSolution P (S.dyn N) b.T X₀ W X →
      (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
        IsWholeFilteredSolution P ℱ W' W X) →
      ∀ η₀ : Ω → (Euc d → ℝ) → ℝ,
      IndepFun (fun ζ => (X₀ ζ, η₀ ζ)) (fun ζ t => W t ζ) P →
      (∀ t ∈ Set.Icc (0 : ℝ) b.T,
        ∫⁻ ζ, ENNReal.ofReal (pair (empirical (X (Real.toNNReal t) ζ)) (fun x => ‖x‖ ^ 2)) ∂P ≤
          ENNReal.ofReal M₂ ∧
        ENNReal.ofReal (pair (withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
          ENNReal.ofReal M₂) →
      ∀ Y : ℝ → Ω → OscDual d b.m,
      IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y →
      AEMeasurable (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)) P ∧
      AEMeasurable (processWindow b.m b.T 0 Y) P ∧
      ENNReal.ofReal (smoothDist 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (S.q N * generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ∧
      wassersteinE 1 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (Real.sqrt (S.q N * generalLocalizationRate d
            (S.energyMomentE N 1 P X).toReal M₂ N))) ∧
      wassersteinE 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 2 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 2 P X +
          ENNReal.ofReal (Real.sqrt (S.q N * generalLocalizationRate d
            (S.energyMomentE N 1 P X).toReal M₂ N)))

/-! ### S2.1: the whole-space headline theorem -/

section Headline

/-- The quadratic gradient dynamics of S2.1 (S lines 318-320): `V(x) = a|x|²/2`, gradient case
`M = -I`, `ν = β⁻¹`. -/
def quadraticGradientDyn (d : ℕ) (s a β : ℝ) : WholeDyn d := ⟨s, -1, confinement a, β⁻¹⟩

/-- Gibbs invariance of the canonical quadratic gradient dynamics at fixed particle number `N` (statement change M1,
2026-10-22; the whole-space "Q47", S L7901, L4640-4650, L5064-5075: "the canonical Gibbs law is invariant").  For every
probability space with a vector Brownian motion `W'`, an initial configuration `X₀'` independent of it with law
`canonicalGibbs (rieszKernel d s) (confinement a) N β = ℙ_{N,β}`, and every collision-free strong solution `X'` of
`quadraticGradientDyn d s a β` on `[0,T]`, the time marginals are `ℙ_{N,β}`: `law (X' t) = ℙ_{N,β}` for `0 ≤ t ≤ T`.
This is the same form as the hypothesis `hInv` of `euclidean_preparations_stationary` (S3.2).  It is a hypothesis about
the dynamics only (it does not involve `ρβ`, `ε`, `ψ`), so it sits after `N` and before the realization.  It is a true
statement for `d ≥ 2`, `0 ≤ s < d`, `a, β > 0`, `N ≥ 1` (no collisions, no explosion, pathwise uniqueness for the
collision-free solutions, the Gibbs density is the invariant density of the associated Dirichlet-form diffusion); proving it
(M1 option (a), whole-space analogue of the torus entropy-law argument) would let every edit below be reverted. -/
def GibbsInvariant (d : ℕ) (s a β : ℝ) (N : ℕ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (T : ℝ) (X₀' : Ω' → EucConfig d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d))
    (X' : ℝ≥0 → Ω' → EucConfig d N), IsVectorBrownian P' W' →
    IndepFun X₀' (fun ζ t => W' t ζ) P' →
    law P' X₀' = canonicalGibbs (rieszKernel d s) (confinement a) N β →
    IsWholeStrongSolution P' (quadraticGradientDyn d s a β) T X₀' W' X' →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      law P' (X' t) = canonicalGibbs (rieszKernel d s) (confinement a) N β

/-- Relative-entropy contraction of the canonical quadratic gradient dynamics with respect to its invariant Gibbs law, at fixed particle
number `N` (statement change M1b, 2026-10-22; the Markov-semigroup step of S L4640-4650 and S L5160-5170: "the Markov semigroup contracts
relative entropy with respect to an invariant measure (Jensen)").  For every probability space with a vector Brownian motion `W'`, an
initial configuration `X₀'` independent of it (of ARBITRARY law), and every collision-free strong solution `X'` of
`quadraticGradientDyn d s a β` on `[0,T]`: `H(law X'_t | ℙ_{N,β}) ≤ H(law X₀' | ℙ_{N,β})` for `0 ≤ t ≤ T`, where
`ℙ_{N,β} = canonicalGibbs (rieszKernel d s) (confinement a) N β` and `H = relEntropy` is `ℝ≥0∞`-valued (so the inequality is trivial when
the right side is `⊤`, in particular when `law X₀'` is not absolutely continuous).  It is a hypothesis about the dynamics only, true for
`d ≥ 2`, `0 ≤ s < d`, `a, β > 0`, `N ≥ 1` (pathwise uniqueness gives a Markov kernel `P_t` from every collision-free point, `ℙ_{N,β}` is
`P_t`-invariant, and the kernel contracts relative entropy by data processing / joint convexity).  It implies `GibbsInvariant d s a β N`:
for `law X₀' = ℙ_{N,β}` the right side is `klDiv ℙ ℙ = 0`, so `klDiv (law X'_t) ℙ = 0`, i.e. `law X'_t = ℙ_{N,β}` (`InformationTheory.klDiv_self`,
`klDiv_eq_zero_iff` for the two finite measures; `law X'_t` is a probability measure because `X' t` is measurable, `IsWholeStrongSolution.adapted`).
Unlike `GibbsInvariant` it also covers initial laws with density vanishing on a set of positive `ℙ_{N,β}`-mass, which a reweighting of a
realization cannot reduce to the stationary case (reviewer D1 of docs/HINV_EDITS.md).  Proving it would let every use be reverted. -/
def GibbsEntropyContraction (d : ℕ) (s a β : ℝ) (N : ℕ) : Prop :=
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (T : ℝ) (X₀' : Ω' → EucConfig d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d))
    (X' : ℝ≥0 → Ω' → EucConfig d N), IsVectorBrownian P' W' →
    IndepFun X₀' (fun ζ t => W' t ζ) P' →
    IsWholeStrongSolution P' (quadraticGradientDyn d s a β) T X₀' W' X' →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      relEntropy (law P' (X' t)) (canonicalGibbs (rieszKernel d s) (confinement a) N β) ≤
        relEntropy (law P' X₀') (canonicalGibbs (rieszKernel d s) (confinement a) N β)

/-- The initial smooth-estimate error `i_N` of `H:eq:whole-prepared-smooth`
(S lines 380-383): `N^{-1/(4d+6)}` for independent preparation (`β₀ = 0`), `√δ_N` for Gibbs
preparation (`β₀ > 0`). -/
def iN (d : ℕ) (s β₀ : ℝ) (N : ℕ) : ℝ :=
  if β₀ = 0 then (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 6))) else Real.sqrt (deltaN d s N)

/-- The initial `W_1` error `j_N` of `H:eq:whole-prepared-W1`: `N^{-1/(4d+6)}` (independent
preparation), `δ_N^{3/20}` (Gibbs preparation). -/
def jN (d : ℕ) (s β₀ : ℝ) (N : ℕ) : ℝ :=
  if β₀ = 0 then (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 6))) else deltaN d s N ^ ((3 : ℝ) / 20)

/-- "The resulting nonlinear mean-field solution" of S2.1 (S lines 322-336) of the quadratic
gradient dynamics from `μ⁰ = (1+εψ)μ_β`, in the form in which it is constructed by Theorem S6.3
`W:thm:r2mov-nonlinear` (S lines 4345-4371) with `j = 100d + 1000` and `m = 102d + 1020`: a global
weak solution (`IsWholeMeanFieldSolution` on every `[0,T']`) with
* `C₁⁻¹ρ_β ≤ ρ^t ≤ C₁ρ_β` (`W:r2mov:ratio`),
* `‖(ρ^t - ρ_β)/√ρ_β‖_{Σ^{102d+1020}} ≤ C₁ε_* e^{-c₁t}` (`W:r2mov:nonlinear-weighted`),
* `‖∇log(ρ^t/ρ_β)‖_{C_b^j} + ‖u^t‖_{C_b^j} ≤ C₁ε_* e^{-c₁t}`, `u^t = ν∇log ρ^t + a x + ∇g*ρ^t`
  (`W:r2mov:velocity`; `a = a₀` the confinement strength, `ν = β⁻¹`).
The constants `c₁, C₁` are those of S6.3 (they depend only on the model parameters); the existence
and uniqueness of such a solution is Theorem S6.3, not asserted here.
Statement repair `Supplement repair P3` (docs/ISSUES.md): `0 < c₁`, continuity of `t ↦ v_t = (ρ^t-ρ_β)/√ρ_β` into
`Σ^{102d+1020}` on `[0,∞)` and continuity of `ρ^t` in `x`, so that the structure implies the S6.3 uniqueness class
`MovInSmallClass` (with `m = 102d+1020`, `r = C₁ε_*`, `c₀ = c₁`, and exponent `0` by `MovInSmallClass.mono_rate`). -/
structure IsResultingSolution (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (εstar ε : ℝ)
    (ψ : Euc d → ℝ) (c₁ C₁ : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop where
  cpos : 0 < c₁
  global : ∀ T' : ℝ, IsWholeMeanFieldSolution (quadraticGradientDyn d s a β) T' ρ
  init : ρ 0 = perturbedDensity ρβ ε ψ
  ratio : ∀ t : ℝ, 0 ≤ t → ∀ x, C₁⁻¹ * ρβ x ≤ ρ t x ∧ ρ t x ≤ C₁ * ρβ x
  weighted : ∀ t : ℝ, 0 ≤ t →
    MemOsc (102 * (d : ℝ) + 1020) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ∧
    oscNorm (102 * (d : ℝ) + 1020) (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x)) ≤
      C₁ * εstar * Real.exp (-c₁ * t)
  velocity : ∀ t : ℝ, 0 ≤ t →
    cbNormVecE (100 * d + 1000) (fun x => gradient (fun y => Real.log (ρ t y / ρβ y)) x) +
      cbNormVecE (100 * d + 1000) (fun x => β⁻¹ • gradient (fun y => Real.log (ρ t y)) x +
        a • x + convGradConvW (rieszKernelGrad d s) (ρ t) x) ≤
      ENNReal.ofReal (C₁ * εstar * Real.exp (-c₁ * t))
  cont : ContinuousOn (fun t : ℝ => OscSpace.ofFun (d := d) (102 * (d : ℝ) + 1020)
    (fun x => (ρ t x - ρβ x) / Real.sqrt (ρβ x))) (Set.Ici 0)
  regular : ∀ t : ℝ, 0 ≤ t → Continuous (ρ t)

/-- Theorem S2.1 (S:H:thm:whole-space, TeX S L348-396), part (i): for `d ≥ 2`, `0 ≤ s < d`, the
quadratic potential `V = a|x|²/2` (`a, β > 0`) and `T < ∞`, with `m = 24d + 240`, stationary
canonical preparation (the particles are started from the canonical Gibbs law `ℙ_{N,β}` and run
with the gradient dynamics) and exact first-marginal centering `ζ_N^t = √N(μ_N^t - m_N^t)`, on
`𝒳 = C([0,T];B_m)`:
`d_2^𝒳(ζ_N, Z_β) ≤ C_T(√δ_N + w_N)` and `W_1^𝒳(ζ_N, Z_β) ≤ C_T(δ_N^{3/20} + √w_N)`
(`H:eq:whole-stationary`), `w_N = (N^{-1/d} + √o_N)^{4/(d+4)}` (`localizationRate`), with the heat-kernel
completion `o_N = oN d s C₀ N` whose constant `C₀` is chosen for the class (`∃ C₀` with the
completion property `F_N(X_N, μ_β) + o_N ≥ 0` off collisions, the lower bound for `F_N`).  `Z_β` is the
stationary linear Gaussian field of the equilibrium (`IsLinearGaussianEvolutionW` along the constant
reference `ρ_β` with noise level `q = β⁻¹` and initial covariance the susceptibility form
`C_β(φ,ψ) = ⟨P_μφ, R_{β,μ}P_μψ⟩_{L²(μ)}`, `H:eq:susceptibility`), for any realization on any
probability space.  `μ_β = ρ_β dx` is the thermal equilibrium (`IsThermalEquilibrium`; its
existence and uniqueness is S3.4).  The constants depend on `d, s, a, β, T`.
Not stated here (pointers in the source, not claims of this theorem): the `s = d/2` strengthening
(`S:prop:critical-whole`) and the sharper fixed-time smooth estimate `C√δ_N` for integer `J > d/2+2`,
`m > J + 2d` (S lines 379-382; it is `HRS.Whole.quadratic_static_field_osc`).
Statement change M1 (2026-10-22): the second conjunct is conditional on `GibbsInvariant d s a β N` (the canonical Gibbs law
`ℙ_{N,β}` is invariant for the gradient particle dynamics, S L7901 "The canonical law is invariant"; the whole-space analogue of
the hypothesis `hInv` of S3.2).  In this theorem the realization is itself started from `ℙ_{N,β}`, so the hypothesis is used only
to read off `law (X t) = ℙ_{N,β}`; it is removed if the invariance is proved later.
Technical hypothesis: `T > 0`. -/
abbrev WholeSpaceStationaryStatement : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T),
    ∃ C₀ C : ℝ, (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal ρβ) + oN d s C₀ N) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
      GibbsInvariant d s a β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
        law P X₀ = canonicalGibbs (rieszKernel d s) (confinement a) N β →
        IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
        IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T
          (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) β) Z →
        AEMeasurable (zetaPathW (wholeSpaceIndex d) T 0 P X) P ∧
        AEMeasurable (processWindow (wholeSpaceIndex d) T 0 Z) P' ∧
        smoothDist 2 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
            (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
          C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ∧
        wassersteinE 1 (law P (zetaPathW (wholeSpaceIndex d) T 0 P X))
            (law P' (processWindow (wholeSpaceIndex d) T 0 Z)) ≤
          ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N)))

/-- Theorem S2.1 (S:H:thm:whole-space, TeX S L348-396), part (ii) (L369-386): `0 ≤ s < 2d/3`, mean-field
initial measure `μ⁰ = (1+εψ)μ_β` in the class `H:eq:whole-smallness` (`IsAdmissiblePerturbation`:
`ψ ∈ C_c^∞` nonzero with `μ_β(ψ) = 0`, `ε = 0` allowed, the smallness
`‖εψ‖_{C_b^{100d+1001}} + ‖ε√ρ_βψ‖_{Σ^{102d+1020}} ≤ ε_*`), `μ^t` the resulting nonlinear mean-field
solution (`IsResultingSolution` with the constants `c₁, C₁` of S6.3, quantified first), particles
prepared from `ℚ_{N,β₀}(μ⁰)` (`β₀ ≥ 0` fixed, `ℚ_{N,0} = (μ⁰)^{⊗N}`; `modulatedGibbs`) and evolved from
time zero (not restarted at the window boundary).  `Z` is the linear Gaussian evolution along `μ^t`
(noise level `q = β⁻¹`) with initial covariance the bridge (`β₀ = 0`) or the susceptibility
(`β₀ > 0`) covariance `⟨P_{μ⁰}φ, (I+β₀K_{μ⁰})⁻¹P_{μ⁰}ψ⟩_{L²(μ⁰)}` (`susceptibilityCov` at `μ⁰`,
`β₀`; at `β₀ = 0` it is the bridge covariance `Cov_{μ⁰}`).  Then uniformly over all window starts
`a₀ ≥ 0`, on `𝒳 = C([0,T];B_m)`, `m = 24d+240`:
`d_2^𝒳(η_N^{a₀+·}, Z^{a₀+·}) ≤ C_T(√N δ_N + w_N + i_N)`,
`W_1^𝒳(η_N^{a₀+·}, Z^{a₀+·}) ≤ C_T(√N δ_N + √w_N + j_N)` (`H:eq:whole-prepared-smooth`,
`H:eq:whole-prepared-W1`), `η_N^t = √N(μ_N^t - μ^t)`, `i_N, j_N` as in the source (`iN`, `jN`).
The quantifier order: `ε_*` and the completion constant `C₀` (chosen for the class: `F_N(X_N,μ^t) +
o_N ≥ 0` for all `t ≥ 0`) first, then `C_T` (uniform over the class and over `a₀`).  The conclusion
does not assert the `W_2` version (S lines 397-400).
Statement change M1b (2026-10-22): the second conjunct (the particle estimates) is conditional on `GibbsEntropyContraction d s a β N`:
the entropy-contraction clauses are conditional on it, which holds because the canonical Gibbs law `ℙ_{N,β}` is invariant for the Markov kernel
of the particle dynamics at the physical `β` and relative entropy contracts along a Markov kernel (S L7901, L4640-4650, L5160-5170); the completion
clause `0 ≤ F_N + o_N` is unconditional.
Depends on S6.3 (see the module docstring). -/
abbrev WholeSpacePreparedStatement : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (T : ℝ) (hT : 0 < T)
    (c₁ C₁ : ℝ),
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ C : ℝ,
      (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal (ρ t)) + oN d s C₀ N) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N →
        GibbsEntropyContraction d s a β N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
          (X : ℝ≥0 → Ω → EucConfig d N),
          IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
          law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
          (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
          (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
            (wholeSpaceIndex d) β⁻¹ T'
            (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
        ∀ a₀ : ℝ, 0 ≤ a₀ →
          AEMeasurable (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ) P ∧
          AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
          smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
              (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
            C * (Real.sqrt N * deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N) ∧
          wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X ρ))
              (law P' (processWindow (wholeSpaceIndex d) T a₀ Z)) ≤
            ENNReal.ofReal (C * (Real.sqrt N * deltaN d s N +
              Real.sqrt (localizationRate d s C₀ N) + jN d s β₀ N))

/-- `h_v(x,y) = (v(x)-v(y))·∇g(x-y)` for the cyclic sums of `H:eq:cubic-formula`; the triple
`(i,j,k)` is `(i, i+1, i+2)` in `Fin 3`. -/
def cubicFormula (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (β β₀ : ℝ) (μ0 : Measure (Euc d))
    (t : Fin 3 → ℝ) (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : ℝ :=
  let f : Fin 3 → ℝ → Euc d → ℝ := fun i r => propagatorW (D.coeff ρ) r (t i) (φ i)
  let r0 : Fin 3 → Euc d → ℝ := fun i => responseInverse (rieszKernel d D.s) μ0 β₀ (f i 0)
  (∫ x, r0 0 x * r0 1 x * r0 2 x ∂μ0)
    - (∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (t i), ∫ x, ∫ y,
        commutatorKernel d D.s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y)
    + (2 / β) * ∑ i : Fin 3, ∫ r in Set.Icc (0 : ℝ) (min (t i) (t (i + 1))), ∫ x,
        inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x

/-- Integrability of the integrands in `cubicFormula` (the Bochner integrals there are the source's
integrals only if these hold; stated as part of the conclusion of `whole_space_edgeworth`). -/
def CubicFormulaIntegrable (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (β₀ : ℝ) (μ0 : Measure (Euc d))
    (t : Fin 3 → ℝ) (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : Prop :=
  let f : Fin 3 → ℝ → Euc d → ℝ := fun i r => propagatorW (D.coeff ρ) r (t i) (φ i)
  let r0 : Fin 3 → Euc d → ℝ := fun i => responseInverse (rieszKernel d D.s) μ0 β₀ (f i 0)
  Integrable (fun x => r0 0 x * r0 1 x * r0 2 x) μ0 ∧
  (∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (t i),
    Integrable (fun p : Euc d × Euc d =>
      commutatorKernel d D.s (fun z => gradient (f i r) z) p.1 p.2 * χ (i + 1) r p.1 * χ (i + 2) r p.2)) ∧
  (∀ i : Fin 3, IntegrableOn (fun r => ∫ x, ∫ y,
      commutatorKernel d D.s (fun z => gradient (f i r) z) x y * χ (i + 1) r x * χ (i + 2) r y)
    (Set.Icc (0 : ℝ) (t i))) ∧
  (∀ i : Fin 3, ∀ r ∈ Set.Icc (0 : ℝ) (min (t i) (t (i + 1))),
    Integrable (fun x => inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x)) ∧
  (∀ i : Fin 3, IntegrableOn (fun r => ∫ x,
      inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) * χ (i + 2) r x)
    (Set.Icc (0 : ℝ) (min (t i) (t (i + 1)))))

/-- Theorem S2.1 (S:H:thm:whole-space, TeX S L348-396), part (iii) (L387-394): `0 ≤ s < d/2`; for a positive Riesz
exponent `β₀ > 0`, for the logarithm every `β₀ ≥ 0`; same data as (ii).  The exactly centered path
`ζ_N^{a₀+·}` (centered at the actual first marginal `m_N^t`, the preparation `ℚ_{N,β₀}(μ⁰)`
evolved from time zero) satisfies the uniform `C_b^5` expansion `H:eq:window-edgeworth` in
`𝒳 = C([0,T];B_m)`: there are symmetric projective cubic tensors `κ_{a₀,T} ∈ 𝒳 ⊗̂_π 𝒳 ⊗̂_π 𝒳`
(`projTensor`) with `sup_{a₀≥0} ‖κ_{a₀,T}‖_π < ∞` and a sequence `ε_N(T) → 0` such that, uniformly in
`a₀ ≥ 0` and `‖Φ‖_{C_b^5(𝒳)} ≤ 1`,
`|√N(E Φ(ζ_N^{a₀+·}) - E Φ(Z^{a₀+·})) - (1/6) E⟨D³Φ(Z^{a₀+·}), κ_{a₀,T}⟩| ≤ ε_N(T)`.  The tensor has
the three terms of `H:eq:cubic-formula` with the whole-space adjoint and the actual nonstationary
Gaussian covariance: for every observation family (`φ_i` oscillator test functions at window times
`τ_i ∈ [0,T]`, physical times `t_i = a₀ + τ_i`) and every bounded trilinear form `M` on `𝒳` evaluating
`M(w₁,w₂,w₃) = ∏_i w_i(τ_i)(φ_i)`, and every family `χ_i^r` of signed densities with `χ_i^r/ρ^r ∈ L²(ρ^r dx)` (the source's `L²(μ)`-relative densities; no
smoothness) determined by
`∫ψχ_i^r = Cov(Z^r(ψ), Z^{t_i}(φ_i))` (`linearGaussianCov`; their existence is part of the conclusion, repair P4 of
2026-10-20, so that the formula clause is not vacuous; imposed for *all* `r ∈ [0,a₀+T]`, since
`cubicFormula` uses `χ_{i+1}^r, χ_{i+2}^r` for `r ≤ t_i` where `t_{i+1}` may be smaller; M L1297 defines `χ_i^r`
for all `r`), `⟨κ_{a₀,T}, M⟩ = cubicFormula` with all integrals absolutely defined
(`CubicFormulaIntegrable`, part of the conclusion); the
`r`-integrals begin at physical time `0` even for a late window; at `β₀ = 0` the initial
susceptibility is the identity.  `ε_N(T)` and `κ` depend on the data (they are not uniform over the
class), and `ε_*` is the smallness constant of the class.  The logarithmic endpoint is verified in
`O:cor:log-path` (M), not here.  Depends on S6.3 and on the static/window Edgeworth rows of S9-S11
for its proof.
Technical hypotheses: `T > 0`; the densities `χ_i^r` are quantified (their existence is asserted in the conclusion). -/
abbrev WholeSpaceEdgeworthStatement : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀s : 0 < s → 0 < β₀)
    (T : ℝ) (hT : 0 < T) (c₁ C₁ : ℝ),
    ∃ εstar : ℝ, 0 < εstar ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∃ (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ),
          (∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖κ a₀‖ ≤ Kb) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
            (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
            (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) (M.domDomCongr σ) =
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M) ∧
          Tendsto εN atTop (𝓝 0) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
            (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
            (∃ χ : Fin 3 → ℝ → Euc d → ℝ,
              ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
                MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
                ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                  Integrable (fun x => ψ' x * χ i r x) ∧
                  ∫ x, ψ' x * χ i r x = linearGaussianCov
                    ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                    (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                    ψ' (φ i)) ∧
            ∀ χ : Fin 3 → ℝ → Euc d → ℝ,
            (∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
              MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
              ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                Integrable (fun x => ψ' x * χ i r x) ∧
                ∫ x, ψ' x * χ i r x = linearGaussianCov
                  ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                  (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                  ψ' (φ i)) →
            ∀ M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ,
              (∀ w : Fin 3 → OscPath d (wholeSpaceIndex d) T,
                M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) →
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M =
                cubicFormula (quadraticGradientDyn d s a β) ρ β β₀ (withDensityReal (ρ 0))
                  (fun i => a₀ + τ i) φ χ ∧
              CubicFormulaIntegrable (quadraticGradientDyn d s a β) ρ β₀ (withDensityReal (ρ 0))
                (fun i => a₀ + τ i) φ χ) ∧
          ∀ N : ℕ, 2 ≤ N →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
            (X : ℝ≥0 → Ω → EucConfig d N),
            IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
            law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
            (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
            (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
              (wholeSpaceIndex d) β⁻¹ T'
              (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
          ∀ a₀ : ℝ, 0 ≤ a₀ →
            AEMeasurable (zetaPathW (wholeSpaceIndex d) T a₀ P X) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
            ∀ Φ : OscPath d (wholeSpaceIndex d) T → ℝ,
              Φ ∈ CbUnitBall (OscPath d (wholeSpaceIndex d) T) 5 →
              |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T a₀ P X ζ) ∂P -
                  ∫ ζ', Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ') ∂P') -
                (1 / 6) * ∫ ζ', (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
                  (iteratedFDeriv ℝ 3 Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ')) ∂P'| ≤
                εN N

end Headline

end HRS.Whole
