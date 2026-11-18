import HRS.Main.Linearization
import HRS.Main.A34Aux29

/-!
# The main torus theorems (main manuscript, Appendix A)

Specification file SPEC-A (statements with `sorry` proofs).  Sources
(`HRS_periodic_main_20261008T010000Z.tex`):
* Proposition A.8 `M:B:thm:main-torus-stat` (L10294-10318): `main_torus_stat`;
* Proposition A.9 `M:B:thm:main-torus-field` (L10330-10349): `main_torus_field`,
  `main_torus_field_limit`;
* Corollary A.10 `M:B:cor:torus-field-wasserstein` (L10351-10378): `torus_field_wasserstein`;
* Proposition A.11 `M:B:thm:main-torus-path` (L10380-10392): `main_torus_path`;
* Corollary A.14 `M:B:cor:true-limit` (L10409-10435): `true_limit_stat`, `true_limit_stat_base`,
  `true_limit_field`;
* Remark A.15 `M:B:rem:interpretation` (L10438-10448): `interpretation_scaling`;
* Example A.16 `M:B:ex:deterministic` (L10450-10466): `deterministic_example`,
  `deterministic_scaling`;
* Proposition A.34 `M:B:prop:surrogate-to-limit` (L11439-11463): `surrogate_to_limit_stat`,
  `surrogate_to_limit_stat_base`, `surrogate_to_limit_field`,
  `surrogate_to_limit_field_qualitative`.

## Shape of the statements

* **Constants.**  "There exist `C, Λ_T > 0` depending only on `d, s, |M|, Λ, T, ‖V‖, C_in` (and `ν₀`)"
  is `∃ C ΛT, 0 < C ∧ 0 < ΛT ∧ ∀ S R …` placed *after* the bounds `(d, s, Rg, ν₀, MB, Λ, T, VB, Cin,
  C₀, Cc)` and *before* the data `S, R` (so the constants cannot depend on `M, V, κ_N, β_N, ρ_N`, on
  the sequences `ε_N, 𝔈_N`, nor on the realization).  Dependence on the regime `Rg` (including `λ₀`
  of R2b) and on the completion pair `(C₀, Cc)` (which depends only on `d, s`) is explicit.
* "for every `t ∈ [0,T]` and `N ≥ C`" is `t ∈ Icc 0 T` and `C ≤ (N : ℝ)` (`C > 0` forces `N ≥ 1`).
* The finite family of tests and times on which the initial coupling may depend (A.4) is
  quantified *before* the realization-dependent hypothesis `InitialFluctuation …` (the realization `R`
  is quantified before the family but `InitialFluctuation` is imposed for the family), and the
  conclusion is stated for that family.
* One real statistic `⟨φ,σ_NΞ_N^t⟩` is the case `ι = Fin 1` (`ℝ^1` and `ℝ` are isometric).  Complex
  tests are `ι = Fin (n+1) × Bool` (real and imaginary parts), the statistics being viewed in `ℝ^{2p}`;
  the `H^m` norm of a complex test is `sobolevNormC`.
* Laws of the linear approximations are the explicit measures of `HRS/Main/Linearization.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Auxiliary notions -/

/-- The transported terminal tests `{U_N^{0,t_a} φ_a}` of the finite family `(φ_a, t_a)` (the
generators of the finite-dimensional span in A.4, TeX L10208). -/
def transportedTests (S : MainData d) {ι : Type*} (ts : ι → ℝ) (φ : ι → Torus d → ℝ) (N : ℕ) :
    Set (Torus d → ℝ) :=
  Set.range fun a => propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)

/-- A complex test lies in `H^m` iff its real and imaginary parts do. -/
def MemSobolevC (m : ℝ) (φ : Torus d → ℂ) : Prop :=
  MemSobolev m (fun x => (φ x).re) ∧ MemSobolev m (fun x => (φ x).im)

/-- The `H^m` norm of a complex test, `‖φ‖²_{H^m} = ‖Re φ‖²_{H^m} + ‖Im φ‖²_{H^m}`
(`∑_k ⟨k⟩^{2m}|φ̂(k)|²` for `φ = u + iv` with `u, v` real). -/
def sobolevNormC (m : ℝ) (φ : Torus d → ℂ) : ℝ :=
  Real.sqrt (sobolevNorm m (fun x => (φ x).re) ^ 2 + sobolevNorm m (fun x => (φ x).im) ^ 2)

/-- The real family `(Re φ_a, Im φ_a)` indexed by `ι × Bool` of a complex family: the statistics of
complex tests "viewed in `ℝ^{2p}`" (A.8 (c), L10310). -/
def realImParts {ι : Type*} (φ : ι → Torus d → ℂ) : ι × Bool → Torus d → ℝ :=
  fun ab x => if ab.2 then (φ ab.1 x).im else (φ ab.1 x).re

/-- The rates `𝔯_N` and `𝔯'_N` of `B:eq:master-rate` (TeX L10299, L10315):
`ε + (σ²/(Nβ))^{1/2} (𝔈^{1/4} + N^{-1/(2d)}) + σ E`, with `q = σ²/(Nβ)`, `E = 𝔈_N` (`𝔯_N`, `ε = ε_N`)
or `E = 𝔈'_N` (`𝔯'_N`, `ε = ε_N^{(2)}`). -/
def masterRate (d : ℕ) (ε q σ 𝔈 E : ℝ) (N : ℕ) : ℝ :=
  ε + Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) + σ * E

/-- The rate of `B:eq:thm-torus-field` (TeX L10339-10341):
`ε^f + σ 𝔈 + (σ²/(Nβ)) (𝔈^{1/2} + N^{-1/d})`. -/
def fieldRate (d : ℕ) (εf q σ 𝔈 : ℝ) (N : ℕ) : ℝ :=
  εf + σ * 𝔈 + q * (𝔈 ^ ((1 : ℝ) / 2) + (N : ℝ) ^ (-(1 : ℝ) / d))

/-- The right-hand side `C e^{Λ_T t} X (1 + X) r` of the statistics bounds
(`B:eq:thm-torus-w1`, `B:eq:thm-torus-dc2`, `B:eq:thm-torus-joint-w2`), `X = ‖φ‖` or `∑_a ‖φ_a‖`. -/
def statBound (C ΛT t X r : ℝ) : ℝ := C * Real.exp (ΛT * t) * X * (1 + X) * r

/-! ### Proposition A.8 -/

/-- Proposition A.8 `M:B:thm:main-torus-stat` (TeX L10294-10318), joint linear statistics on `𝕋^d`.
Hypotheses (`TorusStanding`): A.1, A.2, A.3 with `r = m_*+3`, `|M| ≤ MB`, `‖V‖_{C^{m_*+3}} ≤ VB`, A.6.
There exist `C, Λ_T` depending only on `d, s, |M|, Λ, T, ‖V‖_{C^{m_*+3}}, C_in` (and `ν₀`, `λ₀`, i.e.
the regime `Rg`, and the completion pair) such that for every `t ∈ [0,T]`, `N ≥ C`:
* (a) single statistics, `W₁`: for every real `φ ∈ H^{m_*}`, with A.4 for the family `{(φ,t)}`,
  `W₁(Law⟨φ,σ_NΞ_N^t⟩, Law 𝔖_N^t[φ]) ≤ C e^{Λ_T t} ‖φ‖(1+‖φ‖) 𝔯_N`;
* (b) joint statistics, `d_{C²}`, real `φ_1..φ_p ∈ H^{m_*}`;
* (c) complex tests (statistics in `ℝ^{2p}`) at finitely many times `0 ≤ t_1 ≤ … ≤ t_q = t`
  (`B:rem:multitime`), `d_{C²}`;
* (d) under A.7 (and A.4), the `W₂` variant with `𝔯'_N`, for complex tests at finitely many times
  (this contains the real, single-time case: real tests are complex tests with zero imaginary part).
**Technical hypotheses**: every test is assumed *continuous* (`Continuous φ`, resp. for all `φ_a`,
the continuous representative; `H^{m_*} ⊂ C²` as `m_* > d/2 + 2`), because the statistics evaluate
tests pointwise (`⟨φ,μ_N⟩`) while `MemSobolev` only fixes a class a.e.; also (I2) is imposed for
continuous `ψ` only (see `InitialFluctuation`).  The "In particular" sentence is
`main_torus_stat_tendsto`.

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem main_torus_stat (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 →
        -- (a) single statistics, `W₁`
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (φ : Torus d → ℝ), t ∈ Set.Icc (0 : ℝ) T →
          MemSobolev (PDE.mStar d : ℝ) φ → Continuous φ →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun _ : Fin 1 => t) (fun _ => φ)) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            wassersteinE 1
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t)
                (fun _ => φ) (R N).P (R N).η) ≤
            ENNReal.ofReal (statBound C ΛT t (sobolevNorm (PDE.mStar d : ℝ) φ)
              (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N))) ∧
        -- (b) joint statistics, `d_{C²}`
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (p : ℕ) (φ : Fin p → Torus d → ℝ), 1 ≤ p →
          t ∈ Set.Icc (0 : ℝ) T → (∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) →
          (∀ a, Continuous (φ a)) →
          InitialFluctuation S R m₀ Cin ε (transportedTests S (fun _ : Fin p => t) φ) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            smoothDist 2
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin p => t) φ)
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin p => t) φ
                (R N).P (R N).η) ≤
            statBound C ΛT t (∑ a, sobolevNorm (PDE.mStar d : ℝ) (φ a))
              (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) ∧
        -- (c) complex tests, finitely many times, `d_{C²}`
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (n : ℕ) (ts : Fin (n + 1) → ℝ) (φ : Fin (n + 1) → Torus d → ℂ),
          Monotone ts → 0 ≤ ts 0 → ts (Fin.last n) ≤ T →
          (∀ a, MemSobolevC (PDE.mStar d : ℝ) (φ a)) → (∀ a, Continuous (φ a)) →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ)) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            smoothDist 2
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ))
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ) (R N).P (R N).η) ≤
            statBound C ΛT (ts (Fin.last n)) (∑ a, sobolevNormC (PDE.mStar d : ℝ) (φ a))
              (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) ∧
        -- (d) joint `W₂` variant under A.7, complex tests, finitely many times
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (𝔈' ε2 : ℕ → ℝ) (n : ℕ) (ts : Fin (n + 1) → ℝ)
          (φ : Fin (n + 1) → Torus d → ℂ),
          Monotone ts → 0 ≤ ts 0 → ts (Fin.last n) ≤ T →
          (∀ a, MemSobolevC (PDE.mStar d : ℝ) (φ a)) → (∀ a, Continuous (φ a)) →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ)) →
          EnergySmallness2 S R C₀ Λ m₀
            (transportedTests S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ)) 𝔈' ε2 →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            wassersteinE 2
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ))
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ) (R N).P (R N).η) ≤
            ENNReal.ofReal (statBound C ΛT (ts (Fin.last n)) (∑ a, sobolevNormC (PDE.mStar d : ℝ) (φ a))
              (masterRate d (ε2 N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈' N) N))) := by
  sorry

/-- Proposition A.8 `M:B:thm:main-torus-stat`, the "In particular" sentence (TeX L10317): under A.4
and A.6 (and the standing bound `sup_N β_N⁻¹ < ∞` carried by `MainData`) the rate
`𝔯_N = ε_N + (σ_N²/(Nβ_N))^{1/2}(𝔈_N^{1/4} + N^{-1/(2d)}) + σ_N𝔈_N → 0` (using `ε_N → 0`,
`σ_N𝔈_N → 0`, `σ_N²/(Nβ_N) ≤ 1`), and hence, for each finite family of continuous tests in `H^{m_*}`
(A.4 for that family), the joint law of the statistics `(⟨φ_a,σ_NΞ_N^t⟩)_a` converges to that of the
linear approximation: `d_{C²}(Law (⟨φ_a,σ_NΞ_N^t⟩)_a, Law 𝔖_N^t[φ⃗]) → 0` (consequence of
`main_torus_stat` (b)).  The final clause of the TeX sentence (convergence to the statistics of the limit
field) is `true_limit_stat_base`.

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem main_torus_stat_tendsto (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d), S.s = s → S.T = T →
    ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
    TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 →
    (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Torus d → ℝ)), InitialFluctuation S R m₀ Cin ε Ψ →
      Tendsto (fun N => masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) atTop (𝓝 0)) ∧
    (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (p : ℕ) (φ : Fin p → Torus d → ℝ), 1 ≤ p →
      t ∈ Set.Icc (0 : ℝ) T → (∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) →
      (∀ a, Continuous (φ a)) →
      InitialFluctuation S R m₀ Cin ε (transportedTests S (fun _ : Fin p => t) φ) →
      Tendsto (fun N => smoothDist 2
        (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin p => t) φ)
        (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin p => t) φ
          (R N).P (R N).η)) atTop (𝓝 0)) := by
  sorry

/-! ### Proposition A.9 -/

/-- Proposition A.9 `M:B:thm:main-torus-field` (TeX L10330-10343), the fluctuation field on `𝕋^d`.
Hypotheses: A.1, A.2, A.3 with `r = γ+3` (adjoint index `γ = m_*+d+3`, `gammaIdx`), A.4 (with the
empty finite family, since no finite family of tests occurs in the conclusion), A.5 (`Γ = γ`), A.6.
There exist `C, Λ_T` such that for every `t ∈ [0,T]`, `N ≥ C` and every Gaussian law `νG` of the
field `G_N^t` (`IsLinearFieldNoise`, existence by A.33):
`d_{C²}(Law σ_NΞ_N^t, Law η_{N,lin}^t) ≤ C e^{Λ_T t}[ε_N^f + σ_N𝔈_N + (σ_N²/(Nβ_N))(𝔈_N^{1/2} + N^{-1/d})]`
on the Hilbert space `H^{-γ}(𝕋^d)` (`NegSobolev d γ`); moreover `sup_N E‖σ_NΞ_N^t‖_{H^{-γ}} < ∞`.

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem main_torus_field (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ N : ℕ, C ≤ (N : ℝ) →
            ∀ νG : Measure (NegSobolev d (gammaIdx d : ℝ)),
              IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
              smoothDist 2
                (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
                (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
              C * Real.exp (ΛT * t) *
                fieldRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) N) ∧
          ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N →
            ∫⁻ ω, ‖S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
                (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))‖ₑ ∂(R N).P ≤
              ENNReal.ofReal B := by
  sorry

/-- Proposition A.9 `M:B:thm:main-torus-field` (TeX L10345-10347), convergence in law of the field.
Under the hypotheses of `main_torus_field` and the coefficient-convergence hypotheses of
`B:cor:true-limit` (`CoeffConvergence` with `lvl = m = γ`; `Δ_N^{(γ)} → 0`), the field
`σ_NΞ_N^t` converges in law to `η^t` (law `limitFieldLaw`) on `H^{-γ'}(𝕋^d)` for every `γ' > γ`
(the limit embedded by `NegSobolev.embed`); and the same conclusion holds in the base topology
`H^{-γ}` if, in addition, the transported initial fields `𝓘_N^t = A_N V_N^{t,0} η°` converge in law
there to `𝓘_∞^t = A V_∞^{t,0} η°` (qualitative alternative) or satisfy the quantitative condition
`B:eq:initial-limit-stability` `sup_{t' ≤ T} d_{C²}(Law 𝓘_N^{t'}, Law 𝓘_∞^{t'}) ≤ C Δ_N^{(γ)}`.
The fixed law `νin` of `η°` is part of `InitialFluctuationField`.
**Technical hypothesis** `hεf : ε_N^f → 0`: A.5 never states `ε_N^f → 0` (source gap), but the
convergence in law needs it; the other terms of `B:eq:thm-torus-field` tend to `0` by A.6 and the
standing bound `sup_N β_N⁻¹ < ∞` (see `main_torus_stat_tendsto`).

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem main_torus_field_limit (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈)
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    (L : LimitCoeffs d) (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d) (gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (νG : ℕ → Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνG : ∀ N : ℕ, 1 ≤ N →
      IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) (νG N))
    (νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνGlim : IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim),
    (∀ γ' : ℝ, (gammaIdx d : ℝ) < γ' →
      ConvergesInLaw
        (fun N => particleFieldLaw (R N).P (S.sigma N) γ' (R N).X (S.ρ N) t)
        ((limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map (NegSobolev.embed γ'))) ∧
    (((ConvergesInLaw
          (fun N => law (R N).P (fun ω => S.AN N •
            transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (ηF N ω)))
          (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F))) ∨
      (∃ Cs : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) T,
        smoothDist 2
          (law (R N).P (fun ω => S.AN N •
            transportField (S.dyn N) (S.ρ N) t' (gammaIdx d : ℝ) (ηF N ω)))
          (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
            L.A • transportField (L.dyn S) L.ρ t' (gammaIdx d : ℝ) F)) ≤
          Cs * S.coeffDiscrepancy L (gammaIdx d) N)) →
      ConvergesInLaw
        (fun N => particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
        (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim)) := by
  sorry

/-! ### Corollary A.10 -/

/-- Corollary A.10 `M:B:cor:torus-field-wasserstein` (TeX L10351-10378).  Under the hypotheses of
`main_torus_field`:
`W₁(Law σ_NΞ_N^t, Law η_{N,lin}^t) ≤ C e^{Λ_T t}[ε_N^f + (σ_N²/(Nβ_N))^{1/2}(𝔈_N^{1/4}+N^{-1/(2d)}) + σ_N𝔈_N]`;
if in addition A.7 holds and the field-level coupling satisfies
`(E‖κ_NΞ_N^0 - η°‖²_{H^{-γ}})^{1/2} ≤ ε_N^{f,(2)}` (`B:eq:field-initial-L2`; here `lintegral` form),
then `W₂(…) ≤ C e^{Λ_T t}[ε_N^{f,(2)} + (σ_N²/(Nβ_N))^{1/2}(𝔈_N^{1/4}+N^{-1/(2d)}) + σ_N𝔈'_N]`.
(`C, Λ_T` are quantified here again; they depend on the same data as in `main_torus_field`.)

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem torus_field_wasserstein (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
        ∀ νG : Measure (NegSobolev d (gammaIdx d : ℝ)),
          IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
          wassersteinE 1
            (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
            (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
          ENNReal.ofReal (C * Real.exp (ΛT * t) *
            masterRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) ∧
          (∀ (𝔈' ε2 εf2 : ℕ → ℝ),
            EnergySmallness2 S R C₀ Λ m₀ (fun _ => ∅) 𝔈' ε2 →
            (∀ N' : ℕ, 1 ≤ N' → 0 ≤ εf2 N') →
            (∀ N' : ℕ, 1 ≤ N' →
              ∫⁻ ω, ‖S.κ N' • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
                  (empirical ((R N').X₀ ω)) S.μ0 - ηF N' ω‖ₑ ^ 2 ∂(R N').P ≤
                ENNReal.ofReal ((εf2 N') ^ 2)) →
            wassersteinE 2
              (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
              (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
            ENNReal.ofReal (C * Real.exp (ΛT * t) *
              masterRate d (εf2 N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈' N) N)) := by
  sorry

/-! ### Proposition A.11 -/

/-- Proposition A.11 `M:B:thm:main-torus-path` (TeX L10380-10391), qualitative path-space
fluctuation field.  Hypotheses of `main_torus_field` with `r = γ+5` in A.3 (adjoint index `γ + 2`;
A.5 with `Γ = γ`), and the coefficient convergence `Δ_N^{(γ)} → 0` (`CoeffConvergence` with
`lvl = γ+2`, `m = γ`).  Then `Ξ_N^t = σ_NΞ_N^t`, `0 ≤ t ≤ T`, has continuous paths in `H^{-(γ+2)}`
(a.s.) and `Ξ_N^· ⟹ η^·` in `C([0,T]; H^{-(γ+2)}(𝕋^d))`, where the limit is any (continuous)
solution `Y` of the linear SPDE with the limiting coefficients and initial value `A η°`
(`IsLinearFluctuationSolution`, Proposition A.33).  No second-moment strengthening (A.7) is used.
**Technical hypothesis** `hεf : ε_N^f → 0` (source gap: A.5 never states it; see
`main_torus_field_limit`); the fixed law of `η°` is part of `InitialFluctuationField`.

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem main_torus_path (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈)
    (m₀ : ℕ) (ε : ℕ → ℝ) (hinit : InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (hεf : Tendsto εf atTop (𝓝 0)),
    (∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P,
      Continuous fun t : Set.Icc (0 : ℝ) T =>
        S.sigma N • NegSobolev.ofMeasureDiff ((gammaIdx d + 2 : ℕ) : ℝ)
          (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))) ∧
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y₀ : Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ))
      (Y : ℝ → Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ)),
      Measurable Y₀ →
      law P' Y₀ = νin.map (NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ)) →
      IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) L.invβstar T
        (fun ω => L.A • Y₀ ω) Y →
      ConvergesInLaw
        (fun N => law (R N).P
          (flucPath ((gammaIdx d + 2 : ℕ) : ℝ) T (S.sigma N) (R N).X (S.ρ N)))
        (law P' (toPath ((gammaIdx d + 2 : ℕ) : ℝ) T Y)) := by
  sorry

/-! ### Corollary A.14 -/

/-- Corollary A.14 `M:B:cor:true-limit` (TeX L10409-10435), linear statistics, quantitative part.
Common adjoint regime/constants and `Δ_N^{(m)} → 0` with `m = m_*` (`CoeffConvergence`, `lvl = m+2`).
For a real terminal test `φ` with two additional derivatives (`φ ∈ H^{m_*+2}`) the particle
statistics are compared with the *limiting* linear approximation `𝔖_∞^t[φ]` with error
`C e^{Λ_T t}(‖φ‖(1+‖φ‖) 𝔯_N + ‖φ‖_{H^{m_*+2}}(Δ_N^{(m)} + (Δ_N^{(m)})^{1/2}))`
(this is `main_torus_stat` (a) plus Proposition A.34 (i), L10423-10424).
**Technical hypothesis**: `φ` continuous (pointwise evaluation of the test; `H^{m_*+2} ⊂ C²`).
The remaining parts of the
corollary (path space, `H^{-γ'}`) are `main_torus_path`, `main_torus_field_limit`,
`surrogate_to_limit_field_qualitative`.

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem true_limit_stat (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 →
        ∀ (L : LimitCoeffs d),
          CoeffConvergence S L Rg ν₀ MB Λ VB (PDE.mStar d + 2) (PDE.mStar d) →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (φ : Torus d → ℝ), t ∈ Set.Icc (0 : ℝ) T →
          MemSobolev ((PDE.mStar d + 2 : ℕ) : ℝ) φ → Continuous φ →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun _ : Fin 1 => t) (fun _ => φ)) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            wassersteinE 1
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
              (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
                (R N).P (R N).η) ≤
            ENNReal.ofReal (C * Real.exp (ΛT * t) *
              (sobolevNorm (PDE.mStar d : ℝ) φ * (1 + sobolevNorm (PDE.mStar d : ℝ) φ) *
                  masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N +
                sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ *
                  (S.coeffDiscrepancy L (PDE.mStar d) N +
                    Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N)))) := by
  sorry

/-- Corollary A.14, linear statistics at the base regularity (TeX L10424, "at the base regularity it
is qualitative by density and uniform boundedness"): for every real `φ ∈ H^{m_*}`,
`W₁(Law⟨φ,σ_NΞ_N^t⟩, Law 𝔖_∞^t[φ]) → 0` (the rate `𝔯_N → 0` is `main_torus_stat_tendsto`).
**Technical hypothesis**: `φ` continuous (pointwise evaluation of the test).

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem true_limit_stat_base (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈)
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (PDE.mStar d + 2) (PDE.mStar d))
    (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : Torus d → ℝ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) (hφc : Continuous φ)
    (hinit : InitialFluctuation S R m₀ Cin ε
      (transportedTests S (fun _ : Fin 1 => t) (fun _ => φ))),
    Tendsto (fun N => wassersteinE 1
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
      (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
        (R N).P (R N).η)) atTop (𝓝 0) := by
  sorry

/-- Corollary A.14, fields, quantitative part (TeX L10427-10429, with the quantitative stability of
the transported initial fields `B:eq:initial-limit-stability` assumed, constant `Cs`): under the
hypotheses of `main_torus_field` and `CoeffConvergence` (`lvl = γ+2`, `m = γ`), for every Gaussian
law `νG` of `G_N^t` and `νGlim` of the limiting block,
`d_{C²}(Law σ_NΞ_N^t, Law η^t) ≤ C e^{Λ_T t}(fieldRate_N + Δ_N^{(γ)} + (Δ_N^{(γ)})^{1/2})`
(`main_torus_field` plus Proposition A.34 (ii)); `C` depends in addition on `Cs`.  `η°` has the
fixed law `νin` (part of `InitialFluctuationField`).

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): `TorusStanding` now includes the filtered strong solution (`filtered`, `IsFilteredSolution`) that the duality/Itô identity behind this statement needs and `SelectedFlowA1` (measurability only, ISSUES D1) does not record; `SelectedFlowA1.indep` already gives `IndepFun X₀ W`. -/
theorem true_limit_field (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin Cs : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ (L : LimitCoeffs d),
          CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d) →
          (∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) T,
            smoothDist 2
              (law (R N).P (fun ω => S.AN N •
                transportField (S.dyn N) (S.ρ N) t' (gammaIdx d : ℝ) (ηF N ω)))
              (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
                L.A • transportField (L.dyn S) L.ρ t' (gammaIdx d : ℝ) F)) ≤
              Cs * S.coeffDiscrepancy L (gammaIdx d) N) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
        ∀ νG νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)),
          IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
          IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim →
          smoothDist 2
            (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
            (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) ≤
          C * Real.exp (ΛT * t) *
            (fieldRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) N +
              (S.coeffDiscrepancy L (gammaIdx d) N + Real.sqrt (S.coeffDiscrepancy L (gammaIdx d) N))) := by
  sorry

/-! ### Remark A.15 -/

/-- Remark A.15 `M:B:rem:interpretation` (TeX L10438-10448), the scaling statement: if `β_N < ∞`
and `κ_N ∼ c √(Nβ_N)` with `c ∈ (0,∞)` (i.e. `κ_N / √(Nβ_N) → c`), then `A_N → A = min{1, c⁻¹}` and
`q_N = σ_N²/(Nβ_N) → β_*⁻¹ = min{1,c}²`; and at `β_N = ∞` (`invβ = 0`) the stochastic convolution
vanishes: `A_N = 1`, `q_N = 0`.  (Here `√(Nβ_N) = √(N/invβ_N)`.) -/
theorem interpretation_scaling (κ invβ : ℕ → ℝ) (hκ : ∀ N, 0 < κ N) (c : ℝ) (hc : 0 < c) :
    ((∀ N : ℕ, 1 ≤ N → 0 < invβ N) →
      Tendsto (fun N : ℕ => κ N / Real.sqrt ((N : ℝ) / invβ N)) atTop (𝓝 c) →
      Tendsto (fun N : ℕ => Ascale N (κ N) (invβ N)) atTop (𝓝 (min 1 c⁻¹)) ∧
      Tendsto (fun N : ℕ => qScale N (κ N) (invβ N)) atTop (𝓝 (min 1 c ^ 2))) ∧
    (∀ N : ℕ, invβ N = 0 → Ascale N (κ N) (invβ N) = 1 ∧ qScale N (κ N) (invβ N) = 0) := by
  refine ⟨fun hpos hlim => ?_, fun N hN => ?_⟩
  · have hA : ∀ᶠ N : ℕ in atTop, Ascale N (κ N) (invβ N) =
        min 1 (κ N / Real.sqrt ((N : ℝ) / invβ N))⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hi := hpos N hN
      unfold Ascale sigmaScale
      simp only [if_neg hi.ne']
      rw [← min_div_div_right (hκ N).le, div_self (hκ N).ne', inv_div]
    have hQ : ∀ᶠ N : ℕ in atTop, qScale N (κ N) (invβ N) =
        (min (κ N / Real.sqrt ((N : ℝ) / invβ N)) 1) ^ 2 := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hi := hpos N hN
      have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
      have hdiv : (0 : ℝ) < (N : ℝ) / invβ N := div_pos hNpos hi
      have ht : 0 < Real.sqrt ((N : ℝ) / invβ N) := Real.sqrt_pos.2 hdiv
      have ht2 : Real.sqrt ((N : ℝ) / invβ N) ^ 2 = (N : ℝ) / invβ N := Real.sq_sqrt hdiv.le
      have e1 : Real.sqrt ((N : ℝ) / invβ N) * (κ N / Real.sqrt ((N : ℝ) / invβ N)) = κ N := by
        field_simp
      have hmin : min (κ N) (Real.sqrt ((N : ℝ) / invβ N)) =
          Real.sqrt ((N : ℝ) / invβ N) * min (κ N / Real.sqrt ((N : ℝ) / invβ N)) 1 := by
        rw [mul_min_of_nonneg _ _ ht.le, e1, mul_one]
      unfold qScale sigmaScale
      simp only [if_neg hi.ne']
      rw [hmin, mul_pow, ht2]
      field_simp
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hA' : Tendsto (fun N : ℕ => min 1 (κ N / Real.sqrt ((N : ℝ) / invβ N))⁻¹) atTop
        (𝓝 (min 1 c⁻¹)) :=
      h1.min (hlim.inv₀ hc.ne')
    have hQ' : Tendsto (fun N : ℕ => (min (κ N / Real.sqrt ((N : ℝ) / invβ N)) 1) ^ 2) atTop
        (𝓝 ((min c 1) ^ 2)) :=
      (hlim.min h1).pow 2
    rw [min_comm c 1] at hQ'
    exact ⟨hA'.congr' (hA.mono fun N h => h.symm), hQ'.congr' (hQ.mono fun N h => h.symm)⟩
  · simp [Ascale, qScale, hN]

/-! ### Example A.16 -/

/-- Example A.16 `M:B:ex:deterministic` (TeX L10450-10466), deterministic data and dynamics.
`β_N = ∞` (`invβ = 0`), `X_N^0 = Y_N` deterministic, `κ_N(μ_{Y_N} - μ°) → η°` in `H^{-γ}`
(`hconv`; `ηin` is the deterministic `η°`, and `hη` identifies the functional `(R N).η` with it),
the statistics-level hypothesis A.4 (`hinit`), the standing assumptions A.1-A.3 with `r = γ+5`,
and the coefficient regularity/convergence of `main_torus_path` (`CoeffConvergence`, `lvl = γ+2`,
`m = γ`; it forces `L.invβ = 0`, `L.A = 1`, `L.invβstar = 0`, the limits of `invβ_N = 0`,
`A_N = 1`, `q_N = 0`).  The energy assumption A.6 is *replaced* by the zero-temperature reduction of
Proposition 3.36 (C1) (`B:prop:gronwall-catalog` item `cat-zero`, TeX L10457-10458): `Sym M ≤ 0`, a
transport bound `Λ'`, and smallness of `κ_N(F_N(Y_N,μ°) + 𝔬_N)` (`hsmall`), where `C₀` is a valid
completion constant (`hC : IsCoercivityPair d s C₀ Cc`, as in A.6, so that the corrected energy is
nonnegative).  Conclusion
(TeX L10459-10462): the whole trajectory `σ_NΞ_N^· = κ_NΞ_N^·` converges to the deterministic
solution `Y'` of the linearized equation with datum `η°`
(`IsLinearFluctuationSolution` with noise level `q = 0` and deterministic initial value) in
`C([0,T]; H^{-(γ+2)}(𝕋^d))` (convergence in law to a deterministic limit).  The assertion that the
initial coupling errors are deterministic distances is the definition of the errors.

**Statement repair (repaired 2026-10-17, ISSUES SPEC-C0B)**: completion-threshold prefix `∃ C₀min, ∀ … C₀ Cc, C₀min ≤ C₀ → …` as in ISSUES SPEC-C0, with `∃ C₀min` placed directly after `(s)` so that `C₀min` depends on `d, s` only (it is the `C₀` of `commutator_coercivity_common`; for `s ∉ [0,d)` no `MainData` exists); the remainder needs Prop 3.32, valid for that one threshold.

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): the added hypothesis `hfilt` is the filtered strong solution (`IsFilteredSolution`) of A.1 needed by the Itô/duality identity behind `main_torus_path`, which `SelectedFlowA1` (measurability only, ISSUES D1) does not record (`SelectedFlowA1.indep` already gives `IndepFun X₀ W`). -/
theorem deterministic_example (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB : ℝ) (C₀ Cc Λ' : ℝ), C₀min ≤ C₀ →
    ∀ (hC : IsCoercivityPair d s C₀ Cc)
    (S : MainData d) (hs : S.s = s) (hT : S.T = T) (hβ : ∀ N, S.invβ N = 0)
    (R : ∀ N, Realization d N)
    (hflow : SelectedFlows S R)
    (hfilt : ∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (hregime : S.RegimeHolds Rg ν₀)
    (hmf : MeanFieldRegularity S (gammaIdx d + 2 + 3) Λ)
    (hmat : PDE.MatBound MB S.M) (hV : PDE.VHyp (gammaIdx d + 2) VB S.V)
    (hsym : Torus.SymNonpos S.M)
    (hΛ' : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ')
    (Y : ∀ N, Config d N) (hdet : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P, (R N).X₀ ω = Y N)
    (ηin : NegSobolev d (gammaIdx d : ℝ))
    (hconv : Tendsto (fun N => S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
      (empirical (Y N)) S.μ0) atTop (𝓝 ηin))
    (hη : ∀ N : ℕ, 1 ≤ N → ∀ ω, ∀ ψ : Torus d → ℝ, MemSobolev (gammaIdx d : ℝ) ψ →
      Torus.mean ψ = 0 → (R N).η ω ψ = NegSobolev.eval ηin ψ)
    (m₀ : ℕ) (ε : ℕ → ℝ) (Cin : ℝ) (hinit : InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (hsmall : Tendsto (fun N => S.κ N * correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0)
      atTop (𝓝 0))
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d)),
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y' : ℝ → Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ)),
      IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) 0 T
        (fun _ => NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ) ηin) Y' →
      ConvergesInLaw
        (fun N => law (R N).P
          (flucPath ((gammaIdx d + 2 : ℕ) : ℝ) T (S.sigma N) (R N).X (S.ρ N)))
        (law P' (toPath ((gammaIdx d + 2 : ℕ) : ℝ) T Y')) := by
  sorry

/-- Example A.16, the sufficient scaling (TeX L10463-10466): if the corrected energy of `Y_N` is of the
usual microscopic order, `0 ≤ F_N(Y_N,μ°) + 𝔬_N ≤ B (N^{s/d-1} + 1_{s=0} (log N)/N)`, and
`κ_N (N^{s/d-1} + 1_{s=0}(log N)/N) → 0`, then `κ_N (F_N(Y_N,μ°) + 𝔬_N) → 0`. -/
theorem deterministic_scaling (s : ℝ) (κ E : ℕ → ℝ) (B : ℝ) (hκ : ∀ N, 0 < κ N)
    (hE0 : ∀ N, 0 ≤ E N)
    (hE : ∀ N : ℕ, 2 ≤ N → E N ≤ B * ((N : ℝ) ^ (s / d - 1) +
      (if s = 0 then Real.log N / N else 0)))
    (hscale : Tendsto (fun N : ℕ => κ N * ((N : ℝ) ^ (s / d - 1) +
      (if s = 0 then Real.log N / N else 0))) atTop (𝓝 0)) :
    Tendsto (fun N => κ N * E N) atTop (𝓝 0) := by
  refine squeeze_zero' (g := fun N : ℕ => B * (κ N * ((N : ℝ) ^ (s / d - 1) +
      (if s = 0 then Real.log N / N else 0)))) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun N => mul_nonneg (hκ N).le (hE0 N)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have h := mul_le_mul_of_nonneg_left (hE N hN) (hκ N).le
    exact h.trans_eq (by ring)
  · have h := hscale.const_mul B
    rw [mul_zero] at h
    exact h

/-! ### Proposition A.34 -/

/-- The second-moment part of A.4 for a random functional `η°` on `(Ω,P)` (used by Proposition A.34,
whose statement involves `η°` without listing its hypotheses: AMBIGUITY, the TeX uses the bounds of
A.4): measurable, real-linear on `Y_0 = H^{m₀}`, and `E|⟨ψ,η°⟩|² ≤ C_in² ‖ψ‖²_{H^{m₀}}` for
continuous `ψ ∈ Y_0`. -/
structure FunctionalMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (η : Ω → (Torus d → ℝ) → ℝ) (m₀ : ℕ) (Cin : ℝ) : Prop where
  η_meas : ∀ ψ : Torus d → ℝ, Measurable fun ω => η ω ψ
  linear : ∀ ω, ∀ ψ χ : Torus d → ℝ, ∀ c : ℝ, MemSobolev (m₀ : ℝ) ψ → MemSobolev (m₀ : ℝ) χ →
    η ω (c • ψ + χ) = c * η ω ψ + η ω χ
  second_moment : ∀ ψ : Torus d → ℝ, MemSobolev (m₀ : ℝ) ψ → Continuous ψ →
    ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P ≤ ENNReal.ofReal (Cin ^ 2 * sobolevNorm (m₀ : ℝ) ψ ^ 2)

/-- Proposition A.34 `M:B:prop:surrogate-to-limit` (i) (TeX L11439-11449), quantitative: two
coefficient sets (the `N`-th and the limit) in a common adjoint regime with `Δ_N^{(m)} → 0`
(`CoeffConvergence`, `lvl = m+2`).  For a terminal test with two derivatives above the base class
(`φ ∈ H^{m+2}`; `‖φ‖_{𝒳^{m+2}}` of the TeX, undefined there, is read as `‖φ‖_{H^{m+2}}`):
`W₁(𝔖_N^t[φ], 𝔖_∞^t[φ]) ≤ C e^{Λ_T t}‖φ‖_{H^{m+2}}(Δ_N^{(m)} + (Δ_N^{(m)})^{1/2})`
(AMBIGUITY: the TeX writes `e^{ΛT}`, read as `e^{Λ_T t}` of the other statements).  `η°` is any
random functional with the moment bound of A.4 (`FunctionalMoment`, `m₀ ≤ m`).
**Technical hypothesis**: `φ` continuous (the propagator `U^{0,t}φ` is the classical adjoint
solution, which needs a pointwise datum; `H^{m+2} ⊂ C²`).  **Statement repair 2026-10-16** (ISSUES "A34"):
`m_* ≤ m + 2`; the TeX defines the propagator `U^{r,t}φ` only for data at level `≥ m_*` (L1753), and below
it the Lean `propagator` is a junk value. -/
theorem surrogate_to_limit_stat (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (m m₀ : ℕ)
    (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (hmS : PDE.mStar d ≤ m + 2) :
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (L : LimitCoeffs d), CoeffConvergence S L Rg ν₀ MB Λ VB (m + 2) m →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Torus d → ℝ) → ℝ), FunctionalMoment P η m₀ Cin →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, MemSobolev ((m + 2 : ℕ) : ℝ) φ → Continuous φ →
      ∀ N : ℕ, 1 ≤ N →
        wassersteinE 1
          (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ) P η)
          (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ) P η) ≤
        ENNReal.ofReal (C * Real.exp (ΛT * t) * sobolevNorm ((m + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N))) := by
  by_cases hms : PDE.mStar d ≤ m + 2
  · obtain ⟨C, hC, h⟩ := HRS.A34.a34_stat_main s Rg ν₀ MB Λ T Cin VB m m₀ hm hm₀ hms
    refine ⟨C, 1, hC, one_pos, ?_⟩
    intro S hs hT L hcoef Ω _ P _ η hη t ht φ hφ hφc N hN
    refine (h S hs hT L hcoef P η ⟨hη.η_meas, hη.linear, hη.second_moment⟩ t ht φ hφ hφc N
      hN).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hΔ : 0 ≤ S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N) := by
      have h0 : 0 ≤ S.coeffDiscrepancy L m N := by
        have hAN := hcoef.seq_adjoint N hN
        have hAL := hcoef.limit_adjoint
        exact (HRS.A34.a34_delta_facts S L m N Rg ν₀ MB Λ VB hAN hAL).1
      positivity
    have h1 : 1 ≤ Real.exp (1 * t) := by
      rw [one_mul]; exact Real.one_le_exp ht.1
    have h2 : 0 ≤ C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ *
        (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N)) :=
      mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg _)) hΔ
    calc C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N))
        = 1 * (C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N))) := by ring
      _ ≤ Real.exp (1 * t) * (C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N))) :=
        mul_le_mul_of_nonneg_right h1 h2
      _ = _ := by ring
  · exact absurd hmS hms

/-- Proposition A.34 (i), "at the base regularity, convergence is qualitative" (TeX L11449): for
`φ ∈ H^m`, `W₁(𝔖_N^t[φ], 𝔖_∞^t[φ]) → 0`.  **Statement repair 2026-10-16** (ISSUES "A34"): `m_* ≤ m`, the
level at which the TeX propagator is defined (L1753). -/
theorem surrogate_to_limit_stat_base (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ)
    (m m₀ : ℕ) (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (hmS : PDE.mStar d ≤ m)
    (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (L : LimitCoeffs d) (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (m + 2) m)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Ω → (Torus d → ℝ) → ℝ) (hη : FunctionalMoment P η m₀ Cin)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : Torus d → ℝ) (hφ : MemSobolev (m : ℝ) φ)
    (hφc : Continuous φ) :
    Tendsto (fun N => wassersteinE 1
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ) P η)
      (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ) P η))
      atTop (𝓝 0) := by
  by_cases hmS' : PDE.mStar d ≤ m
  · exact HRS.A34.a34_base_main s Rg ν₀ MB Λ T VB Cin m m₀ hm₀ hmS S hs hT L hcoef P η
      ⟨hη.η_meas, hη.linear, hη.second_moment⟩ t ht φ hφ hφc
  · exact absurd hmS hmS'

/-- Proposition A.34 (ii) (TeX L11450-11459), fields, quantitative: with the output index `m = γ`,
common adjoint regime (`CoeffConvergence`, `lvl = γ+2`, `m = γ`) and the transported initial fields
satisfying `sup_{t' ≤ T} d_{C²}(Law 𝓘_N^{t'}, Law 𝓘_∞^{t'}) ≤ Cs Δ_N^{(γ)}`
(`B:eq:initial-limit-stability`; `η°` has the fixed law `νin`):
`d_{C²}(Law η_{N,lin}^t, Law η^t) ≤ C e^{Λ_T t}(Δ_N^{(γ)} + (Δ_N^{(γ)})^{1/2})`
in the field topology `H^{-γ}`; `C` depends on `Cs` as well. -/
theorem surrogate_to_limit_field (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB Cs : ℝ) :
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (L : LimitCoeffs d),
        CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d) →
      ∀ (νin : Measure (NegSobolev d (gammaIdx d : ℝ))), IsProbabilityMeasure νin →
        (∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) T,
          smoothDist 2
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              S.AN N • transportField (S.dyn N) (S.ρ N) t' (gammaIdx d : ℝ) F))
            (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
              L.A • transportField (L.dyn S) L.ρ t' (gammaIdx d : ℝ) F)) ≤
            Cs * S.coeffDiscrepancy L (gammaIdx d) N) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, 1 ≤ N →
      ∀ νG νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)),
        IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
        IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim →
        smoothDist 2
          (linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id νG)
          (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) ≤
        C * Real.exp (ΛT * t) *
          (S.coeffDiscrepancy L (gammaIdx d) N + Real.sqrt (S.coeffDiscrepancy L (gammaIdx d) N)) :=
  HRS.A34.a34_field_main s Rg ν₀ MB Λ T VB Cs

/-- Proposition A.34, fields, qualitative parts (TeX L11460): with `E‖η°‖²_{H^{-γ}} ≤ C_in²` and
`Δ_N^{(γ)} → 0`, the laws of `η_{N,lin}^t` converge weakly to the law of `η^t` in `H^{-γ'}` for every
`γ' > γ` (uniform moment bound and compactness); and in the base topology `H^{-γ}` provided the
transported initial fields converge in law there.  The sentence of the TeX on the comparison in the
topology weakened by two derivatives (L11460) gives no rate and is the case `γ' = γ+2 > γ` of the first
clause (no separate statement). -/
theorem surrogate_to_limit_field_qualitative (s : ℝ) (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ)
    (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) (hν : IsProbabilityMeasure νin)
    (hmom : ∫⁻ F, ‖F‖ₑ ^ 2 ∂νin ≤ ENNReal.ofReal (Cin ^ 2))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (νG : ℕ → Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνG : ∀ N : ℕ, 1 ≤ N →
      IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) (νG N))
    (νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)))
    (hνGlim : IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim) :
    (∀ γ' : ℝ, (gammaIdx d : ℝ) < γ' →
      ConvergesInLaw
        (fun N => (linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id (νG N)).map
          (NegSobolev.embed γ'))
        ((limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim).map (NegSobolev.embed γ'))) ∧
    (ConvergesInLaw
        (fun N => law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
          S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F))
        (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
          L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) →
      ConvergesInLaw
        (fun N => linearFieldLaw νin (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) id (νG N))
        (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim)) :=
  ⟨fun _ hγ' => HRS.A34.a34_qual_one s Rg ν₀ MB Λ T VB S hs hT L hcoef νin hν t ht νG hνG νGlim
      hνGlim hγ',
    HRS.A34.a34_qual_two s Rg ν₀ MB Λ T VB S hs hT L hcoef νin hν t ht νG hνG νGlim hνGlim⟩

end Main

end HRS
