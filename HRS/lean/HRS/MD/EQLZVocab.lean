import HRS.Appendix.B15DAux2
import HRS.Appendix.B15EAux1
import HRS.PDE.TorusFPExistAux4
import HRS.Stochastic.LyonsZhengSpec

/-!
# Vocabulary for the EQ-LZ packets (sorry-free)

Definitions used by the statements in `HRS.MD.EQLZ` (`HRS/MD/EQLZSpec.lean`, sorried, never imported by a packet) and by
the proofs.  Plan and dependency order: `HRS/MD/EQLZPlan.md`.  No new mathematics is defined here: every item is an
abbreviation of a formula that the repository already writes inline (`b15e_*`, `d1_*` and `IsStationaryGibbsFlow`).

* `IsSmoothCfg F`: `F : Config d N → ℝ` is `C^∞` as a function on the big torus `𝕋^{N d}` (through `d1_configEquiv`).
* `levelProc Y t ω`: the level-`lev` regularised process `e(mk ∘ Y_t)` on `𝕋^{N d}`.
* `IsLevelFlow D lev P ℱ W' Y₀ Y`: `Y` is the strong solution of the level-`lev` regularised gradient SDE on the covering
  space (`dY = b15c_liftedDriftReg D lev (Y) dt + liftedNoise D dW'`), in a Brownian filtration, with `ℱ_t`-measurable
  initial lift `Y₀` (exactly the hypotheses of `b15e_exists_regularised` / `b15d_law_eq_fp`).
* `fddProd`, `fddKer`, `HasFDD`: the finite-dimensional-distribution identity of a Markov process with semigroup `d1_P`:
  for gaps `δ_1,...,δ_k ≥ 0` and smooth `g_1,...,g_k` and bounded measurable `g_0`,
  `E g_0(Z_0) ∏_i g_i(Z_{δ_1+...+δ_i}) = ∫ g_0 · P_{δ_1}(g_1 · P_{δ_2}(g_2 ⋯ P_{δ_k} g_k)) dν`, `ν` the law of `Z_0`.
* `LevelMaximal`, `SmoothMaximal`: the statements of the two intermediate packets `eqlz_level`, `eqlz_smooth` (kept as
  `Prop`s so that the next packet can take them as a hypothesis without a Pi-type chain).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

namespace MD

namespace EQLZ

variable {d N n : ℕ}

/-! ### Smooth test functions on configurations -/

/-- `F : Config d N → ℝ` is `C^∞` on the big torus `𝕋^{N d} ≃ Config d N` (`d1_configEquiv`). -/
def IsSmoothCfg (F : Config d N → ℝ) : Prop :=
  Torus.IsSmooth (fun x : Torus (N * d) => F ((d1_configEquiv d N).symm x))

/-! ### The level-`lev` regularised flow -/

/-- The torus-valued process `t ↦ e(mk ∘ Y_t)` (`e = d1_configEquiv`), `Y` a path on the covering space. -/
def levelProc {Ω : Type*} (Y : ℝ → Ω → Fin N → Euc d) (t : ℝ) (ω : Ω) : Torus (N * d) :=
  d1_configEquiv d N (fun i => Torus.mk (Y t ω i))

/-- `Y` is the (strong) solution of the level-`lev` regularised gradient SDE `dY = b^{lev}(Y) dt + √(2 D.invβ) dW'` in a
Brownian filtration `ℱ`, with initial lift `Y₀` adapted at every time (hypotheses of `b15e_exists_regularised`). -/
structure IsLevelFlow (D : DynData d) (lev : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Y₀ : Ω → Fin N → Euc d)
    (Y : ℝ → Ω → Fin N → Euc d) : Prop where
  brownian : IsBrownianFiltration P ℱ W'
  init_adapted : ∀ t : ℝ, Measurable[ℱ t] Y₀
  sol : IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D lev) (liftedNoise D) Y₀
    (fun _ => ⊤) Y

/-! ### Finite-dimensional distributions of a `d1_P`-Markov process -/

section FDD

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)

/-- The product `∏_i g_i(Z_{t+δ_1+...+δ_i})` along a list `[(δ_1,g_1),...,(δ_k,g_k)]` of (gap, function) pairs,
started at time `t`. -/
def fddProd {Ω : Type*} (Z : ℝ → Ω → Torus n) : ℝ → List (ℝ × (Torus n → ℝ)) → Ω → ℝ
  | _, [], _ => 1
  | t, p :: l, ω => p.2 (Z (t + p.1) ω) * fddProd Z (t + p.1) l ω

/-- The iterated kernel `P_{δ_1}(g_1 · P_{δ_2}(g_2 ⋯ P_{δ_k}(g_k)))` (the empty list gives the constant `1`). -/
def fddKer : List (ℝ × (Torus n → ℝ)) → Torus n → ℝ
  | [] => fun _ => 1
  | p :: l => d1_P hn hκ hU p.1 (fun x => p.2 x * fddKer l x)

/-- `Z` has the finite-dimensional distributions of the `d1_P`-Markov process with initial law `ν`: for every list of
nonnegative gaps and smooth functions and every bounded measurable `g₀`,
`E[g₀(Z_0) ∏ g_i(Z_{δ_1+...+δ_i})] = ∫ g₀ · fddKer dν`. -/
def HasFDD {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ → Ω → Torus n) (ν : Measure (Torus n)) :
    Prop :=
  ∀ l : List (ℝ × (Torus n → ℝ)), (∀ p ∈ l, 0 ≤ p.1 ∧ Torus.IsSmooth p.2) →
    ∀ g₀ : Torus n → ℝ, Measurable g₀ → (∃ C : ℝ, ∀ x, |g₀ x| ≤ C) →
      ∫ ω, g₀ (Z 0 ω) * fddProd Z 0 l ω ∂P = ∫ x, g₀ x * fddKer hn hκ hU l x ∂ν

end FDD

/-! ### The two intermediate statements -/

/-- (Statement of packet `eqlz_level`.)  Maximal inequality on a uniform grid for a smooth statistic of the level-`lev`
regularised flow, started from a law dominated by the level Gibbs law: if `Law(Z_0) = ρ · π_lev` with `0 ≤ ρ ≤ c`
(`π_lev = d1_gibbsMeasure D.invβ (b15d_U D lev)`, `Z = levelProc Y`), then for every smooth `F` on `𝕋^{N d}`, `a, T ≥ 0`
and every `m ≥ 1`,
`E max_{0≤j≤m} (F(Z_{a+jT/m}) - F(Z_a))² ≤ c · 40 · T · κ ∫|∇F|² dπ_lev` (`κ = D.invβ`).
The constant `40` is absolute (it does not depend on `m`, `lev`, `N`, `d`, `V`, `κ`, `c`, `F`). -/
def LevelMaximal : Prop :=
  ∀ (d N : ℕ) (_ : 1 ≤ N * d) (D : DynData d), D.M = -(1 : Matrix (Fin d) (Fin d) ℝ) →
    Torus.IsSmooth D.V → 0 < D.invβ → ∀ (lev : ℝ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (Y₀ : Ω → Fin N → Euc d)
    (Y : ℝ → Ω → Fin N → Euc d), IsLevelFlow D lev P ℱ W' Y₀ Y →
    ∀ (c : ℝ) (ρ : Torus (N * d) → ℝ), Measurable ρ → (∀ x, 0 ≤ ρ x ∧ ρ x ≤ c) →
      P.map (levelProc Y 0) =
        (d1_gibbsMeasure D.invβ (b15d_U (N := N) D lev)).withDensity (fun x => ENNReal.ofReal (ρ x)) →
    ∀ F : Torus (N * d) → ℝ, Torus.IsSmooth F → ∀ a T : ℝ, 0 ≤ a → 0 ≤ T → ∀ m : ℕ, 1 ≤ m →
      ∫⁻ ω, ⨆ j : Fin (m + 1),
          ENNReal.ofReal ((F (levelProc Y (a + (j : ℕ) * (T / m)) ω) - F (levelProc Y a ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (c * (40 * T * D.invβ *
          ∫ x, ‖Torus.grad F x‖ ^ 2 ∂(d1_gibbsMeasure D.invβ (b15d_U (N := N) D lev))))

/-- (Statement of packet `eqlz_smooth`.)  The frozen Lyons-Zheng inequality `lyonsZheng_maximal` restricted to
smooth test functions `F` (`IsSmoothCfg`), with an absolute constant. -/
def SmoothMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ), 2 ≤ d → 2 ≤ N → ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ), Torus.IsSmooth V → ∀ (β : ℝ) (hβ : 0 < β) (T a : ℝ), 0 ≤ T → 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
        ∀ F : Config d N → ℝ, IsSmoothCfg F →
          ∫⁻ ω, ⨆ t ∈ LZ.ratTimes a T,
              ENNReal.ofReal
                ((F (X t.toNNReal ω) - ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2) ∂P ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal (∫ Y, (F Y -
                  ∫ Y', F Y' ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2
                    ∂(canonicalGibbs (periodicRiesz d s) V N β)) +
                ENNReal.ofReal (β⁻¹ * T) *
                  ENNReal.ofReal (∫ Y, LZ.configGradSq F Y
                    ∂(canonicalGibbs (periodicRiesz d s) V N β)))

end EQLZ

end MD

end HRS

end
