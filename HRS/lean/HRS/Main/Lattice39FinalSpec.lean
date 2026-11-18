import HRS.Main.TorusTheorems
import HRS.Dynamics.InitialData

/-!
# Example A.39 (perturbed lattice): the FINAL form, without the domination hypothesis (SPEC ONLY)

Statements only (every proof is `sorry`).  Source: `HRS_periodic_main_20261008T010000Z.tex`, Example
`M:B:ex:lattice` (L11608-11612); plan `docs/MAIN_A_PLAN_A39_513_cubic.md` section 1 (D1-D4); interim form
`HRS/Main/Lattice39Spec.lean` (`perturbedLattice_linearization`, proved in `Lattice39Main.lean`).

The interim form assumes `hdom` (`εf (n^d) ≤ K(κ⁻¹ + κ N^{-2/d})`, `𝔈 (n^d) ≤ K(κ⁻² + N^{s/d-1})`).  Here it is
removed: at `N = n^d` (`n ≥ max 2 n₁`) the field-level (A.5), statistics-level (A.4) and energy (A.6)
packages are DERIVED from the lattice (`perturbedLattice_stat`, `perturbedLattice_field`,
`perturbedLattice_energy`, Proposition 3.36 (C1) via `det16_pathwise_energy`); they are ASSUMED only at the
other `N` (`N ∉ lattice39fSet d n₁`), because `Realization d N`, `InitialFluctuation*`, `EnergySmallness`
quantify over all `N ≥ 1` while lattices exist only for `N = n^d` (plan, decision 1; A.8-A.11 cannot be
applied to a subsequence).

Layout: D2 (field moments), D1 (statistics-level `I2` and assembly of `InitialFluctuation`), D2' (assembly of
`InitialFluctuationField`), D3 (energy at lattice `N`), G (glue of `EnergySmallness`), then
`perturbedLattice_linearization_final`.

Proof plan of the final theorem (not formalised here): take `C₀min` as the max of the A.9 threshold
(`main_torus_field_proof`) and the `Det16` threshold (`det16_pathwise_energy`); given `S`, build
`𝔈' N := if N ∈ lat then 𝔈L N else 𝔈 N`, `εf' N := if N ∈ lat then Cf (κ⁻¹ + κ N^{-2/d}) else εf N`,
`Cin' := max Cin (sup over the finitely many lattice N with small κ or large field moment)` (this `Cin'` depends
on `S`, hence on `S` also the A.9 constants; the exported `ΛT` is cosmetic, see below), apply D1-D3 and the
glue lemmas to obtain `TorusStanding`, `InitialFluctuation`, `InitialFluctuationField` for the primed data,
check the domination `hdom` for them and apply `perturbedLattice_linearization_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Data -/

/-- The set of lattice particle numbers `{n^d : n ≥ max 2 n₁}` at which the lattice hypothesis is imposed
(`n₁` arbitrary: for small `n` the perturbed lattice may have collisions, which `TorusStanding.flow` excludes). -/
def lattice39fSet (d n₁ : ℕ) : Set ℕ := {N | ∃ n : ℕ, max 2 n₁ ≤ n ∧ N = n ^ d}

/-- The deterministic initial field `η° = -div a ∈ H^{-γ}`, `γ = gammaIdx d`. -/
def lattice39fEta (a : Torus d → Euc d) : NegSobolev d (gammaIdx d : ℝ) :=
  NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)

/-! ### D2: field-level moments of the perturbed lattice (A.5 at `N = n^d`) -/

/-- D2 (A.5 at a lattice `N = n^d`, from `perturbedLattice_field`).  For smooth `a` there is `Cf ≥ 0`
(depending on `d` and `‖a‖_{C¹}`) such that for every `n ≥ 1`, `κ > 0` and every probability space on which
`X₀ = perturbedLattice n κ a` a.s., with `μ° = volume` and `η° = -div a`:
`E‖κ Ξ - η°‖_{H^{-γ}} ≤ Cf(κ⁻¹ + κ N^{-2/d})` (so `εf_N := Cf(κ⁻¹ + κ N^{-2/d})`), and the second moment
`E‖κΞ‖² + E‖η°‖²` is at most `(‖η°‖ + εf_N)² + ‖η°‖²` (uniformly bounded once `εf_N` is). -/
theorem lattice39f_field_moments (hd : 1 ≤ d) (a : Torus d → Euc d) (ha : Torus.IsSmooth a) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d (n ^ d)), (∀ᵐ ω ∂P, X₀ ω = perturbedLattice n κ a) →
      ∫⁻ ω, ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (X₀ ω)) volume -
          lattice39fEta a‖ₑ ∂P ≤
        ENNReal.ofReal (Cf * (κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))) ∧
      ∫⁻ ω, ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (X₀ ω)) volume‖ₑ ^ 2 ∂P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((‖lattice39fEta a‖ +
          Cf * (κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))) ^ 2 + ‖lattice39fEta a‖ ^ 2) := by
  sorry

/-! ### D1: statistics-level moment (A.4 `I2`) and assembly of `InitialFluctuation` -/

/-- D1 (`I2` at a lattice `N = n^d`, `m₀ = m_* = mStar d`).  For smooth `a` there is `Ca ≥ 0` such that for all
`n ≥ 1`, `κ > 0`, every `Cin ≥ Ca(1 + κ⁻¹ + κ N^{-2/d})`, every probability space with `X₀ = perturbedLattice n κ a`
a.s. and the deterministic functional `η ω ψ = ∫ ψ·(-div a)`, and every continuous `ψ ∈ H^{m_*}`:
`E|κ⟨ψ, μ_{X₀} - 1⟩|² + E|η ψ|² ≤ Cin² ‖ψ‖²_{H^{m_*}}`.  (Route: `perturbedLattice_stat`, or
`perturbedLattice_field` at level `m_*` with `abs_pair_sub_le`; `H^{m_*} ↪ C²` since `m_* > d/2 + 2`
(`cbNorm_le_sobolevNorm`).  `m₀ = m_*` is the weakest case: I2 at `m₀ < m_*` implies I2 at `m_*`; for small `m₀` with
`H^{m₀} ⊄ C²` the statistic bound `κ|⟨ψ, μ_{Y_N} - 1⟩|` is not controlled by `‖ψ‖_{H^{m₀}}` in general, so the
final statement fixes `m₀ = m_*`.) -/
theorem lattice39f_I2 (hd : 1 ≤ d) (a : Torus d → Euc d) (ha : Torus.IsSmooth a) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ →
    ∀ Cin : ℝ, Ca * (1 + κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ≤ Cin →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d (n ^ d)) (η : Ω → (Torus d → ℝ) → ℝ),
      (∀ᵐ ω ∂P, X₀ ω = perturbedLattice n κ a) →
      (∀ ω ψ, η ω ψ = ∫ x, ψ x * (-Torus.div a x)) →
      ∀ ψ : Torus d → ℝ, MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
        ∫⁻ ω, ENNReal.ofReal ((κ * (pair (empirical (X₀ ω)) ψ - pair volume ψ)) ^ 2) ∂P +
          ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P ≤
        ENNReal.ofReal (Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2) := by
  sorry

/-- D1' (assembly of A.4).  If the functional `η°` is the deterministic `ψ ↦ ∫ ψ·(-div a)` for every `N`,
the flows satisfy A.1 (this gives `X₀ ⫫ W`), `1 ≤ Cin`, and the second-moment bound `I2` holds at every `N ≥ 1`
(derived by D1 at lattice `N`, assumed at the other `N`), then `InitialFluctuation S R m_* Cin 0 ∅` holds
(`ε = 0`, `Ψ = ∅`, so `I1` is void; `linear`, `η_meas`, `fixed_law` (the law is a Dirac mass), `I3`
(`η` constant, `X₀ ⫫ W` from `SelectedFlowA1.indep`) are consequences). -/
theorem lattice39f_initialFluctuation_of_I2 (S : MainData d) (R : ∀ N, Realization d N)
    (a : Torus d → Euc d) (ha : Torus.IsSmooth a) (Cin : ℝ) (hCin : 1 ≤ Cin)
    (hη : ∀ (N : ℕ) (ω : (R N).Ω) (ψ : Torus d → ℝ), (R N).η ω ψ = ∫ x, ψ x * (-Torus.div a x))
    (hflow : SelectedFlows S R)
    (hI2 : ∀ N : ℕ, 1 ≤ N → ∀ ψ : Torus d → ℝ, MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
      ∫⁻ ω, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ)) ^ 2)
          ∂(R N).P +
        ∫⁻ ω, ENNReal.ofReal (((R N).η ω ψ) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2)) :
    InitialFluctuation S R (PDE.mStar d) Cin (fun _ => 0) (fun _ => ∅) := by
  sorry

/-! ### D2': assembly of `InitialFluctuationField` -/

/-- D2' (assembly of A.5).  If `η°` is deterministic as above (`η ω ψ = ∫ ψ·(-div a)` and `ηF = -div a`, both
for every `N`; `compat` then follows from `eval (ofFun γ f) ψ = ∫ ψ f` for mean-zero `ψ ∈ H^γ`), `εf ≥ 0`, and
the first and second field moments hold at every `N ≥ 1` (derived by D2 at lattice `N`, assumed at the other
`N`), then `InitialFluctuationField S R γ Cin εf (fun _ _ => -div a) (δ_{-div a})` (`law_eq`: a constant has a
Dirac law). -/
theorem lattice39f_initialFluctuationField_of_moments (S : MainData d) (R : ∀ N, Realization d N)
    (a : Torus d → Euc d) (ha : Torus.IsSmooth a) (Cin : ℝ) (εf : ℕ → ℝ)
    (hη : ∀ (N : ℕ) (ω : (R N).Ω) (ψ : Torus d → ℝ), (R N).η ω ψ = ∫ x, ψ x * (-Torus.div a x))
    (hεf : ∀ N : ℕ, 1 ≤ N → 0 ≤ εf N)
    (h1 : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
          lattice39fEta a‖ₑ ∂(R N).P ≤ ENNReal.ofReal (εf N))
    (h2 : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
          ∂(R N).P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2)) :
    InitialFluctuationField S R (gammaIdx d) Cin εf (fun _ _ => lattice39fEta a)
      (Measure.dirac (lattice39fEta a)) := by
  sorry

/-! ### D3: the energy bound at a lattice `N = n^d` (A.6 at `N = n^d`) -/

/-- D3 (energy at lattice `N`; `perturbedLattice_energy` + Proposition 3.36 (C1) via `det16_pathwise_energy`).
Zero temperature (`invβ = 0`), `d ≥ 1` (hypothesis `hd2 : 1 ≤ d`; the binder name is historical), `Sym M ≤ 0` (`Torus.SymNonpos`), a transport bound `Λ'` for the drift
`meanFieldDrift (S.dyn N) (S.ρ N t)` (`N ≥ 1`, `t ∈ [0,T]`), mean-field regularity (A.3 at level `γ+3`),
`V ∈ C^γ` (`VHyp`), `μ° = volume`, A.1 flows (at `invβ = 0` the Cépa–Lépingle and `M = 0` branches of A.1 require `0 < invβ`, so
`Det16.det16c_strong` gives `IsStrongSolution` for every `d ≥ 1`) and the lattice initial datum at `N = n^d`, `n ≥ 2`:
(i) if `κ_N ≥ κ₀` (`κ₀, Ke` depend on `d, s, C₀, Λ, T, Λ', a` but not on `S, R, n`) then for `t ∈ [0,T]`
`E[F_N(X_N^t, μ^t) + 𝔬_N(Λ)] ≤ Ke(κ⁻² + N^{s/d-1})` (the `lintegral` form of `EnergySmallness.bound`);
(ii) for every `n ≥ 2` (no lower bound on `κ_N`) the left side is bounded by some finite `B`
(`S, R, n`-dependent: the initial energy of a collision-free lattice is finite, `X₀` collision-free a.s. by A.1).
The threshold `C₀min` is the `Det16` one (`C₀ ≥ C₀min` is needed for the monotone passage from the C1
constant to a general `C₀`). -/
theorem lattice39f_energy (hd2 : 1 ≤ d) (s : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (Λ T VB Λ' : ℝ) (a : Torus d → Euc d),
    Torus.IsSmooth a → ∃ κ₀ Ke : ℝ, 0 < κ₀ ∧ 0 ≤ Ke ∧
    ∀ (S : MainData d), S.s = s → S.T = T → S.μ0 = volume → (∀ N : ℕ, S.invβ N = 0) →
    Torus.SymNonpos S.M →
    (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    MeanFieldRegularity S (gammaIdx d + 3) Λ → PDE.VHyp (gammaIdx d) VB S.V →
    ∀ (R : ∀ N, Realization d N), SelectedFlows S R →
    ∀ n : ℕ, 2 ≤ n → (∀ᵐ ω ∂(R (n ^ d)).P, (R (n ^ d)).X₀ ω = perturbedLattice n (S.κ (n ^ d)) a) →
      (κ₀ ≤ S.κ (n ^ d) → ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ENNReal.ofReal
            (correctedEnergy (S.dyn (n ^ d)) C₀ Λ (S.ρ (n ^ d)) ((R (n ^ d)).X (Real.toNNReal t) ω) t)
          ∂(R (n ^ d)).P ≤
        ENNReal.ofReal (Ke * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)))) ∧
      (∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ENNReal.ofReal
            (correctedEnergy (S.dyn (n ^ d)) C₀ Λ (S.ρ (n ^ d)) ((R (n ^ d)).X (Real.toNNReal t) ω) t)
          ∂(R (n ^ d)).P ≤ ENNReal.ofReal B) := by
  sorry

/-! ### G: glue of `EnergySmallness` (lattice `N` derived, other `N` assumed) -/

open Classical in
/-- G (assembly of A.6 from a lattice part and an off-lattice part).  `𝔈 N` is assumed at the `N ∉ lat`
(positivity, bound, and smallness along `N ∉ lat`), `𝔈L N` is the lattice bound (D3) at `N ∈ lat`; then
`EnergySmallness` holds for `𝔈' N = if N ∈ lat then 𝔈L N else 𝔈 N`.  (Smallness: the two indicator
sequences tend to `0` and add up to `σ_N 𝔈'_N`.) -/
theorem lattice39f_energySmallness_glue (S : MainData d) (R : ∀ N, Realization d N) (C₀ Cc Λ : ℝ)
    (lat : Set ℕ) (𝔈 𝔈L : ℕ → ℝ) (hC : IsCoercivityPair d S.s C₀ Cc)
    (hpos : ∀ N : ℕ, 1 ≤ N → N ∉ lat → 0 < 𝔈 N)
    (hbd : ∀ N : ℕ, 1 ≤ N → N ∉ lat → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
        ENNReal.ofReal (𝔈 N))
    (hsm : Tendsto (Set.indicator latᶜ (fun N : ℕ => S.sigma N * 𝔈 N)) atTop (𝓝 0))
    (hposL : ∀ N : ℕ, 1 ≤ N → N ∈ lat → 0 < 𝔈L N)
    (hbdL : ∀ N : ℕ, 1 ≤ N → N ∈ lat → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
        ENNReal.ofReal (𝔈L N))
    (hsmL : Tendsto (Set.indicator lat (fun N : ℕ => S.sigma N * 𝔈L N)) atTop (𝓝 0)) :
    EnergySmallness S R C₀ Cc Λ (fun N => if N ∈ lat then 𝔈L N else 𝔈 N) := by
  sorry

/-! ### Example A.39, final form -/

/-- Example A.39 `M:B:ex:lattice` (TeX L11608-11612), conclusion, FINAL form (no domination hypothesis).

The conclusion is that of `perturbedLattice_linearization` (the exported exponent `ΛT` is cosmetic: `t ∈ [0,T]`
and `K'` may depend on everything but `t`, so `e^{ΛT t}` is absorbed in `K'`; it is kept for shape).

Hypotheses ADDED relative to the interim form `perturbedLattice_linearization`:
* `hd2 : 1 ≤ d` (the binder name is historical: the statement was widened from `2 ≤ d` on 2026-10-20 after review, once `perturbedLattice_energy` was proved for `1 ≤ d`);
* `hsym : Torus.SymNonpos S.M`, `hΛ' : HasTransportBound … Λ'` (zero-temperature reduction, Proposition 3.36
  (C1); cf. `deterministic_example`), with `Λ'` quantified after `S`;
* `hC : IsCoercivityPair d s C₀ Cc` (this is the `completion` field of `EnergySmallness`; a statement about
  `(C₀, Cc)` only, as in `deterministic_example`);
* `hη` : the realisation's functional `η°` is the deterministic functional `ψ ↦ ∫ ψ·(-div a)` for every `N`
  (identification of `η°` with `-Div a`; `compat` of A.5 only ties `η` to `ηF` on mean-zero `H^γ`, whereas A.4
  (`linear`, `fixed_law`, `I2`) constrains `η` on `H^{m₀}`, so it cannot be derived).

Hypotheses REMOVED or WEAKENED relative to the interim form (so the new statement is strictly closer to the TeX):
* `hdom` (the domination) is gone, together with the variables `m₀, ε, ηF, νin` (now `m₀ := m_* = mStar d`,
  `ε := 0`, `Ψ := ∅`, `ηF := -div a`, `νin := δ_{-div a}`; `ηF N ω = -div a` was an interim hypothesis for all `N`);
* `TorusStanding` is replaced by its fields `flow, filtered, regime, mean_field, matrix_bound, potential` for ALL
  `N ≥ 1` (A.1-A.3 are not derivable from the lattice: strong solutions, mean-field regularity are standing
  assumptions), WITHOUT the field `energy`;
* A.4: only `I2` is assumed, and only at `N ∉ lattice39fSet d n₁` (`hI2off`); `m₀_pos, m₀_le, Cin_ge`
  (`hCin : 1 ≤ Cin`), `eps_*`, `family_finite`, `linear, η_meas, fixed_law, I1, I3` are derived (D1');
* A.5: only `first_moment, second_moment, εf ≥ 0` are assumed, only at `N ∉ lattice39fSet d n₁` (`hfieldoff`);
  `ηF_meas, law_eq, compat` are derived (D2'); at `N ∈ lattice39fSet d n₁` D2 gives them;
* A.6: `pos, bound` assumed only at `N ∉ lattice39fSet d n₁`, `small` only along `N ∉ lattice39fSet d n₁`
  (`henergyoff`, `hsmoff`); at `N ∈ lattice39fSet d n₁` D3 gives them, `small` there from `hκ1, hκ3`.

The constants `εf` (A.5) and `𝔈` (A.6) occur ONLY in the off-lattice hypotheses and not in the conclusion
(there is no rate hypothesis).  `Cin` is quantified before `a` as in A.9; D1/D2 need `Cin ≥ Ca(a)(1 + κ⁻¹ + κ N^{-2/d})`
only at lattice `N`, and this is absorbed in the proof by replacing `Cin` by `Cin' = max Cin (…)` (depends on `S`
through finitely many lattice `N`; the A.9 constants then depend on `S`, which is why `ΛT` is cosmetic). -/
theorem perturbedLattice_linearization_final (s : ℝ) (hd2 : 1 ≤ d) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (a : Torus d → Euc d), Torus.IsSmooth a →
    ∃ ΛT : ℝ, 0 < ΛT ∧
    ∀ (S : MainData d), S.s = s → S.T = T → S.μ0 = volume → (∀ N : ℕ, S.invβ N = 0) →
    (∀ (N M : ℕ) (t : ℝ), S.ρ N t = S.ρ M t) →
    ∀ (R : ∀ N, Realization d N) (𝔈 εf : ℕ → ℝ) (Λ' : ℝ) (n₁ : ℕ),
    -- A.1-A.3 (the fields of `TorusStanding` other than `energy`), all `N ≥ 1`
    SelectedFlows S R →
    (∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) →
    S.RegimeHolds Rg ν₀ → MeanFieldRegularity S (gammaIdx d + 3) Λ →
    PDE.MatBound MB S.M → PDE.VHyp (gammaIdx d) VB S.V →
    -- tacit TeX hypotheses (zero-temperature reduction, Proposition 3.36 (C1)) and the completion pair
    Torus.SymNonpos S.M →
    (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    IsCoercivityPair d s C₀ Cc →
    -- the data: `η° = -div a`, deterministic, for every `N`; `1 ≤ Cin`
    1 ≤ Cin →
    (∀ (N : ℕ) (ω : (R N).Ω) (ψ : Torus d → ℝ), (R N).η ω ψ = ∫ x, ψ x * (-Torus.div a x)) →
    -- the lattice and the scales (as in the interim form)
    (∀ n : ℕ, max 2 n₁ ≤ n → ∀ᵐ ω ∂(R (n ^ d)).P,
      (R (n ^ d)).X₀ ω = perturbedLattice n (S.κ (n ^ d)) a) →
    Tendsto (fun n : ℕ => S.κ (n ^ d)) atTop atTop →
    Tendsto (fun n : ℕ => S.κ (n ^ d) / (n : ℝ)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) atTop (𝓝 0) →
    -- A.4 (`I2`, `m₀ = m_*`), assumed only off the lattice
    (∀ N : ℕ, 1 ≤ N → N ∉ lattice39fSet d n₁ → ∀ ψ : Torus d → ℝ,
      MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
      ∫⁻ ω, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ)) ^ 2)
          ∂(R N).P +
        ∫⁻ ω, ENNReal.ofReal (((R N).η ω ψ) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2)) →
    -- A.5 (field moments), assumed only off the lattice
    (∀ N : ℕ, 1 ≤ N → N ∉ lattice39fSet d n₁ → 0 ≤ εf N ∧
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
          lattice39fEta a‖ₑ ∂(R N).P ≤ ENNReal.ofReal (εf N) ∧
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
          ∂(R N).P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2)) →
    -- A.6 (`pos`, `bound`, `small`), assumed only off the lattice
    (∀ N : ℕ, 1 ≤ N → N ∉ lattice39fSet d n₁ → 0 < 𝔈 N ∧
      ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        ∫⁻ ω, ENNReal.ofReal
            (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
          ENNReal.ofReal (𝔈 N)) →
    Tendsto (Set.indicator (lattice39fSet d n₁)ᶜ (fun N : ℕ => S.sigma N * 𝔈 N)) atTop (𝓝 0) →
    (∃ (K' : ℝ) (n₀ : ℕ), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, n₀ ≤ n →
      smoothDist 2
        (particleFieldLaw (R (n ^ d)).P (S.sigma (n ^ d)) (gammaIdx d : ℝ) (R (n ^ d)).X
          (S.ρ (n ^ d)) t)
        (Measure.dirac (transportField (S.dyn (n ^ d)) (S.ρ (n ^ d)) t (gammaIdx d : ℝ)
          (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)))) ≤
      K' * Real.exp (ΛT * t) *
        ((S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1))) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      ConvergesInLaw
        (fun n : ℕ => particleFieldLaw (R (n ^ d)).P (S.sigma (n ^ d)) (gammaIdx d : ℝ)
          (R (n ^ d)).X (S.ρ (n ^ d)) t)
        (Measure.dirac (transportField (S.dyn 1) (S.ρ 1) t (gammaIdx d : ℝ)
          (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x))))) := by
  sorry

end Main

end HRS
