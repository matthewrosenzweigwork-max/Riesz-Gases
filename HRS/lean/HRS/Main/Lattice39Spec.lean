import HRS.Main.TorusTheorems
import HRS.Dynamics.InitialData

/-!
# Example A.39 (perturbed lattice): statement of the linearisation conclusion (SPEC ONLY)

Statements only (every proof is `sorry`).  Source: `HRS_periodic_main_20261008T010000Z.tex`,
Example `M:B:ex:lattice` (L11608-11612); plan `docs/MAIN_A_PLAN_A39_513_cubic.md`, section 1.

Lemma D4 (`lattice39_*`): the zero-noise (`q = 0`) Gaussian is the Dirac mass at `0`, and the linear
field law with deterministic initial field is a Dirac mass; plus the scale/rate algebra at `β = ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Lemma D4 -/

/-- D4(a): at noise level `q = 0` the covariance `noiseCovariance` vanishes (it has the factor `2q`). -/
theorem lattice39_noiseCovariance_zero (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ)
    (φ ψ : Torus d → ℝ) : noiseCovariance D ρ 0 t φ ψ = 0 := by
  sorry

/-- D4(b): the Dirac mass at `0` is the centered Gaussian field law of covariance
`noiseCovariance D ρ 0 t` (`IsLinearFieldNoise` with `q = 0`). -/
theorem lattice39_dirac_isLinearFieldNoise (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t γ : ℝ) :
    IsLinearFieldNoise D ρ 0 t γ (Measure.dirac (0 : NegSobolev d γ)) := by
  sorry

/-- D4(c): `linearFieldLaw` with a deterministic initial field `F` and noise law `δ_0` is the Dirac
mass at `A • V^{t,0} F`. -/
theorem lattice39_linearFieldLaw_dirac {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A t γ : ℝ)
    (F : NegSobolev d γ) (η : Ω → NegSobolev d γ) (hη : ∀ ω, η ω = F) :
    linearFieldLaw P D ρ A t γ η (Measure.dirac (0 : NegSobolev d γ)) =
      Measure.dirac (A • transportField D ρ t γ F) := by
  sorry

/-- D4(d): at `β_N = ∞` (`invβ N = 0`), `(σ_N, A_N, q_N) = (κ_N, 1, 0)`. -/
theorem lattice39_scales_of_invβ_zero (S : MainData d) (N : ℕ) (h : S.invβ N = 0) :
    S.sigma N = S.κ N ∧ S.AN N = 1 ∧ S.qN N = 0 := by
  sorry

/-- D4(e): rate algebra.  At `q = 0`, `σ = κ > 0`, the domination `εf ≤ K(κ⁻¹ + κ N^{-2/d})`,
`𝔈 ≤ K((κ⁻¹)² + N^{s/d-1})` (`0 ≤ K`) gives
`fieldRate d εf 0 κ 𝔈 N ≤ 2K(κ⁻¹ + κ N^{-2/d} + κ N^{s/d-1})`. -/
theorem lattice39_fieldRate_le (s κ K εf 𝔈 : ℝ) (N : ℕ) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hN : 1 ≤ N)
    (hεf : εf ≤ K * (κ⁻¹ + κ * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ))))
    (h𝔈 : 𝔈 ≤ K * ((κ⁻¹) ^ 2 + (N : ℝ) ^ (s / (d : ℝ) - 1))) :
    fieldRate d εf 0 κ 𝔈 N ≤
      2 * K * (κ⁻¹ + κ * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) + κ * (N : ℝ) ^ (s / (d : ℝ) - 1)) := by
  sorry

/-! ### Example A.39 -/

/-- Example A.39 `M:B:ex:lattice` (TeX L11608-11612), conclusion (perturbed lattice, linearisation).

Data: `N = n^d`, `Y_N = {z + κ_N⁻¹ a(z) : z ∈ Λ_N}` (`perturbedLattice n κ a`), `a` smooth,
`μ° = 1` (`S.μ0 = volume`), `β_N = ∞` (`S.invβ N = 0`), `η° = -div a` deterministic
(`ηF N ω = NegSobolev.ofFun γ (-div a)`), `1 ≪ κ_N ≪ min(N^{1/d}, N^{1-s/d})`.
Conclusion: `σ_N Ξ_N^t → V_∞^{t,0}(-div a)` in `H^{-γ}` (`γ = gammaIdx d`) with rate
`C(κ⁻¹ + κ N^{-2/d} + κ N^{s/d-1})`, the rate being uniform in `t ∈ [0,T]` (`K'`, `n₀` independent
of `t`), and `ConvergesInLaw` for each `t` (to the Dirac mass of the limit field).

**Faithfulness decisions** (plan section 1, all to be logged in ISSUES):
* indexing by `n`: the global packages `TorusStanding`, `InitialFluctuation`,
  `InitialFluctuationField` quantify over ALL `N ≥ 1`, but lattices exist only for `N = n^d`.  They are
  kept as hypotheses (they carry the off-lattice `N`); the lattice is imposed only at `N = n^d`
  (`n ≥ 2`) and the conclusion is only at `N = n^d`, eventually (`∃ n₀`), because `κ_N ≥ κ₀(a)` and
  `N ≥ C` (the A.9 threshold) are only eventual.
* `μ_{β=∞}` is `N`-independent (datum 1, `invβ = 0`): hypothesis `S.ρ N t = S.ρ M t`; then the
  coefficients are exactly the limit ones.  NOT claimed: `ρ = 1`.
* The lattice hypothesis and the domination hypothesis are imposed only for `n ≥ max 2 n₁` (`n₁` arbitrary),
  because the TeX needs them only eventually (for small `n` the perturbed lattice may have collisions, which
  `TorusStanding.flow` excludes); `n₀` may depend on `n₁`.
* `K'`, `n₀` depend on `a`, `S`, `R` and the hypotheses but not on `t`.  The A.9 constant `C` is not
  exported; only `ΛT` is.

**INTERIM hypothesis** (`hdom`, the domination): it assumes what the TeX derives from
`perturbedLattice_field` (InitialData.lean:4154) and `perturbedLattice_energy` (InitialData.lean:6096)
(`εf (n^d) ≤ K(κ⁻¹ + κ N^{-2/d})`, `𝔈 (n^d) ≤ K(κ⁻² + N^{s/d-1})`).  The final A.39 will replace it using
lemmas D1-D3 (lattice => `InitialFluctuation`, `InitialFluctuationField`, `EnergySmallness` at
`N = n^d`).

**Tacit TeX hypotheses for the final form** (not yet present here): `Torus.SymNonpos S.M` and
`HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ'` for `N ≥ 1`, `t ∈ [0,T]` (zero
temperature reduction, Prop 3.36 (C1); cf. `deterministic_example`, TorusTheorems.lean:562), and
`2 ≤ d` (the energy lemma `perturbedLattice_energy` needed it before its widening to `1 ≤ d` on 2026-10-20).  Here only
`1 ≤ d` (from `MainData.hd`) is used. -/
theorem perturbedLattice_linearization (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (a : Torus d → Euc d), Torus.IsSmooth a →
    ∃ ΛT : ℝ, 0 < ΛT ∧
    ∀ (S : MainData d), S.s = s → S.T = T → S.μ0 = volume → (∀ N : ℕ, S.invβ N = 0) →
    (∀ (N M : ℕ) (t : ℝ), S.ρ N t = S.ρ M t) →
    ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ) (m₀ : ℕ) (ε εf : ℕ → ℝ)
      (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
      (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) (n₁ : ℕ),
    TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
    InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
    (∀ (N : ℕ) (ω : (R N).Ω),
      ηF N ω = NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)) →
    InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
    (∀ n : ℕ, max 2 n₁ ≤ n → ∀ᵐ ω ∂(R (n ^ d)).P,
      (R (n ^ d)).X₀ ω = perturbedLattice n (S.κ (n ^ d)) a) →
    Tendsto (fun n : ℕ => S.κ (n ^ d)) atTop atTop →
    Tendsto (fun n : ℕ => S.κ (n ^ d) / (n : ℝ)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) atTop (𝓝 0) →
    (∃ K : ℝ, ∀ n : ℕ, max 2 n₁ ≤ n →
      εf (n ^ d) ≤ K * ((S.κ (n ^ d))⁻¹ +
        S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ∧
      𝔈 (n ^ d) ≤ K * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1))) →
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
