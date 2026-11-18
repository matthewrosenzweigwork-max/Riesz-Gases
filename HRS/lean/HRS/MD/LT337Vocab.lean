import HRS.Energy.Coercivity

/-!
# Vocabulary of the Prop 3.37 spec (chunk D), sorry-free copy

Verbatim copies of the definitions of `HRS/MD/LT337Spec.lean` (namespace `HRS.MD.LT337`), placed in the namespace
`HRS.MD.LT337Vocab`, so that packet files can state their theorems without importing the sorried spec file.
`StoppingFamily` is a structure, hence NOT definitionally the spec's structure: the tie files convert field by field.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS

namespace HRS.MD.LT337Vocab

variable {d N : ℕ}

/-- The Coulomb constant `c_d`: `ĝ(k) = c_d (2π|k|)^{-2}` for `s = d - 2` (`rieszCoeff`), so that
`-Δ g = c_d (δ_0 - 1)` on `𝕋^d` (M L3137-3139, `B:eq:coulomb-diffusion-correction`). -/
def cd (d : ℕ) : ℝ := rieszConst d ((d : ℝ) - 2)

/-- The limit of the diffusion correction `𝒟_N^t` (M L3140-3146, torus case):
`c_d (-N⁻¹ + 2⟨μ, μ_N⟩ - ∫ μ²)`. -/
def diffLimit (d : ℕ) {N : ℕ} (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  cd d * (-(1 / (N : ℝ)) + 2 * ((1 / (N : ℝ)) * ∑ i, ρ (X i)) - ∫ x, ρ x ^ 2)

/-- The microscopic term `N⁻¹ ∑_i a_iᵀ M a_i` of M L3133 (`a_i` = `selfForce` of `∇g`); equals
`N⁻¹ ∑ a_iᵀ 𝖲 a_i` (`𝖲` the symmetric part of `M`). -/
def microG (D : DynData d) (ρ : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, inner ℝ (selfForce (periodicRieszGrad d D.s) ρ X i)
    (Torus.matVec D.M (selfForce (periodicRieszGrad d D.s) ρ X i))

/-- The drift of `E[F_N^t]` in `B:eq:coulomb-energy-identity` (M L3133), with the diffusion term already evaluated:
`½ Comm_N(u^t; X, μ^t) + N⁻¹ ∑ a_iᵀ M a_i + β⁻¹ 𝒟_N^t`, where `u^t = M ∇g*μ^t - ∇V = meanFieldDrift`. -/
def ltDrift (D : DynData d) (ρ : ℝ → Torus d → ℝ) (r : ℝ) (Z : Config d N) : ℝ :=
  (1 / 2) * commQuantity d D.s (meanFieldDrift D (ρ r)) Z (withDensityReal (ρ r)) + microG D (ρ r) Z +
    D.invβ * diffLimit d (ρ r) Z

/-- The stopped time `t ∧ τ` as a real number (`τ = ⊤` gives `t`). -/
def stopTime (t : ℝ) (τ : WithTop ℝ) : ℝ := min t (τ.untopD t)

/-- The deterministic part of `LowTempHyp` (everything not involving the probability space). -/
def LTDet (D : DynData d) (T Λ ΛV Mb : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop :=
  D.s = (d : ℝ) - 2 ∧ Torus.SymNonpos D.M ∧ (∀ v : Euc d, ‖Torus.matVec D.M v‖ ≤ Mb * ‖v‖) ∧
    (Torus.IsCk 2 D.V ∧ Torus.cbNorm 2 D.V ≤ ΛV) ∧ IsMeanFieldSolution D T ρ ∧
    IsRegularMF 3 Λ T ρ ∧ 1 ≤ Λ

/-- A family `τ_ε` (`ε > 0`) of localising stopping times for the Itô calculus of the proof (M L3137):
`τ_ε` is the exit time of `{min pair distance > ε}` of the (everywhere continuous, adapted) lift of `X`;
for `0 < τ_ε` and `s ≤ τ_ε` the pair distances of `X_s` are `≥ ε`; and a.s. `τ_ε ≥ T` for all small `ε`
(the minimum pair distance on `[0,T]` is positive, `IsStrongSolution.no_collision`). -/
structure StoppingFamily {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (X : ℝ≥0 → Ω → Config d N) (T : ℝ) (τ : ℝ → Ω → WithTop ℝ) : Prop where
  stopping : ∀ ε : ℝ, IsStoppingTime ℱ (τ ε)
  zero_le : ∀ ε : ℝ, ∀ ω, 0 ≤ τ ε ω
  sep : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ s ∈ Set.Icc (0 : ℝ) T, ((s : ℝ) : WithTop ℝ) ≤ τ ε ω →
    0 < τ ε ω → ∀ i j, i ≠ j → ε ≤ ‖X (Real.toNNReal s) ω i - X (Real.toNNReal s) ω j‖
  exhaust : ∀ᵐ ω ∂P, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ((T : ℝ) : WithTop ℝ) ≤ τ ε ω

/-- The localised energy identity (M L3131-3137, the stopped form of `B:eq:coulomb-energy-identity`):
for every `ε > 0` and `t ∈ [0,T]`,
`E[(F_N + o_N)(X_{t∧τ_ε}, μ_{t∧τ_ε})] - E[(F_N + o_N)(X_0, μ_0)] = ∫_0^t E[1_{r < τ_ε} ltDrift(r)] dr`,
with the integrability needed to read the Bochner integrals. -/
def StoppedIdentity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d) (N : ℕ) (T Λ C₀ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (τ : ℝ → Ω → WithTop ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc (0 : ℝ) T,
    Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω)
      (stopTime t (τ ε ω))) P ∧
    Integrable (fun p : ℝ × Ω => if ((p.1 : ℝ) : WithTop ℝ) < τ ε p.2
        then ltDrift D ρ p.1 (X (Real.toNNReal p.1) p.2) else 0)
      ((volume.restrict (Set.Icc (0 : ℝ) t)).prod P) ∧
    ∫ ω, correctedEnergy D C₀ Λ ρ (X (Real.toNNReal (stopTime t (τ ε ω))) ω) (stopTime t (τ ε ω)) ∂P -
        ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, (if ((r : ℝ) : WithTop ℝ) < τ ε ω
        then ltDrift D ρ r (X (Real.toNNReal r) ω) else 0) ∂P


end HRS.MD.LT337Vocab
