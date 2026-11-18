import HRS.Main.Lattice39Spec

/-!
# Example A.39: proofs of the D4 lemmas (relocation pattern `X_proof`)

Packet `lat39`.  The statements are copied verbatim from `HRS/Main/Lattice39Spec.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

theorem lattice39_noiseCovariance_zero_proof (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ)
    (φ ψ : Torus d → ℝ) : noiseCovariance D ρ 0 t φ ψ = 0 := by
  simp [noiseCovariance]

example := (@lattice39_noiseCovariance_zero_proof : type_of% @lattice39_noiseCovariance_zero)

theorem lat39_eval_zero (γ : ℝ) (φ : Torus d → ℝ) :
    NegSobolev.eval (0 : NegSobolev d γ) φ = 0 := by
  have h0 : ∀ k, NegSobolev.fourierCoeff (0 : NegSobolev d γ) k = 0 := fun k => by
    simp only [NegSobolev.fourierCoeff]
    have : NegSobolev.coord (0 : NegSobolev d γ) k = 0 := rfl
    rw [this, mul_zero]
  simp [NegSobolev.eval, h0]

theorem lattice39_dirac_isLinearFieldNoise_proof (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t γ : ℝ) :
    IsLinearFieldNoise D ρ 0 t γ (Measure.dirac (0 : NegSobolev d γ)) := by
  refine ⟨inferInstance, ⟨inferInstance, fun L => ?_⟩, fun φ ψ _ _ => ?_⟩
  · simp
  · rw [integral_dirac, lat39_eval_zero]
    simp [lattice39_noiseCovariance_zero_proof]

example := (@lattice39_dirac_isLinearFieldNoise_proof : type_of% @lattice39_dirac_isLinearFieldNoise)

theorem lattice39_linearFieldLaw_dirac_proof {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A t γ : ℝ)
    (F : NegSobolev d γ) (η : Ω → NegSobolev d γ) (hη : ∀ ω, η ω = F) :
    linearFieldLaw P D ρ A t γ η (Measure.dirac (0 : NegSobolev d γ)) =
      Measure.dirac (A • transportField D ρ t γ F) := by
  have := InitialDataAux.negSobolev_secondCountable d γ
  unfold linearFieldLaw
  have h1 : law P (fun ω => A • transportField D ρ t γ (η ω)) =
      Measure.dirac (A • transportField D ρ t γ F) := by
    have : (fun ω => A • transportField D ρ t γ (η ω)) =
        fun _ => A • transportField D ρ t γ F := funext fun ω => by rw [hη]
    unfold law
    rw [this, Measure.map_const, measure_univ, one_smul]
  rw [h1, Measure.dirac_conv_dirac, add_zero]

example := (@lattice39_linearFieldLaw_dirac_proof : type_of% @lattice39_linearFieldLaw_dirac)

theorem lattice39_scales_of_invβ_zero_proof (S : MainData d) (N : ℕ) (h : S.invβ N = 0) :
    S.sigma N = S.κ N ∧ S.AN N = 1 ∧ S.qN N = 0 := by
  simp [MainData.sigma, MainData.AN, MainData.qN, sigmaScale, Ascale, qScale, h]

example := (@lattice39_scales_of_invβ_zero_proof : type_of% @lattice39_scales_of_invβ_zero)

theorem lattice39_fieldRate_le_proof (s κ K εf 𝔈 : ℝ) (N : ℕ) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hN : 1 ≤ N)
    (hεf : εf ≤ K * (κ⁻¹ + κ * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ))))
    (h𝔈 : 𝔈 ≤ K * ((κ⁻¹) ^ 2 + (N : ℝ) ^ (s / (d : ℝ) - 1))) :
    fieldRate d εf 0 κ 𝔈 N ≤
      2 * K * (κ⁻¹ + κ * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) + κ * (N : ℝ) ^ (s / (d : ℝ) - 1)) := by
  have h1 : κ * 𝔈 ≤ κ * (K * ((κ⁻¹) ^ 2 + (N : ℝ) ^ (s / (d : ℝ) - 1))) :=
    mul_le_mul_of_nonneg_left h𝔈 hκ.le
  have h2 : κ * (K * ((κ⁻¹) ^ 2 + (N : ℝ) ^ (s / (d : ℝ) - 1))) =
      K * κ⁻¹ + K * (κ * (N : ℝ) ^ (s / (d : ℝ) - 1)) := by
    field_simp
  have p1 : 0 ≤ K * (κ * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) := by positivity
  have p2 : 0 ≤ K * (κ * (N : ℝ) ^ (s / (d : ℝ) - 1)) := by positivity
  unfold fieldRate
  simp only [zero_mul, add_zero]
  nlinarith [h1, h2, hεf, p1, p2]

example := (@lattice39_fieldRate_le_proof : type_of% @lattice39_fieldRate_le)

end Main

end HRS
