import HRS.Main.TorusTheorems
import HRS.Main.A9Aux22
import HRS.Main.A9Aux33

/-!
# Packet A9: relocated proofs of Proposition A.9 (`main_torus_field`, `main_torus_field_limit`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

theorem main_torus_field_proof (s : ℝ) :
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
              ENNReal.ofReal B :=
  HRS.Main.A9.a9_field_main s

example := (@main_torus_field_proof : type_of% @HRS.Main.main_torus_field)

theorem main_torus_field_limit_proof (s : ℝ) :
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
        (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim)) :=
  HRS.Main.A9.a9_field_limit s

example := (@main_torus_field_limit_proof : type_of% @HRS.Main.main_torus_field_limit)

end Main

end HRS
