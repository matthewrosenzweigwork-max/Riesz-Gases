import HRS.MS.MainRdFieldAux14

/-!
# S.A.6, packet P8b: `main_rd_field` for arbitrary `Λ`

`sa6_main`: the frozen statement `HRS.Whole.AppendixA.main_rd_field` (with the repaired `σ_N e_N → 0` hypothesis) .
the occupation of collisions is derived from the flow (`sa6_inj_N`); obtained from `sa6_main_core` (`Λ ≥ 1`) by the
`Λ`-normalisation `sa6_standing_normalise`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa6_main (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        Filter.Tendsto (fun N : ℕ => S.sigma N * fd.eN N) Filter.atTop (nhds 0) →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
          InitialFieldDist S R fd.Gamma εf Iemp I →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ N : ℕ, C ≤ (N : ℝ) →
            ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
              IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
              (∃ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ ∧
                IsFluctFieldRepr S R N fd.Gamma t Ξ) ∧
              ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
                IsFluctFieldRepr S R N fd.Gamma t Ξ →
                smoothDist 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                  C * Real.exp (ΛT * t) *
                    fieldRateRd (εf N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) (fd.eN N)) ∧
          ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
            IsFluctFieldRepr S R N fd.Gamma t Ξ → ∫⁻ ζ, ‖Ξ ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal B := by
  classical
  by_cases hex : ∃ S0 : WholeMainData d, S0.s = s ∧ fd.Holds S0 ν₀
  swap
  · exact ⟨0, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun S hs _ _ hH => absurd ⟨S, hs, hH⟩ hex⟩⟩
  by_cases hΛ0 : 0 < Λ
  swap
  · exact ⟨0, fun C₀ _ => ⟨1, 1, one_pos, one_pos, fun S _ _ _ _ R 𝔈 hS =>
      absurd (sa6_pos_of_standing hS) hΛ0⟩⟩
  obtain ⟨S0, hS0s, hS0⟩ := hex
  have hd1 : 1 ≤ d := S0.hd
  have hs0 : 0 ≤ s := hS0s ▸ S0.hs0
  have hsd : s < d := hS0s ▸ S0.hsd
  have hΛ' : 1 ≤ max Λ 1 := le_max_right _ _
  have hΛ'0 : 0 < max Λ 1 := lt_of_lt_of_le one_pos hΛ'
  obtain ⟨C₀minc, hcore⟩ := sa6_main_core s fd ν₀ MB (max Λ 1) ΛV G₀ νbar T Cin m20 χ hχ Kad hΛ'
  obtain ⟨C₀c, C₁, hC₀c, hpairE⟩ := HRS.MH.CoercTest.p_assembly d hd1 s hs0 hsd
  set base : ℝ := max C₀minc C₀c with hbase
  set X : ℝ := (if s = 0 then Real.log (max Λ 1 / Λ) / (2 * d) else 0) with hX
  refine ⟨(base * (max Λ 1) ^ (s / d) + X) / Λ ^ (s / d), fun C₀ hC₀ => ?_⟩
  have hΛp : 0 < Λ ^ (s / d) := Real.rpow_pos_of_pos hΛ0 _
  have hΛ'p : 0 < (max Λ 1) ^ (s / d) := Real.rpow_pos_of_pos hΛ'0 _
  have hC₀' : base ≤ sa6_C0norm d s C₀ Λ (max Λ 1) := by
    unfold sa6_C0norm
    rw [← hX, le_div_iff₀ hΛ'p]
    rw [div_le_iff₀ hΛp] at hC₀
    linarith
  obtain ⟨C, ΛT, hC, hΛT, H⟩ := hcore _ (le_trans (le_max_left _ _) hC₀')
  refine ⟨C, ΛT, hC, hΛT, ?_⟩
  intro S hs hT hinv hH R 𝔈 hS hFA hσe m₂ hm₂ hm2 m₀ ε hinit0 εf Iemp I hinit hdist
  have hpairC := hpairE _ (le_trans (le_max_right _ _) hC₀')
  have hcomp : CompletionNonnegRd d S.s (sa6_C0norm d s C₀ Λ (max Λ 1)) := hs ▸ hpairC.1
  have hS' := sa6_standing_normalise hS (by rw [hs]) hcomp
  exact H S hs hT hinv hH R 𝔈 hS' hFA hσe m₂ hm₂ hm2 m₀ ε hinit0 εf Iemp I hinit hdist

end HRS.MS.MainRdField
