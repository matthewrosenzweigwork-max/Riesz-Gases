import HRS.MS.MainRdFieldAux19

/-!
# S.A.7: `rd_field_wasserstein_one` / `_two` for arbitrary `Λ`

`Λ`-normalisation of `Aux19` as in `sa6_main` (`Aux15`): `Λ' = max Λ 1`, `C₀min := (base·Λ'^{s/d} + X)/Λ^{s/d}`; A.7
(`EnergySmallness2Rd`) is unchanged because it depends on `(C₀, Λ)` only through `correctedEnergyRd`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- `A.7` (`EnergySmallness2Rd`) depends on `(C₀, Λ)` only through `correctedEnergyRd`, which is unchanged by the `Λ`-normalisation. -/
theorem sa6_es2_normalise {S : WholeMainData d} {R : ∀ N, RealizationRd d N}
    {MB Λ ΛV G₀ m20 : ℝ} {r mV : ℕ} {C₀ : ℝ} {𝔈 : ℕ → ℝ}
    (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {C₀' : ℝ}
    (hC : C₀' = sa6_C0norm d S.s C₀ Λ (max Λ 1)) {χ : Euc d → ℝ} {m₀ : ℕ}
    {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ} (h : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2) :
    EnergySmallness2Rd S R C₀' (max Λ 1) χ m₀ Ψ 𝔈' ε2 := by
  have hΛ := sa6_pos_of_standing hS
  have hΛ' : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcorr : ∀ (N : ℕ) (X : EucConfig d N) (t : ℝ), 1 ≤ N →
      correctedEnergyRd S C₀' (max Λ 1) N X t = correctedEnergyRd S C₀ Λ N X t := by
    intro N X t hN
    unfold correctedEnergyRd
    rw [hC, sa6_oN_normalise S.hd hΛ hΛ' C₀ (by omega)]
  refine ⟨h.𝔈'_nonneg, h.ε2_nonneg, fun N hN t ht => ?_, h.small, h.I1_L2⟩
  simp only [hcorr N _ t hN]
  exact h.bound N hN t ht

theorem sa6_w1 (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
        ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        ∀ εf1 : ℕ → ℝ, (∀ N : ℕ, 1 ≤ N → 0 ≤ εf1 N) →
          (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
            wassersteinE 1 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ ENNReal.ofReal (εf1 N)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
            IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
            ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
              IsFluctFieldRepr S R N fd.Gamma t Ξ →
              wassersteinE 1 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                ENNReal.ofReal (C * Real.exp (ΛT * t) *
                  (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈 N + fd.eN N))) := by
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
  obtain ⟨C₀minc, hcore⟩ := sa6_w1_core s fd ν₀ MB (max Λ 1) ΛV G₀ νbar T Cin m20 χ hχ Kad hΛ'
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
  intro S hs hT hinv hH R 𝔈 hS hFA m₂ hm₂ hm2 m₀ ε hinit0 εf Iemp I hinit εf1 hεf1 hW
  have hpairC := hpairE _ (le_trans (le_max_right _ _) hC₀')
  have hcomp : CompletionNonnegRd d S.s (sa6_C0norm d s C₀ Λ (max Λ 1)) := hs ▸ hpairC.1
  have hS' := sa6_standing_normalise hS (by rw [hs]) hcomp
  exact H S hs hT hinv hH R 𝔈 hS' hFA m₂ hm₂ hm2 m₀ ε hinit0 εf Iemp I hinit εf1 hεf1 hW

theorem sa6_w2 (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad : ℝ) :
        ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        FieldAdjointInputRd fd S Kad →
        ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
        ∀ (𝔈' ε2 : ℕ → ℝ), EnergySmallness2Rd S R C₀ Λ χ m₀ (fun _ => ∅) 𝔈' ε2 →
        ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
          TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        ∀ εf1 : ℕ → ℝ, (∀ N : ℕ, 1 ≤ N → 0 ≤ εf1 N) →
          (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
            wassersteinE 2 (law (R N).P (Iemp N t)) (law (R N).P (I N t)) ≤ ENNReal.ofReal (εf1 N)) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
          ∀ νG : Measure (HNeg d (fd.Gamma : ℝ)),
            IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t fd.Gamma νG →
            ∀ Ξ : (R N).Ω → HNeg d (fd.Gamma : ℝ), Measurable Ξ →
              IsFluctFieldRepr S R N fd.Gamma t Ξ →
              wassersteinE 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
                ENNReal.ofReal (C * Real.exp (ΛT * t) *
                  (εf1 N + Real.sqrt (S.qN N * wN d N (𝔈 N) m₂) + S.sigma N * (𝔈' N + fd.eN N))) := by
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
  obtain ⟨C₀minc, hcore⟩ := sa6_w2_core s fd ν₀ MB (max Λ 1) ΛV G₀ νbar T Cin m20 χ hχ Kad hΛ'
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
  intro S hs hT hinv hH R 𝔈 hS hFA m₂ hm₂ hm2 m₀ ε hinit0 𝔈' ε2 h2 εf Iemp I hinit εf1 hεf1 hW
  have hpairC := hpairE _ (le_trans (le_max_right _ _) hC₀')
  have hcomp : CompletionNonnegRd d S.s (sa6_C0norm d s C₀ Λ (max Λ 1)) := hs ▸ hpairC.1
  have hS' := sa6_standing_normalise hS (by rw [hs]) hcomp
  have h2' : EnergySmallness2Rd S R (sa6_C0norm d s C₀ Λ (max Λ 1)) (max Λ 1) χ m₀ (fun _ => ∅) 𝔈' ε2 := sa6_es2_normalise (C₀' := sa6_C0norm d s C₀ Λ (max Λ 1)) hS (by rw [hs]) h2 
  exact H S hs hT hinv hH R 𝔈 hS' hFA m₂ hm₂ hm2 m₀ ε hinit0 𝔈' ε2 h2' εf Iemp I hinit εf1 hεf1 hW

end HRS.MS.MainRdField
