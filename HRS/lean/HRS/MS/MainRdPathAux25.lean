import HRS.MS.MainRdPathAux24

/-!
# S.A.9, glue (K-independent version): `C₀min` does not depend on the constant `K` of `WeightedPathInput`

Same as `sa9_core` of `MainRdPathAux21`, with the free constant `Cw` of the weighted extension quantified after `C₀`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdRem
  HRS.MS.MainRdField

variable {d : ℕ}

theorem sa9_coreK_ge1 (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d,
        Tendsto (fun N => coeffDiscrepancyRd S L fd.Gamma N) atTop (𝓝 0) →
      ∀ Cw : ℝ,
        (∀ N : ℕ, 1 ≤ N → ∃ U, IsWeightedExtension (S.coeff N) (m₀ + 1) (fd.Gamma + 2) S.T Cw U) →
      FieldAdjointInputRd fd S Kad →
        AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
        AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
        Sa9Conc S R fd.Gamma := by
  classical
  obtain ⟨C₀m, hin⟩ := sa6_inputs s fd ν₀ MB Λ ΛV G₀ νbar T m20 χ hχ Kad hΛ
  refine ⟨C₀m, fun C₀ hC₀ S hs hT hinv hH R 𝔈 hS m₂ hm₂0 hm₂ m₀ ε hinit εf Iemp I hTIF hdist L hΔ Cw hW hFA
    hAdjP hAdjL hStab hsm => ?_⟩
  obtain ⟨K', Cp, Ck, hCk0, hall⟩ := hin C₀ hC₀
  have hS3 : RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 :=
    sa9_standing_mono hS (by omega) (by omega)
  obtain ⟨hsel, -, -⟩ := hall S hs hT hinv hH R 𝔈 hS3 hFA
  obtain ⟨C₁, hker, ⟨B⟩⟩ := sa9_bundle_exists s fd ν₀ MB Λ ΛV G₀ νbar T Kad Kadj Cw Cin m₀ hinit.m₀_pos
    hinit.m₀_le χ hχ S hs hT hinv hH R C₀ m20 𝔈 hS ε hinit εf Iemp I hTIF hdist hFA hAdjP hW
  have hsmall := sa9_small_of_total fd hS hm₂0 hTIF hsm
  exact ⟨fun N hN => sa9_pathRepr_exists B hN, fun Ξ hΞ =>
    sa9_path_tight B hS hΛ hm₂0 hm₂ hker (fun N => mrr_eN_nonneg fd N) hsel hsmall hinit.m₀_pos hinit hTIF
      hAdjP L hAdjL hStab hΔ Ξ hΞ⟩

theorem sa9_coreK (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d,
        Tendsto (fun N => coeffDiscrepancyRd S L fd.Gamma N) atTop (𝓝 0) →
      ∀ Cw : ℝ,
        (∀ N : ℕ, 1 ≤ N → ∃ U, IsWeightedExtension (S.coeff N) (m₀ + 1) (fd.Gamma + 2) S.T Cw U) →
      FieldAdjointInputRd fd S Kad →
        AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
        AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
        Sa9Conc S R fd.Gamma := by
  classical
  by_cases hex : ∃ S0 : WholeMainData d, S0.s = s ∧ fd.Holds S0 ν₀
  swap
  · exact ⟨0, fun C₀ _ S hs _ _ hH => absurd ⟨S, hs, hH⟩ hex⟩
  by_cases hΛ0 : 0 < Λ
  swap
  · exact ⟨0, fun C₀ _ S _ _ _ _ R 𝔈 hS => absurd (sa6_pos_of_standing hS) hΛ0⟩
  obtain ⟨S0, hS0s, hS0⟩ := hex
  have hd1 : 1 ≤ d := S0.hd
  have hs0 : 0 ≤ s := hS0s ▸ S0.hs0
  have hsd : s < d := hS0s ▸ S0.hsd
  have hΛ'0 : 0 < max Λ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨C₀minc, hcore⟩ := sa9_coreK_ge1 s fd ν₀ MB (max Λ 1) ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
    (le_max_right _ _)
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
  intro S hs hT hinv hH R 𝔈 hS
  have hpairC := hpairE _ (le_trans (le_max_right _ _) hC₀')
  have hcomp : CompletionNonnegRd d S.s (sa6_C0norm d s C₀ Λ (max Λ 1)) := hs ▸ hpairC.1
  have hS' := sa6_standing_normalise hS (by rw [hs]) hcomp
  exact hcore _ (le_trans (le_max_left _ _) hC₀') S hs hT hinv hH R 𝔈 hS'

end HRS.MS.MainRdPath
