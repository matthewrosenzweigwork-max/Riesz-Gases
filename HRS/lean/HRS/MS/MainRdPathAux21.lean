import HRS.MS.MainRdPathAux20

/-!
# S.A.9, glue: the existence of path representatives and the tightness of their laws from the hypotheses of `main_rd_path`

`Sa9Conc S R Γ`: (a) the existence of measurable path representatives and (b) the tightness of the laws of every
family of representatives (`N ≥ 2`).  `sa9_core_ge1` proves it for `Λ ≥ 1`; `sa9_core` removes this restriction by the
`Λ`-normalisation of S.A.6.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdRem
  HRS.MS.MainRdField

variable {d : ℕ}

/-- The conclusions of P1-P4. -/
def Sa9Conc (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (Γ : ℕ) : Prop :=
  (∀ N : ℕ, 1 ≤ N → ∃ Ξ : (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T, Measurable Ξ ∧
    IsFluctPathRepr S R N (Γ + 2) Ξ) ∧
  ∀ Ξ : ∀ N, (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T,
    (∀ N : ℕ, 1 ≤ N → IsFluctPathRepr S R N (Γ + 2) (Ξ N)) →
      IsTightMeasureSet {μ | ∃ N : ℕ, 2 ≤ N ∧ μ = (R N).P.map (Ξ N)}

theorem sa9_small_of_total {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ} {s : ℝ}
    (fd : FieldDensityRd d s) {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) {m₂ Cin : ℝ} {εf : ℕ → ℝ}
    (hm₂0 : 0 ≤ m₂) {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}
    (hTIF : TransportedInitialFieldRd S R Γ Cin εf Iemp I)
    (hsm : Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0)) :
    Tendsto (fun N => S.sigma N * (𝔈 N + fd.eN N)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hsm
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact mul_nonneg (mrr_sigma_nonneg S N) (add_nonneg (hS.energy.pos N hN).le (mrr_eN_nonneg fd N))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have h1 := hTIF.εf_nonneg N hN
    have h2 := mul_nonneg (sa6_qN_nonneg S N) (sa6_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN).le hm₂0)
    linarith

theorem sa9_core_ge1 (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst Cw : ℝ) (hΛ : 1 ≤ Λ) :
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
        (∀ N : ℕ, 1 ≤ N → ∃ U, IsWeightedExtension (S.coeff N) (m₀ + 1) (fd.Gamma + 2) S.T Cw U) →
      FieldAdjointInputRd fd S Kad →
        AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
        AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
        Sa9Conc S R fd.Gamma := by
  classical
  obtain ⟨C₀m, hin⟩ := sa6_inputs s fd ν₀ MB Λ ΛV G₀ νbar T m20 χ hχ Kad hΛ
  refine ⟨C₀m, fun C₀ hC₀ S hs hT hinv hH R 𝔈 hS m₂ hm₂0 hm₂ m₀ ε hinit εf Iemp I hTIF hdist L hΔ hW hFA
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

theorem sa9_core (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst Cw : ℝ) :
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
  obtain ⟨C₀minc, hcore⟩ := sa9_core_ge1 s fd ν₀ MB (max Λ 1) ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst Cw
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
