import HRS.MS.ZeroTempAux15

/-!
# SA11, packet D3: the constants of the commutator bound for the selected decaying densities

`sa11_comm_exists`: for `fd` a decaying selected density with `fd.wParams = some (m,p)` there are `C₀min, K_c, c₂` (depending only on
`d, s, fd, MB, Λ, Kad`) such that the pathwise bound `|Comm_N(Mᵀ∇U^{r,t}φ)| ≤ K_c ‖Jφ‖ (F + oNΛ + c₂ e_N)` holds for every
admissible `S` with `C₀ ≥ C₀min`.  The impossible cases (`d = 0`, `s ∉ [0,d)`, wrong side of `d-2`, `Λ ≤ 0`) are discharged by
contradiction with the hypotheses on `S`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

theorem sa11_Λ_pos {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {rs mV : ℕ}
    {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 rs mV C₀ 𝔈) : 0 < Λ := by
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) S.T := ⟨le_rfl, S.hT.le⟩
  have hprob := sa11_density_prob hS (le_refl 1) hT0
  obtain ⟨hcb, hfin, hle⟩ := (hS.mean_field.regular 1 le_rfl).1 0 hT0
  have hw0 : 0 ≤ (weightedSupE rs ((d : ℝ) + 3) (S.ρ 1 0)).toReal := ENNReal.toReal_nonneg
  have hex : ∃ x, 0 < S.ρ 1 0 x := by
    by_contra hne
    push Not at hne
    have h0 : ∀ x, S.ρ 1 0 x = 0 := fun x => le_antisymm (hne x) (hprob.nonneg x)
    have := hprob.integral_one
    simp [h0] at this
  obtain ⟨x, hx⟩ := hex
  have h1 : |S.ρ 1 0 x| ≤ HRS.cbNorm rs (S.ρ 1 0) := by
    have := sa11_iter_le_cbNorm hcb (Nat.zero_le rs) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  rw [abs_of_pos hx] at h1
  linarith

theorem sa11_comm_exists (s : ℝ) (fd : FieldDensityRd d s) {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]
    (hfd : fd.wParams = some (m, p)) (ν₀ MB Λ Kad : ℝ) :
    ∃ C₀min Kc c₂ : ℝ, 0 ≤ Kc ∧ 0 ≤ c₂ ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (ΛV G₀ m20 : ℝ) (𝔈 : ℕ → ℝ),
        S.s = s → fd.Holds S ν₀ →
        RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 3) (fd.Gamma + 3) C₀ 𝔈 →
        ∀ N : ℕ, 2 ≤ N → AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad →
        ∀ X : EucConfig d N, Function.Injective X → ∀ r₀ t : ℝ, 0 ≤ r₀ → r₀ ≤ t → t ≤ S.T → ∀ φ : sa11_V d,
        |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t φ.1) x)) X
            (HRS.Whole.withDensityReal (S.ρ N r₀))| ≤
          Kc * ‖sa11_J (m := m) (p := p) φ‖ *
            (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d S.s C₀ Λ N +
              c₂ * fd.eN N) := by
  by_cases hΛ : 0 < Λ
  swap
  · exact ⟨0, 0, 0, le_rfl, le_rfl, fun C₀ _ S R ΛV G₀ m20 𝔈 hs hH hS => absurd (sa11_Λ_pos hS) hΛ⟩
  by_cases hdd : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, 0, 0, le_rfl, le_rfl, fun C₀ _ S R ΛV G₀ m20 𝔈 hs hH hS => ?_⟩
    exfalso; apply hdd
    exact ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩
  obtain ⟨hd, hs0, hsd⟩ := hdd
  cases fd with
  | nd Rg => simp [FieldDensityRd.wParams] at hfd
  | decSub c =>
    simp only [FieldDensityRd.wParams, Option.some.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl⟩ := hfd
    by_cases hsub : s < (d : ℝ) - 2
    swap
    · refine ⟨0, 0, 0, le_rfl, le_rfl, fun C₀ _ S R ΛV G₀ m20 𝔈 hs hH hS => ?_⟩
      exfalso; apply hsub
      have := hH 1 le_rfl
      simp only [FieldDensityRd.HoldsAt] at this
      rwa [hs] at this
    have hmm : mStar d ≤ c.sobolevIndex := by unfold DecayingDensity.sobolevIndex; omega
    obtain ⟨C₀min, Kc, c₂, hKc, hc₂, H⟩ := sa11_commBound_sub hd hs0 hsub c hΛ MB Kad hmm rfl
    exact ⟨C₀min, Kc, c₂, hKc, hc₂, fun C₀ hC₀ S R ΛV G₀ m20 𝔈 hs hH hS N hN hA X hX r₀ t hr hrt htT φ =>
      H C₀ hC₀ S R ΛV G₀ m20 _ _ 𝔈 hs hS N hN hA X hX r₀ t hr hrt htT φ⟩
  | decSuperIso m' p' =>
    simp only [FieldDensityRd.wParams, Option.some.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl⟩ := hfd
    by_cases hsc : (d : ℝ) - 2 < s
    swap
    · refine ⟨0, 0, 0, le_rfl, le_rfl, fun C₀ _ S R ΛV G₀ m20 𝔈 hs hH hS => ?_⟩
      exfalso; apply hsc
      have := (hH 1 le_rfl).1
      rwa [hs] at this
    obtain ⟨C₀min, Kc, hKc, H⟩ := sa11_commBound_super (m := m') (p := p') hd hs0 hsd hsc.le hΛ MB Kad
    refine ⟨C₀min, Kc, 0, hKc, le_rfl, fun C₀ hC₀ S R ΛV G₀ m20 𝔈 hs hH hS N hN hA X hX r₀ t hr hrt htT φ => ?_⟩
    have := H C₀ hC₀ S R ΛV G₀ m20 _ _ 𝔈 hs hS N hN hA X hX r₀ t hr hrt htT φ
    simpa [FieldDensityRd.eN] using this
  | decSuperHilb m' =>
    simp only [FieldDensityRd.wParams, Option.some.injEq, Prod.mk.injEq] at hfd
    obtain ⟨rfl, rfl⟩ := hfd
    by_cases hsc : (d : ℝ) - 2 < s
    swap
    · refine ⟨0, 0, 0, le_rfl, le_rfl, fun C₀ _ S R ΛV G₀ m20 𝔈 hs hH hS => ?_⟩
      exfalso; apply hsc
      have := (hH 1 le_rfl).1
      rwa [hs] at this
    obtain ⟨C₀min, Kc, hKc, H⟩ := sa11_commBound_super (m := m') (p := 2) hd hs0 hsd hsc.le hΛ MB Kad
    refine ⟨C₀min, Kc, 0, hKc, le_rfl, fun C₀ hC₀ S R ΛV G₀ m20 𝔈 hs hH hS N hN hA X hX r₀ t hr hrt htT φ => ?_⟩
    have := H C₀ hC₀ S R ΛV G₀ m20 _ _ 𝔈 hs hS N hN hA X hX r₀ t hr hrt htT φ
    simpa [FieldDensityRd.eN] using this

end HRS.MS.ZeroTemp
