import HRS.Main.A9Aux19

/-!
# Packet A9, part 20: the first moment of `Z = σ_N Ξ_N^t` in `E_γ`, and the pathwise bound for `N = 1`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

/-- the empty family of modes. -/
def a9k0 (d : ℕ) : Fin 0 → NonzeroLattice d := fun a => a.elim0

theorem a9tail_empty (Λ₁ t : ℝ) : a9tail d Λ₁ t (a9k0 d) = ∑' j, a9K d Λ₁ t j := by
  classical
  unfold a9tail
  refine tsum_congr fun j => ?_
  have : j ∉ Set.range (a9k0 d) := by
    rintro ⟨a, _⟩; exact a.elim0
  simp [this]

section Moment2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

theorem a9_Z_moment (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {Cin : ℝ} {εf : ℕ → ℝ} {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Kb : ℝ} (hKb : ∑' j, a9K d Λ₁ t j ≤ Kb) :
    ∫⁻ ω, ‖a9Z S R N t ω‖ₑ ∂(R N).P ≤
      ENNReal.ofReal (Ktr * (1 + Cin ^ 2) +
        (S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) + Real.sqrt (2 * S.T) * (d * Ca)) * Kb) := by
  have hP' := hP
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP'
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hT := S.hT.le
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hσ := a8p_sigma_nonneg S N
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  have hZm := a9_Z_meas hS hN1 ht hF
  have hXm : Measurable (a9I S R N t) := (a9_I_meas hS hN1 ht hF).mono (ℱ.le 0) le_rfl
  have hI := a9_I_moment hKtr0 hKtr hS hN1 ht hfield
  have hbQ0 : ∀ j, 0 ≤ a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) (a9k0 d) j :=
    fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈 (a9k0 d) j
  have hbQs : Summable (a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) (a9k0 d)) :=
    a9bQ_summable hCa hCq hcT0 hN1 h𝔈 (a9k0 d)
  have hZI : ∫⁻ ω, ENNReal.ofReal ‖a9Z S R N t ω - a9I S R N t ω‖ ∂(R N).P ≤
      ENNReal.ofReal (∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) (a9k0 d) j) := by
    refine a9_lintegral_norm_le (R N).P (fun ω => a9Z S R N t ω - a9I S R N t ω)
      (hZm.aemeasurable.sub hXm.aemeasurable) _ hbQ0 hbQs fun j => ?_
    have hj : j ∉ Set.range (a9k0 d) := by rintro ⟨a, _⟩; exact a.elim0
    have h := a9_ZI_moment hspec hCa hS hN hF hcom hCq hC hcT0 hcT ht j
    have hbQ : a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) (a9k0 d) j =
        Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (d * (Ca * a8pK Λ₁ t (a9phi d j))) ^ 2)) +
        S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d j)))) * (S.T * 𝔈 N) := by
      simp only [a9bQ, if_neg hj]
      rfl
    rw [hbQ]
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun ω => ?_
    rw [a9_coord_sub]
  have hbound : ∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) (a9k0 d) j ≤
      (S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) + Real.sqrt (2 * S.T) * (d * Ca)) * Kb := by
    rw [a9bQ_tsum hCq hcT0 hCa hN1 h𝔈 (a9k0 d), a9tail_empty]
    have hqe := a8p_q_eq S N
    obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN1
    have hcM : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) ≤ Real.sqrt (2 * S.T) := by
      refine Real.sqrt_le_sqrt ?_
      rw [← hqe]; nlinarith
    have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
    have hKtot0 : 0 ≤ ∑' j, a9K d Λ₁ t j := tsum_nonneg fun j => a9K_nonneg _ _ _
    have h1 : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) *
        ∑' j, a9K d Λ₁ t j ≤ Real.sqrt (2 * S.T) * (d * Ca) * Kb :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcM hCd) hKb hKtot0 (by positivity)
    have h0 : 0 ≤ S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hKb h0
    linarith
  calc ∫⁻ ω, ‖a9Z S R N t ω‖ₑ ∂(R N).P
      ≤ ∫⁻ ω, (ENNReal.ofReal ‖a9I S R N t ω‖ +
          ENNReal.ofReal ‖a9Z S R N t ω - a9I S R N t ω‖) ∂(R N).P := by
        refine lintegral_mono fun ω => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by
          have := norm_add_le (a9I S R N t ω) (a9Z S R N t ω - a9I S R N t ω)
          simpa using this)
    _ = ∫⁻ ω, ENNReal.ofReal ‖a9I S R N t ω‖ ∂(R N).P +
          ∫⁻ ω, ENNReal.ofReal ‖a9Z S R N t ω - a9I S R N t ω‖ ∂(R N).P :=
        lintegral_add_left hXm.norm.ennreal_ofReal _
    _ ≤ ENNReal.ofReal (Ktr * (1 + Cin ^ 2)) +
          ENNReal.ofReal ((S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) +
            Real.sqrt (2 * S.T) * (d * Ca)) * Kb) :=
        add_le_add hI (hZI.trans (ENNReal.ofReal_le_ofReal hbound))
    _ = _ := by
        rw [← ENNReal.ofReal_add]
        · have := a9_I_moment hKtr0 hKtr hS hN1 ht hfield
          positivity
        · have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
          have hKtot0 : 0 ≤ Kb := (tsum_nonneg fun j => a9K_nonneg (d := d) Λ₁ t j).trans hKb
          positivity

end Moment2

end HRS.Main.A9
