import HRS.Main.A9Aux13

/-!
# Packet A9, part 14: the initial-field term `E‖𝕀 - Ĩ‖ ≤ K_tr ε^f`, measurability of the field objects
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section InitDiff

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a9_I_diff {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)} {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) :
    ∫⁻ ω, ENNReal.ofReal ‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ∂(R N).P ≤
      ENNReal.ofReal (Ktr * εf N) := by
  have hS' := a9_standing_mStar hS
  have hA : AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    a9_adjointData a9_mStar_le_gamma hS hN
  have hd := S.hd
  have hε := hfield.εf_nonneg N hN
  obtain ⟨-, -, h0⟩ := a8p_flow_facts hS' hN
  have hfm := hfield.first_moment N hN
  have hAN := a8p_A_abs_le S N
  calc ∫⁻ ω, ENNReal.ofReal ‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ∂(R N).P
      ≤ ∫⁻ ω, ENNReal.ofReal Ktr * ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ∂(R N).P := by
        refine lintegral_mono_ae ?_
        filter_upwards [h0] with ω hω
        have e : a9I S R N t ω - a9Itil S R N t ηF ω =
            S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
              (a9F0 S R N ω - ηF N ω) := by
          unfold a9I a9Itil
          rw [← smul_sub, a9_transport_sub hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht]
        have e2 : a9F0 S R N ω = S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
            (empirical ((R N).X₀ ω)) S.μ0 := by
          unfold a9F0; rw [hω]
        rw [e, norm_smul, ← e2, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hKtr0]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hKtr (S.dyn N) (S.ρ N) hA t ht (a9F0 S R N ω - ηF N ω)
        rw [Real.norm_eq_abs]
        calc |S.AN N| * ‖transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (a9F0 S R N ω - ηF N ω)‖
            ≤ 1 * (‖a9F0 S R N ω - ηF N ω‖ * Ktr) :=
              mul_le_mul hAN h1 (norm_nonneg _) zero_le_one
          _ = Ktr * ‖a9F0 S R N ω - ηF N ω‖ := by ring
    _ = ENNReal.ofReal Ktr * ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ∂(R N).P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Ktr * ENNReal.ofReal (εf N) := by gcongr
    _ = ENNReal.ofReal (Ktr * εf N) := (ENNReal.ofReal_mul hKtr0).symm

end InitDiff

section Meas

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a9_Z_meas (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {ℱ : MeasureTheory.Filtration ℝ (R N).mΩ}
    {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) :
    Measurable (a9Z S R N t) := by
  have hρ := (hS.mean_field.solution N hN).density t ht
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ N t)) := HRS.isProb_withDensityReal hρ
  have hXm : ∀ s : ℝ≥0, Measurable ((R N).X s) := fun s => (hF.adapted s).mono (ℱ.le _) le_rfl
  exact ((measurable_ofMeasureDiff_empirical a9_gamma_gt (withDensityReal (S.ρ N t)) hN).comp
    (hXm _)).const_smul (S.sigma N)

theorem a9_I_meas (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {ℱ : MeasureTheory.Filtration ℝ (R N).mΩ}
    {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) :
    Measurable[ℱ 0] (a9I S R N t) := by
  haveI := S.hμ0
  have hA : AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    a9_adjointData a9_mStar_le_gamma hS hN
  have h1 : Measurable[ℱ 0] (a9F0 S R N) := by
    have := ((measurable_ofMeasureDiff_empirical a9_gamma_gt S.μ0 hN).comp (hF.adapted 0))
    exact this.const_smul (S.κ N)
  have h2 := a9_transport_meas S.hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht
  exact (h2.comp h1).const_smul (S.AN N)

theorem a9_Itil_meas (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)} {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) :
    Measurable (a9Itil S R N t ηF) := by
  have hA : AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    a9_adjointData a9_mStar_le_gamma hS hN
  have h2 := a9_transport_meas S.hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) hA ht
  exact (h2.comp (hfield.ηF_meas N)).const_smul (S.AN N)

end Meas

end HRS.Main.A9
