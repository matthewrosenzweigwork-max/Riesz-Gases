import HRS.Main.A8PAux16

/-!
# Packet A8P, part 17: the time integral of the square root of the completed energy
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_meas_section {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (G : α → β → γ) (hG : Measurable fun p : α × β => G p.1 p.2) (r : α) : Measurable (G r) :=
  hG.comp measurable_prodMk_left

section SqrtEn

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a8p_sqrt_energy (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {ℱ : Filtration ℝ (R N).mΩ}
    (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) :
    (∀ᵐ ω ∂(R N).P, IntegrableOn (fun r => Real.sqrt (a8pEn S R N C₀ Λ r ω)) (Set.Icc (0 : ℝ) S.T)) ∧
    Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEn S R N C₀ Λ r ω)) (R N).P ∧
    ∫ ω, (∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEn S R N C₀ Λ r ω)) ∂(R N).P ≤
      S.T * Real.sqrt (𝔈 N) := by
  have hT : 0 ≤ S.T := S.hT.le
  have hGm := a8pEnC_meas hS hN hprog (C₀ := C₀) (Λ := Λ)
  have hGr : ∀ r, Measurable (a8pEnC S R N C₀ Λ r) := fun r => a8p_meas_section _ hGm r
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal (a8pEnC S R N C₀ Λ r ω) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N) := by
    intro r hr
    have h := hS.energy.bound N hN r hr
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun ω => ?_
    rw [a8pEnC_eq S R N C₀ Λ hr ω]
    unfold a8pEn
    rw [a8p_ofReal_max]
  have hE0 : 0 ≤ 𝔈 N := (hS.energy.pos N hN).le
  have hintG : ∀ r ∈ Set.Icc (0 : ℝ) S.T, Integrable (a8pEnC S R N C₀ Λ r) (R N).P := by
    intro r hr
    refine ⟨(hGr r).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt (hmom r hr) ENNReal.ofReal_lt_top)
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (a8pEnC_nonneg S R N C₀ Λ r ω)]
  have hIG : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∫ ω, a8pEnC S R N C₀ Λ r ω ∂(R N).P ≤ 𝔈 N := by
    intro r hr
    have h1 : ENNReal.ofReal (∫ ω, a8pEnC S R N C₀ Λ r ω ∂(R N).P) =
        ∫⁻ ω, ENNReal.ofReal (a8pEnC S R N C₀ Λ r ω) ∂(R N).P :=
      ofReal_integral_eq_lintegral_ofReal (hintG r hr)
        (Eventually.of_forall fun ω => a8pEnC_nonneg S R N C₀ Λ r ω)
    have h2 := hmom r hr
    rw [← h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hE0).1 h2
  have hjens : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      Integrable (fun ω => Real.sqrt (a8pEnC S R N C₀ Λ r ω)) (R N).P ∧
      ∫ ω, Real.sqrt (a8pEnC S R N C₀ Λ r ω) ∂(R N).P ≤ Real.sqrt (𝔈 N) := by
    intro r hr
    obtain ⟨h1, h2⟩ := gfb2_jensen_sqrt (R N).P _ (hGr r)
      (Eventually.of_forall fun ω => a8pEnC_nonneg S R N C₀ Λ r ω) (hintG r hr)
    exact ⟨h1, h2.trans (Real.sqrt_le_sqrt (hIG r hr))⟩
  have hFm : Measurable fun p : ℝ × (R N).Ω => Real.sqrt (a8pEnC S R N C₀ Λ p.1 p.2) := hGm.sqrt
  obtain ⟨h1, h2, h3⟩ := gfb2_time_integral (R N).P hT
    (fun r ω => Real.sqrt (a8pEnC S R N C₀ Λ r ω)) hFm
    (Eventually.of_forall fun ω r _ => Real.sqrt_nonneg _) (fun r hr => (hjens r hr).1)
    (Real.sqrt (𝔈 N)) (fun r hr => (hjens r hr).2)
  have hI : ∀ ω, ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEn S R N C₀ Λ r ω) =
      ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEnC S R N C₀ Λ r ω) := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => by
      simp only [a8pEnC_eq S R N C₀ Λ hr ω]
  simp only [hI]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h1] with ω hω
    exact hω.congr_fun (fun r hr => by simp only [a8pEnC_eq S R N C₀ Λ hr ω]) measurableSet_Icc
  · refine ⟨h3.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h2 ENNReal.ofReal_lt_top)
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc
      fun r _ => Real.sqrt_nonneg _)]
  · have hint : Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEnC S R N C₀ Λ r ω))
        (R N).P := by
      refine ⟨h3.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h2 ENNReal.ofReal_lt_top)
      refine lintegral_congr fun ω => ?_
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc
        fun r _ => Real.sqrt_nonneg _)]
    have e : ENNReal.ofReal (∫ ω, (∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEnC S R N C₀ Λ r ω)) ∂(R N).P) =
        ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEnC S R N C₀ Λ r ω)) ∂(R N).P :=
      ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Icc fun r _ => Real.sqrt_nonneg _)
    rw [← e] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end SqrtEn

end HRS.Main.A8P
