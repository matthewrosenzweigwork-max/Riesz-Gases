import HRS.Uniform.Q54cAux40
import HRS.Uniform.Q45Gauss
import HRS.Prob.HilbertBDG

/-!
# Q54c, part 41: the coupled Gaussian noises with the two covariance densities, and their `L²` bounds
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform HRS.PDE

variable {d : ℕ}

theorem covDens_eq_ite {n q T : ℝ} {μ : ℝ → Torus d → ℝ} (r : ℝ) :
    (if r ≤ T then covDens n q T μ r else 0) = covDens n q T μ r := by
  by_cases h : r ≤ T
  · rw [if_pos h]
  · rw [if_neg h]
    unfold covDens
    rw [if_neg (fun hr => h hr.2)]

theorem covDens_eq_ite' {n q T : ℝ} (hT : 0 ≤ T) {μ : ℝ → Torus d → ℝ} (r : ℝ) :
    (if ENNReal.ofReal r ≤ ENNReal.ofReal T then covDens n q T μ r else 0) = covDens n q T μ r := by
  have : ENNReal.ofReal r ≤ ENNReal.ofReal T ↔ r ≤ T := by
    rw [ENNReal.ofReal_le_ofReal_iff hT]
  simp only [this]
  exact covDens_eq_ite r

theorem noise_bundle {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {T : ℝ} (hT : 0 < T) {q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) {μ₁ μ₂ : ℝ → Torus d → ℝ}
    (hprob₁ : ∀ σ ∈ Set.Icc 0 T, IsProbDensity (μ₁ σ))
    (hprob₂ : ∀ σ ∈ Set.Icc 0 T, IsProbDensity (μ₂ σ))
    (hw₁ : ∀ ψ : Torus d → ℝ, Continuous ψ → ContinuousOn (fun r => ∫ x, ψ x * μ₁ r x) (Set.Icc 0 T))
    (hw₂ : ∀ ψ : Torus d → ℝ, Continuous ψ → ContinuousOn (fun r => ∫ x, ψ x * μ₂ r x) (Set.Icc 0 T))
    (hc₁ : ∀ σ ∈ Set.Icc 0 T, Continuous (μ₁ σ)) (hc₂ : ∀ σ ∈ Set.Icc 0 T, Continuous (μ₂ σ))
    {δ : ℝ} (hδ : ∀ σ ∈ Set.Icc 0 T, ∀ x, |μ₁ σ x - μ₂ σ x| ≤ δ) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (ℱ' : Filtration ℝ mΩ') (G₁ G₂ : ℝ → Ω' → NegSobolev d n),
      (∀ ω, Continuous fun τ => G₁ τ ω) ∧ (∀ ω, Continuous fun τ => G₂ τ ω) ∧
      (∀ ω, G₁ 0 ω = 0) ∧ (∀ ω, G₂ 0 ω = 0) ∧
      IsHilbertMartingaleWithCovariation P' ℱ' T G₁ (fun r _ => covDens n q₁ T μ₁ r) ∧
      IsHilbertMartingaleWithCovariation P' ℱ' T G₂ (fun r _ => covDens n q₂ T μ₂ r) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G₁ t ω - G₂ t ω‖ₑ) ^ (2 : ℝ) ∂P' ≤
        ENNReal.ofReal (HilbertBDG.bdgConst 2 * (4 * d * HRS.Uniform.Q14.q14S d (n - 1) *
          (q₁ * δ + |q₁ - q₂|) * T)) ∧
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G₁ t ω‖ₑ) ^ (2 : ℝ) ∂P' ≤
        ENNReal.ofReal (HilbertBDG.bdgConst 2 * (4 * q₁ * d * HRS.Uniform.Q14.q14S d (n - 1) * T)) := by
  have hDb₁ := isDetCovDensity_covDens hn hq₁ hprob₁ hw₁ hc₁
  have hDb₂ := isDetCovDensity_covDens hn hq₂ hprob₂ hw₂ hc₂
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, ℱ₁, G, hGc, hG0, hGM⟩ :=
    HRS.Uniform.Q45.exists_gaussian_martingale (H := NegSobolev d n) T hT.le _ hDb₁
  have hGM' : IsHilbertMartingaleWithCovariation P₁ ℱ₁ T G (fun r _ => covDens n q₁ T μ₁ r) := by
    have : (fun (r : ℝ) (_ : Ω₁) => if r ≤ T then covDens n q₁ T μ₁ r else 0) =
        fun r _ => covDens n q₁ T μ₁ r := funext fun r => funext fun _ => covDens_eq_ite r
    rw [this] at hGM; exact hGM
  obtain ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, hcoup, hGbc, hGb0⟩ :=
    q54c_coupling_strong P₁ ℱ₁ T hT.le ⟨⊥, bot_le⟩ G (fun r _ => covDens n q₁ T μ₁ r) hGM'
      (covDens n q₂ T μ₂) hDb₂
  haveI : IsProbabilityMeasure (P' : Measure Ω') := inferInstance
  have hMπ := hcoup.martingale T hT.le le_rfl
  have hGb := hcoup.gaussian T hT.le le_rfl
  have hGb' : IsHilbertMartingaleWithCovariation (P' : Measure Ω') ℱ' T Gb
      (fun r _ => covDens n q₂ T μ₂ r) := by
    have : (fun (r : ℝ) (_ : Ω') => if ENNReal.ofReal r ≤ ENNReal.ofReal T then
        covDens n q₂ T μ₂ r else 0) = fun r _ => covDens n q₂ T μ₂ r :=
      funext fun r => funext fun _ => covDens_eq_ite' hT.le r
    have h2 : (fun (r : ℝ) (_ : Ω') => if ENNReal.ofReal r ≤ ENNReal.ofReal T then
        covDens n q₂ T μ₂ r else 0) = fun r _ => if ENNReal.ofReal r ≤ ENNReal.ofReal T then
        covDens n q₂ T μ₂ r else 0 := rfl
    rw [this] at hGb; exact hGb
  have hdiff := hcoup.difference T hT.le le_rfl
  have hcost := hcoup.cost
  refine ⟨Ω', mΩ', (P' : Measure Ω'), inferInstance, ℱ', fun τ ω => G τ (π ω), Gb,
    fun ω => hGc (π ω), hGbc, fun ω => hG0 (π ω), hGb0, hMπ, hGb', ?_, ?_⟩
  · -- the difference
    have hb := HilbertBDG.hilbert_bdg_aux hdiff (p := 2) (by norm_num)
    set β : ℝ := 4 * d * HRS.Uniform.Q14.q14S d (n - 1) * (q₁ * δ + |q₁ - q₂|) with hβdef
    have hβ : ∀ᵐ ω ∂(P' : Measure Ω'), ∀ r ∈ Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (traceNormForm (if r ≤ T then Sd r ω else 0)) ≤ ENNReal.ofReal β := by
      filter_upwards [hcost] with ω hω r hr
      rw [if_pos hr.2]
      have h1 := hω r hr.1 (by rw [ENNReal.ofReal_le_ofReal_iff hT.le]; exact hr.2)
      have h1' : traceNormForm (Sd r ω) =
          HRS.Uniform.bures2 (covDens n q₁ T μ₁ r) (covDens n q₂ T μ₂ r) := h1
      rw [h1', covDens_of_mem hr, covDens_of_mem hr]
      exact ENNReal.ofReal_le_ofReal (bures2_covForm_le hn hq₁ hq₂ (hprob₁ r hr) (hprob₂ r hr)
        (hc₁ r hr) (hc₂ r hr) (hδ r hr))
    have hint : ∀ᵐ ω ∂(P' : Measure Ω'),
        (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (if r ≤ T then Sd r ω else 0))) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal β * ENNReal.ofReal T := by
      filter_upwards [hβ] with ω hω
      have h2 : (2 : ℝ) / 2 = 1 := by norm_num
      rw [h2, ENNReal.rpow_one]
      calc _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal β :=
            setLIntegral_mono' measurableSet_Icc hω
        _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    have hle : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (traceNormForm (if r ≤ T then Sd r ω else 0))) ^ ((2 : ℝ) / 2) ∂(P' : Measure Ω') ≤
        ENNReal.ofReal β * ENNReal.ofReal T := by
      refine (lintegral_mono_ae hint).trans ?_
      simp
    have hl : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G t (π ω) - Gb t ω‖ₑ) ^ (2 : ℝ) ∂(P' : Measure Ω') =
        ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
          ‖G (min t T) (π ω) - Gb (min t T) ω‖ₑ) ^ (2 : ℝ) ∂(P' : Measure Ω') := by
      refine lintegral_congr fun ω => ?_
      congr 1
      refine iSup_congr fun t => iSup_congr fun ht => ?_
      rw [min_eq_left ht.2]
    show ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖G t (π ω) - Gb t ω‖ₑ) ^ (2 : ℝ) ∂(P' : Measure Ω') ≤ _
    rw [hl]
    refine hb.trans ?_
    have hbdg0 := HilbertBDG.bdgConst_nonneg 2
    have hβ0 : 0 ≤ β := by
      have := HRS.Uniform.Q14.q14S_nonneg d (n - 1)
      have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0 ⟨le_rfl, hT.le⟩ (Classical.arbitrary _))
      positivity
    calc ENNReal.ofReal (HilbertBDG.bdgConst 2) * _ ≤
        ENNReal.ofReal (HilbertBDG.bdgConst 2) * (ENNReal.ofReal β * ENNReal.ofReal T) :=
          mul_le_mul' le_rfl hle
      _ = _ := by
          rw [← ENNReal.ofReal_mul hβ0, ← ENNReal.ofReal_mul hbdg0]
  · have hb := HilbertBDG.hilbert_bdg_aux hMπ (p := 2) (by norm_num)
    set β : ℝ := 4 * q₁ * d * HRS.Uniform.Q14.q14S d (n - 1) with hβdef
    have hint : ∀ ω : Ω',
        (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (covDens n q₁ T μ₁ r))) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal β * ENNReal.ofReal T := by
      intro ω
      have h2 : (2 : ℝ) / 2 = 1 := by norm_num
      rw [h2, ENNReal.rpow_one]
      calc _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal β := by
            refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
            exact ENNReal.ofReal_le_ofReal (covDens_trace hn hq₁ hprob₁ hr).2
        _ = _ := by rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    have hle : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (covDens n q₁ T μ₁ r))) ^
        ((2 : ℝ) / 2) ∂(P' : Measure Ω') ≤ ENNReal.ofReal β * ENNReal.ofReal T := by
      refine (lintegral_mono hint).trans ?_
      simp
    refine hb.trans ?_
    have hbdg0 := HilbertBDG.bdgConst_nonneg 2
    have hβ0 : 0 ≤ β := by
      have := HRS.Uniform.Q14.q14S_nonneg d (n - 1)
      positivity
    calc ENNReal.ofReal (HilbertBDG.bdgConst 2) * _ ≤
        ENNReal.ofReal (HilbertBDG.bdgConst 2) * (ENNReal.ofReal β * ENNReal.ofReal T) :=
          mul_le_mul' le_rfl hle
      _ = _ := by
          rw [← ENNReal.ofReal_mul hβ0, ← ENNReal.ofReal_mul hbdg0]

end HRS.Uniform.Q54c
