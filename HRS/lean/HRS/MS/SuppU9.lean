import HRS.MS.SuppU9Aux1
import HRS.MS.SuppU9Aux2

/-!
# U9: the frozen statement `HRS.Whole.orbit_maximal` (Lemma S5.2, clauses (i) and (ii))

Clause (i): `u9_exists_form` (`SuppU9Aux1`), with `Ctr = 2 n B²`.
Clause (ii): `‖(𝒯M)(t)‖ ≤ (3 + √T) sup_s ‖M_s‖` (`SuppU9Aux2`), continuity of `evalA`, and
`hilbert_bdg` with `p = 2`; `Cmax = (3 + √T)² C_BDG`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.U9

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

lemma u9_traceNormForm_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (C : H →L[ℝ] H →L[ℝ] ℝ) : 0 ≤ traceNormForm C :=
  Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma u9_continuous_recon (hT : 0 ≤ T) {Ω : Type*} (M : ℝ → Ω → KSpace d m T) (ζ : Ω)
    (hc : ContinuousOn (fun τ => M τ ζ) (Set.Icc 0 T)) :
    Continuous fun t : Set.Icc (0 : ℝ) T => reconstructPath m T M ζ t := by
  unfold reconstructPath
  have h1 : Continuous fun t : Set.Icc (0 : ℝ) T => (M T ζ).evalA t :=
    continuousOn_iff_continuous_restrict.1 (u9_continuousOn_evalA hT (M T ζ))
  have h3 : Continuous fun t : Set.Icc (0 : ℝ) T => (M t ζ).B :=
    continuousOn_iff_continuous_restrict.1 (u9_continuous_B.comp_continuousOn hc)
  exact (h1.sub continuous_const).add h3

lemma u9_pointwise (hT : 0 ≤ T) {Ω : Type*} (M : ℝ → Ω → KSpace d m T) (ζ : Ω) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ENNReal.ofReal ‖reconstructPath m T M ζ t‖ ≤
      ENNReal.ofReal (3 + Real.sqrt T) * ⨆ s ∈ Set.Icc (0 : ℝ) T, ‖M s ζ‖ₑ := by
  set S := ⨆ s ∈ Set.Icc (0 : ℝ) T, ‖M s ζ‖ₑ with hS
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hx : ‖M T ζ‖ₑ ≤ S := le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0 : ℝ) T) => ‖M s ζ‖ₑ) T hTm
  have hy : ‖M t ζ‖ₑ ≤ S := le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0 : ℝ) T) => ‖M s ζ‖ₑ) t ht
  have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have h := u9_recon_norm_le hT (M T ζ) (M t ζ) t
  calc ENNReal.ofReal ‖reconstructPath m T M ζ t‖
      ≤ ENNReal.ofReal ((2 + Real.sqrt T) * ‖M T ζ‖ + ‖M t ζ‖) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (2 + Real.sqrt T) * ‖M T ζ‖ₑ + ‖M t ζ‖ₑ := by
        rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _), ENNReal.ofReal_mul (by positivity),
          ofReal_norm, ofReal_norm]
    _ ≤ ENNReal.ofReal (2 + Real.sqrt T) * S + 1 * S := by
        gcongr; rw [one_mul]; exact hy
    _ = ENNReal.ofReal (3 + Real.sqrt T) * S := by
        rw [← add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num)]
        congr 2; ring


lemma u9_lintegral_trace {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → KSpace d m T}
    {Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ))) ∂P =
      ENNReal.ofReal (∫ ζ, (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) ∂P) := by
  have hnn : ∀ ζ, 0 ≤ ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ) :=
    fun ζ => integral_nonneg fun r => u9_traceNormForm_nonneg _
  rw [ofReal_integral_eq_lintegral_ofReal hM.sigma_int (Filter.Eventually.of_forall hnn)]
  refine lintegral_congr_ae ?_
  filter_upwards [hM.sigma_pathint] with ζ hζ
  rw [ofReal_integral_eq_lintegral_ofReal hζ (Filter.Eventually.of_forall fun r =>
    u9_traceNormForm_nonneg _)]

lemma u9_bound (hT : 0 ≤ T) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → KSpace d m T}
    {Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hb : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal C₂ * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (traceNormForm (Sg r ω))) ^ ((2 : ℝ) / 2) ∂P) :
    ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 2 ∂P ≤
      ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C₂ *
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) ∂P) := by
  have hJ : 0 ≤ ∫ ζ, (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) ∂P :=
    integral_nonneg fun ζ => integral_nonneg fun r => u9_traceNormForm_nonneg _
  have h22 : ((2 : ℝ) / 2) = 1 := by norm_num
  simp only [h22, ENNReal.rpow_one] at hb
  rw [u9_lintegral_trace hM] at hb
  calc ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 2 ∂P
      ≤ ∫⁻ ζ, ENNReal.ofReal (3 + Real.sqrt T) ^ 2 *
          (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ζ‖ₑ) ^ (2 : ℝ) ∂P := by
        refine lintegral_mono fun ζ => ?_
        rw [ENNReal.rpow_two, ← mul_pow]
        gcongr
        exact iSup_le fun t => u9_pointwise hT M ζ t t.2
    _ = ENNReal.ofReal (3 + Real.sqrt T) ^ 2 *
          ∫⁻ ζ, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ζ‖ₑ) ^ (2 : ℝ) ∂P :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (3 + Real.sqrt T) ^ 2 * (ENNReal.ofReal C₂ *
          ENNReal.ofReal (∫ ζ, (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) ∂P)) := by
        gcongr
    _ = ENNReal.ofReal ((3 + Real.sqrt T) ^ 2 * C₂ *
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) ∂P) := by
        have h3 : 0 ≤ 3 + Real.sqrt T := by positivity
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow h3, mul_assoc]

theorem orbit_maximal_proof : type_of% @HRS.Whole.orbit_maximal := by
  intro d C m T hT n Dop B hB hmeas
  obtain ⟨C₂, hC₂, hbdg⟩ := HRS.HilbertBDG.hilbert_bdg 2 le_rfl
  refine ⟨2 * n * B ^ 2, (3 + Real.sqrt T) ^ 2 * C₂, ?_, ?_⟩
  · intro q hq r hr ν hν
    haveI := hν
    obtain ⟨Bf, h1, h2, h3⟩ := u9_exists_form (ν := ν)
      (Γ := fun a => orbitFeature C m T (Dop a) r) hq (fun a => hmeas a r hr)
      (fun a x => hB a r hr x)
    exact ⟨Bf, h1, h2, h3⟩
  · intro Ω mΩ P hP ℱ M Sg hM
    refine ⟨?_, ?_⟩
    · filter_upwards [hM.cont] with ζ hζ
      exact u9_continuous_recon hT M ζ hζ
    · exact u9_bound hT hM C₂ hC₂ (hbdg Ω P ℱ (KSpace d m T) T M Sg hM)

end HRS.MS.U9
