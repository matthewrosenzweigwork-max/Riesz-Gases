import HRS.MS.SuppU9
import HRS.MS.SuppU9Aux2
import HRS.MS.GoMax

/-!
# SOL40 packet 9b (wR37): power-six companion of the Hilbert-martingale maximal estimate

Mechanical adaptation of `HRS.MS.U9.u9_bound` (power two) to exponent six, using
`HRS.HilbertBDG.hilbert_bdg 6`. The reconstruction lemmas `u9_traceNormForm_nonneg`,
`u9_continuous_recon`, `u9_pointwise`, `u9_lintegral_trace` are reused from `HRS.MS.U9`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.U9

variable {d : ℕ} {m T : ℝ}

/-- Power-six reconstruction bound from the Hilbert BDG hypothesis `hb` (exponent `6`). -/
theorem fp81s21_u9_bound_six (hT : 0 ≤ T) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → KSpace d m T}
    {Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)} (Cbdg : ℝ)
    (hb : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ (6 : ℝ) ∂P ≤
      ENNReal.ofReal Cbdg * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal (traceNormForm (Sg r ω))) ^ ((6 : ℝ) / 2) ∂P) :
    ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 6 ∂P ≤
      ENNReal.ofReal (3 + Real.sqrt T) ^ 6 * (ENNReal.ofReal Cbdg *
        ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ) ∂P) := by
  have hL : ∀ x : ℝ≥0∞, x ^ (6 : ℝ) = x ^ (6 : ℕ) := fun x => by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  have hR : ∀ x : ℝ≥0∞, x ^ ((6 : ℝ) / 2) = x ^ (3 : ℕ) := fun x => by
    rw [show ((6 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [hL, hR] at hb
  calc ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 6 ∂P
      ≤ ∫⁻ ζ, ENNReal.ofReal (3 + Real.sqrt T) ^ 6 *
          (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ζ‖ₑ) ^ (6 : ℕ) ∂P := by
        refine lintegral_mono fun ζ => ?_
        rw [← mul_pow]
        gcongr
        exact iSup_le fun t => u9_pointwise hT M ζ t t.2
    _ = ENNReal.ofReal (3 + Real.sqrt T) ^ 6 *
          ∫⁻ ζ, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ζ‖ₑ) ^ (6 : ℕ) ∂P :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (3 + Real.sqrt T) ^ 6 * (ENNReal.ofReal Cbdg *
          ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ) ∂P) :=
        mul_le_mul' le_rfl hb

/-- Power-six maximal estimate, with the constant `C₆ = (3 + √T)^6 · C_BDG(6)` depending only on `T`. -/
theorem fp81s21_orbit_maximal_six (m T : ℝ) (hT : 0 ≤ T) (d : ℕ) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧ ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → KSpace d m T)
      (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ T M Sg →
      (∀ᵐ ζ ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => reconstructPath m T M ζ t) ∧
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 6 ∂P ≤
        ENNReal.ofReal C₆ * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ) ∂P := by
  obtain ⟨Cbdg, hCbdg, hbdg⟩ := HRS.HilbertBDG.hilbert_bdg 6 (by norm_num)
  have h3 : (0 : ℝ) ≤ 3 + Real.sqrt T := by positivity
  have h6 : (0 : ℝ) ≤ (3 + Real.sqrt T) ^ 6 := by positivity
  refine ⟨(3 + Real.sqrt T) ^ 6 * Cbdg, mul_nonneg h6 hCbdg, ?_⟩
  intro Ω mΩ P hP ℱ M Sg hM
  refine ⟨?_, ?_⟩
  · filter_upwards [hM.cont] with ζ hζ
    exact u9_continuous_recon hT M ζ hζ
  · have key := fp81s21_u9_bound_six (d := d) (m := m) (ℱ := ℱ) hT Cbdg
      (hbdg Ω P ℱ (KSpace d m T) T M Sg hM)
    have hsplit : ENNReal.ofReal ((3 + Real.sqrt T) ^ 6 * Cbdg) =
        ENNReal.ofReal (3 + Real.sqrt T) ^ 6 * ENNReal.ofReal Cbdg := by
      rw [ENNReal.ofReal_mul h6, ENNReal.ofReal_pow h3]
    rw [hsplit, mul_assoc]
    exact key

/-- Power-six maximal estimate with the trace bracket bounded a.e. by a constant `K`:
the bound is `ofReal (C₆ * K^3)`, with `C₆` (depending only on `T`) preceding all data. -/
theorem fp81s21_orbit_maximal_six_of_bracket_le (m T : ℝ) (hT : 0 ≤ T) (d : ℕ) :
    ∃ C₆ : ℝ, 0 ≤ C₆ ∧ ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (M : ℝ → Ω → KSpace d m T)
      (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ T M Sg → ∀ K : ℝ, 0 ≤ K →
      (∀ᵐ ζ ∂P, ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ) ≤ K) →
      ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖reconstructPath m T M ζ t‖) ^ 6 ∂P ≤
        ENNReal.ofReal (C₆ * K ^ 3) := by
  obtain ⟨C₆, hC₆, hmax⟩ := fp81s21_orbit_maximal_six m T hT d
  refine ⟨C₆, hC₆, ?_⟩
  intro Ω mΩ P hP ℱ M Sg hM K hK hbd
  have hmx := (hmax P ℱ M Sg hM).2
  have hlin : ∀ᵐ ζ ∂P, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ)
      ≤ ENNReal.ofReal (K ^ 3) := by
    filter_upwards [hM.sigma_pathint, hbd] with ζ hζ hζK
    have hJ : 0 ≤ ∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ) :=
      integral_nonneg fun r => u9_traceNormForm_nonneg (Sg r ζ)
    have he : ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ)) =
        ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ζ)) :=
      (ofReal_integral_eq_lintegral_ofReal hζ
        (Filter.Eventually.of_forall fun r => u9_traceNormForm_nonneg (Sg r ζ))).symm
    rw [he, ← ENNReal.ofReal_pow hJ]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hJ hζK 3)
  have hmono : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ζ))) ^ (3 : ℕ) ∂P
      ≤ ∫⁻ _ζ, ENNReal.ofReal (K ^ 3) ∂P :=
    lintegral_mono_ae hlin
  rw [lintegral_const, measure_univ, mul_one] at hmono
  have hsplit : ENNReal.ofReal (C₆ * K ^ 3) = ENNReal.ofReal C₆ * ENNReal.ofReal (K ^ 3) :=
    ENNReal.ofReal_mul hC₆
  rw [hsplit]
  exact hmx.trans (mul_le_mul' le_rfl hmono)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_u9_bound_six
#print axioms HRS.Fp81.S21.fp81s21_orbit_maximal_six
#print axioms HRS.Fp81.S21.fp81s21_orbit_maximal_six_of_bracket_le
