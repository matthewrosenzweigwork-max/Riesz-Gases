import HRS.MS.S111X1E8
import HRS.MS.GapRefAux1
import HRS.MS.S111X1Aux6

/-!
# S11.1 X1 (energy), part 9: the energy field of `X1Input` from `energy_main`
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem projMean_sq_le {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (hρi : Integrable ρ) {g : Euc d → ℝ} (hg : MemLp g 2 (HRS.Whole.withDensityReal ρ)) :
    ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) g x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
      ∫ x, g x ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  have hfin : IsFiniteMeasure (HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.withDensityReal
    exact isFiniteMeasure_withDensity_ofReal hρi.2
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hμ1 : μ.real Set.univ = 1 := by
    have := HRS.MS.Gap.gap1_integral_wdr hρm hρ0 (fun _ => (1 : ℝ))
    simp only [integral_const, smul_eq_mul, mul_one] at this
    rw [hρ1] at this
    simpa using this
  set m := ∫ x, g x ∂μ with hm
  have hint : Integrable g μ := hg.integrable one_le_two
  have hg2 : Integrable (fun x => g x ^ 2) μ := hg.integrable_sq
  have e : ∀ x, HRS.Whole.projMean μ g x ^ 2 = g x ^ 2 - 2 * m * g x + m ^ 2 := by
    intro x
    unfold HRS.Whole.projMean HRS.Whole.pair
    rw [← hm]; ring
  simp_rw [e]
  have hi1 : Integrable (fun x => g x ^ 2 - 2 * m * g x) μ := hg2.sub (hint.const_mul _)
  rw [integral_add hi1 (integrable_const _), integral_sub hg2 (hint.const_mul _),
    integral_const_mul, integral_const]
  simp only [smul_eq_mul, hμ1, one_mul]
  nlinarith [sq_nonneg m, hm]

theorem energy_field {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} (E : EnData d s β ρ M C)
    (hρ1 : ∫ x, ρ x = 1) {t : ℝ} (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ψ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), IsClassicalAdjointW C t ψ f →
      (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (f 0) x ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        c * ∫ x, ψ x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ∧
      (∫ r in Set.Icc (0 : ℝ) t, ∫ x, inner ℝ (gradient (f r) x) (gradient (f r) x) * ρ x ≤
        c * ∫ x, ψ x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  have hβ := E.hβ
  have hA0 := kA_nonneg E.K
  set C₂ : ℝ := β * kA d s M ρ ^ 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨max (Real.exp (C₂ * t)) (β * (1 + C₂ * t * Real.exp (C₂ * t))), le_max_of_le_left (Real.exp_pos _).le,
    fun ψ f hf => ?_⟩
  haveI : IsFiniteMeasure (HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.withDensityReal
    exact isFiniteMeasure_withDensity_ofReal E.K.int.2
  obtain ⟨h1, h2⟩ := energy_main E ht hf
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have conv : ∀ g : Euc d → ℝ, ∫ x, g x ^ 2 ∂(HRS.Whole.withDensityReal ρ) = ∫ x, g x ^ 2 * ρ x := by
    intro g
    rw [HRS.MS.Gap.gap1_integral_wdr E.K.meas E.K.nonneg (fun x => g x ^ 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hΨ : 0 ≤ ∫ x, ψ x ^ 2 * ρ x := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (E.K.nonneg x)
  have hexp : 0 ≤ Real.exp (C₂ * t) := (Real.exp_pos _).le
  constructor
  · calc ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (f 0) x ^ 2 ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫ x, f 0 x ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
          projMean_sq_le E.K.meas E.K.nonneg hρ1 E.K.int (x1_classical_memLp hf h0 _)
      _ = ∫ x, f 0 x ^ 2 * ρ x := conv _
      _ ≤ Real.exp (C₂ * (t - 0)) * ∫ x, ψ x ^ 2 * ρ x := h1 0 h0
      _ ≤ max (Real.exp (C₂ * t)) (β * (1 + C₂ * t * Real.exp (C₂ * t))) * ∫ x, ψ x ^ 2 * ρ x := by
          rw [sub_zero]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hΨ
      _ = _ := by rw [conv ψ]
  · refine h2.trans ?_
    show β * ((∫ x, ψ x ^ 2 * ρ x) + C₂ * t * Real.exp (C₂ * t) * ∫ x, ψ x ^ 2 * ρ x) ≤ _
    rw [conv ψ]
    have : β * ((∫ x, ψ x ^ 2 * ρ x) + C₂ * t * Real.exp (C₂ * t) * ∫ x, ψ x ^ 2 * ρ x) =
        β * (1 + C₂ * t * Real.exp (C₂ * t)) * ∫ x, ψ x ^ 2 * ρ x := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hΨ

end HRS.MS.S111X1
