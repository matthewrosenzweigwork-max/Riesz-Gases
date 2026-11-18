import HRS.MS.S111X1Aux1
import HRS.MH.DualityRdB1Aux
import HRS.MS.R2InterpAux7
import HRS.MP.SelfSimP2

/-!
# S11.1 X1 (energy), part 1: the force kernel `∇g`: envelope, oddness, the cancellation convention
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- the constant `σ` of the force kernel (`σ = s` or `1`) -/
def kσ (s : ℝ) : ℝ := |HRS.Whole.movtr_sigma s|

theorem kσ_nonneg (s : ℝ) : 0 ≤ kσ s := abs_nonneg _

/-- envelope of the force: `‖∇g(z)‖ ≤ σ (|z|^{-(s+1)} 1_{|z|<1} + 1)`. -/
theorem kG_envelope (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (z : Euc d) :
    ‖rieszKernelGrad d s z‖ ≤ kσ s * (HRS.MH.DualityRd.db1G (s + 1) z + 1) := by
  by_cases hz : z = 0
  · subst hz
    rw [HRS.MP.SelfSimP2.ssp2_riesz_grad_zero hd s hs0, norm_zero]
    have := HRS.MH.DualityRd.db1G_nonneg (d := d) (s + 1) 0
    have := kσ_nonneg s
    positivity
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [HRS.Whole.movtr_rieszKernelGrad_norm s hs0 hz]
    have hσ : HRS.Whole.movtr_sigma s = kσ s := by
      unfold kσ HRS.Whole.movtr_sigma
      split_ifs <;> simp [abs_of_nonneg, hs0]
    rw [hσ]
    by_cases h1 : ‖z‖ < 1
    · have : HRS.MH.DualityRd.db1G (s + 1) z = ‖z‖ ^ (-(s + 1)) := by
        unfold HRS.MH.DualityRd.db1G
        rw [Set.indicator_of_mem (by simpa using h1)]
      rw [this, show (-s - 1) = -(s + 1) by ring]
      nlinarith [kσ_nonneg s, Real.rpow_nonneg hzpos.le (-(s + 1))]
    · replace h1 := not_lt.1 h1
      have hle : ‖z‖ ^ (-s - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
      have := HRS.MH.DualityRd.db1G_nonneg (d := d) (s + 1) z
      nlinarith [kσ_nonneg s, Real.rpow_nonneg hzpos.le (-s - 1)]

theorem kG_measurable (s : ℝ) : Measurable (rieszKernelGrad d s) :=
  HRS.Whole.Q09B.q09b_measurable_rkg s

theorem kG_norm_neg (s : ℝ) (z : Euc d) : ‖rieszKernelGrad d s (-z)‖ = ‖rieszKernelGrad d s z‖ := by
  rw [HRS.MS.R2Interp.s102_rieszKernelGrad_neg, norm_neg]

/-- the uniform bound `A` of `∫ |∇g(x-y)| ρ(y) dy` -/
def kA (d : ℕ) (s M : ℝ) (ρ : Euc d → ℝ) : ℝ :=
  kσ s * (M * (∫ z, HRS.MH.DualityRd.db1G (d := d) (s + 1) z) + ∫ y, ρ y)

theorem kG_weighted (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    (x : Euc d) :
    Integrable (fun y => ρ y * ‖rieszKernelGrad d s (x - y)‖) ∧
      ∫ y, ρ y * ‖rieszKernelGrad d s (x - y)‖ ≤ kA d s M ρ := by
  have hdb := HRS.MH.DualityRd.db1G_integrable (d := d) hd hs1
  have hdbx : Integrable (fun y => HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y)) :=
    hdb.comp_sub_left x
  have hM0 : 0 ≤ M := (hρ0 0).trans (hM 0)
  have hbound : ∀ y, ρ y * ‖rieszKernelGrad d s (x - y)‖ ≤
      kσ s * (M * HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y) + ρ y) := by
    intro y
    have h1 := kG_envelope hd hs0 (x - y)
    have h2 := HRS.MH.DualityRd.db1G_nonneg (d := d) (s + 1) (x - y)
    have h3 := hρ0 y
    have h4 := hM y
    calc ρ y * ‖rieszKernelGrad d s (x - y)‖
        ≤ ρ y * (kσ s * (HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y) + 1)) :=
          mul_le_mul_of_nonneg_left h1 h3
      _ = kσ s * (ρ y * HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y) + ρ y) := by ring
      _ ≤ _ := by
          have := kσ_nonneg s
          have : ρ y * HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y) ≤
              M * HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y) :=
            mul_le_mul_of_nonneg_right h4 h2
          nlinarith
  have hint : Integrable (fun y => kσ s * (M * HRS.MH.DualityRd.db1G (d := d) (s + 1) (x - y) + ρ y)) :=
    ((hdbx.const_mul M).add hρi).const_mul _
  have hmeas : Measurable (fun y => ρ y * ‖rieszKernelGrad d s (x - y)‖) :=
    hρm.mul ((kG_measurable s).comp (measurable_const.sub measurable_id)).norm
  refine ⟨hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 y) (norm_nonneg _))]
    exact hbound y
  · refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => mul_nonneg (hρ0 y) (norm_nonneg _))
      hint (Filter.Eventually.of_forall hbound)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (hdbx.const_mul M) hρi, integral_const_mul]
    unfold kA
    rw [integral_sub_left_eq_self (fun y => HRS.MH.DualityRd.db1G (d := d) (s + 1) y) volume x]

end HRS.MS.S111X1
