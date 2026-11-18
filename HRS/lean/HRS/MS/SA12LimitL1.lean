import HRS.MS.SA12LimitDefs
import HRS.MS.UniqM1Fin
import HRS.MS.UniqC3c

/-!
# S.A.12 L1: the cell pairing bound `|∫ u g| ≤ ‖u‖_{H⁰_uloc} · cellL2Sum g`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MS.UniqM1

variable {d : ℕ}

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued functions in the form `∫ fg ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}`. -/
theorem sa12l1_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a * g a ∂μ ≤ (∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two hf hg
  simpa [ENNReal.rpow_two] using h

-- BEGIN SA12.L1
theorem cell_pair_bound (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (B : ℝ) (hB : 0 ≤ B) (u g : Euc d → ℝ)
    (hu : ulocNormE 0 χ u ≤ ENNReal.ofReal B)
    (hg : AEStronglyMeasurable g volume) (hgf : cellL2Sum g < ⊤) :
    Integrable (fun x => u x * g x) ∧
      |∫ x, u x * g x| ≤ B * (cellL2Sum g).toReal := by
  have hfm := locMass_of_ulocNormE hχ hB hu
  have hcover : (Set.univ : Set (Euc d)) ⊆ ⋃ z : Fin d → ℤ, Metric.ball (cellPt d z) 1 := by
    intro w _
    obtain ⟨z, hz⟩ := HRS.MS.UniqC3.exists_cellPt_near hd w
    exact Set.mem_iUnion.2 ⟨z, by
      rw [Metric.mem_ball, dist_eq_norm]; linarith⟩
  have hcell : ∀ z : Fin d → ℤ, ∫⁻ x in Metric.ball (cellPt d z) 1, ‖u x * g x‖ₑ ≤
      ENNReal.ofReal B * (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ) := by
    intro z
    have h1 := sa12l1_cs (volume.restrict (Metric.ball (cellPt d z) 1)) (f := fun x => ‖u x‖ₑ)
      (g := fun x => ‖g x‖ₑ) hfm.1.enorm.restrict hg.enorm.restrict
    have h2 : ∫⁻ x in Metric.ball (cellPt d z) 1, ‖u x * g x‖ₑ =
        ∫⁻ x in Metric.ball (cellPt d z) 1, ‖u x‖ₑ * ‖g x‖ₑ :=
      lintegral_congr fun x => by rw [enorm_mul]
    have h3 : ∫⁻ x in Metric.ball (cellPt d z) 1, ‖g x‖ₑ ^ 2 =
        ∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2) :=
      lintegral_congr fun x => by
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have h4 : (∫⁻ x in Metric.ball (cellPt d z) 1, ‖u x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal B := by
      calc (∫⁻ x in Metric.ball (cellPt d z) 1, ‖u x‖ₑ ^ 2) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal (B ^ 2)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (hfm.2 _) (by norm_num)
        _ = ENNReal.ofReal B := by
          rw [ENNReal.ofReal_pow hB, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    rw [h2]
    refine h1.trans ?_
    rw [h3]
    exact mul_le_mul' h4 le_rfl
  have hsum : ∫⁻ x, ‖u x * g x‖ₑ ≤ ENNReal.ofReal B * cellL2Sum g := by
    calc ∫⁻ x, ‖u x * g x‖ₑ = ∫⁻ x in Set.univ, ‖u x * g x‖ₑ := by rw [Measure.restrict_univ]
      _ ≤ ∫⁻ x in ⋃ z : Fin d → ℤ, Metric.ball (cellPt d z) 1, ‖u x * g x‖ₑ :=
          lintegral_mono_set hcover
      _ ≤ ∑' z : Fin d → ℤ, ∫⁻ x in Metric.ball (cellPt d z) 1, ‖u x * g x‖ₑ :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' z : Fin d → ℤ, ENNReal.ofReal B *
            (∫⁻ x in Metric.ball (cellPt d z) 1, ENNReal.ofReal (g x ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.tsum_le_tsum hcell
      _ = ENNReal.ofReal B * cellL2Sum g := by
          rw [ENNReal.tsum_mul_left]; rfl
  have hfin : ∫⁻ x, ‖u x * g x‖ₑ < ⊤ :=
    hsum.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgf)
  have hint : Integrable (fun x => u x * g x) volume := ⟨hfm.1.mul hg, hfin⟩
  refine ⟨hint, ?_⟩
  calc |∫ x, u x * g x| ≤ ∫ x, ‖u x * g x‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = (∫⁻ x, ‖u x * g x‖ₑ).toReal := integral_norm_eq_lintegral_enorm hint.1
    _ ≤ (ENNReal.ofReal B * cellL2Sum g).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgf.ne) hsum
    _ = B * (cellL2Sum g).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB]
-- END SA12.L1

end HRS.MH.AdjointRd.Phase2SA12Limit
