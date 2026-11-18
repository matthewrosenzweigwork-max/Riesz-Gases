/-
# HRS.Equilibrium.Q84eAuxK — packet Q84e: `L²` norms of centred statistics from variance bounds
-/
import HRS.Equilibrium.PairMoments
import HRS.Equilibrium.Q84eAuxJ

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

/-- `‖F - E F‖_{L²(P)} = evariance(F)^{1/2}`. -/
theorem q84e_eLp_center_eq {α : Type*} [MeasurableSpace α] (P : Measure α) {F : α → ℝ}
    (hF : AEStronglyMeasurable F P) :
    eLpNorm (centeredUnder P F) 2 P = (evariance F P) ^ (1 / 2 : ℝ) := by
  have hm : AEStronglyMeasurable (centeredUnder P F) P := hF.sub aestronglyMeasurable_const
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
  simp only [ENNReal.toReal_ofNat, one_div]
  unfold evariance centeredUnder
  simp_rw [ENNReal.rpow_two]

theorem q84e_eLp_center_le {α : Type*} [MeasurableSpace α] (P : Measure α) {F : α → ℝ}
    (hF : AEStronglyMeasurable F P) (a : ℝ)
    (ha : 0 ≤ a) (h : evariance F P ≤ ENNReal.ofReal a) :
    eLpNorm (centeredUnder P F) 2 P ≤ ENNReal.ofReal (Real.sqrt a) := by
  rw [q84e_eLp_center_eq P hF, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ha (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- Finite variance gives `L²`, hence integrability, on a probability space. -/
theorem q84e_integrable_of_evariance {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {F : α → ℝ} (hF : AEStronglyMeasurable F P) {a : ℝ}
    (h : evariance F P ≤ ENNReal.ofReal a) : Integrable F P := by
  have : MemLp F 2 P :=
    (evariance_lt_top_iff_memLp hF).1 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  exact this.integrable one_le_two

/-- Centred `L²` norm of an a.e. linear combination of three statistics with finite variance. -/
theorem q84e_err_L2 {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {E FJ T B : α → ℝ} {c1 aJ aT aB : ℝ} (haJ : 0 ≤ aJ) (haT : 0 ≤ aT) (haB : 0 ≤ aB)
    (hE : ∀ᵐ x ∂P, E x = -c1 * FJ x + T x - B x)
    (hJm : AEStronglyMeasurable FJ P) (hTm : AEStronglyMeasurable T P)
    (hBm : AEStronglyMeasurable B P)
    (hJ : evariance FJ P ≤ ENNReal.ofReal aJ) (hT : evariance T P ≤ ENNReal.ofReal aT)
    (hB : evariance B P ≤ ENNReal.ofReal aB) :
    eLpNorm (centeredUnder P E) 2 P ≤
      ENNReal.ofReal (|c1| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) := by
  have iJ := q84e_integrable_of_evariance P hJm hJ
  have iT := q84e_integrable_of_evariance P hTm hT
  have iB := q84e_integrable_of_evariance P hBm hB
  have hint : ∫ x, E x ∂P = -c1 * ∫ x, FJ x ∂P + ∫ x, T x ∂P - ∫ x, B x ∂P := by
    have i1 : Integrable (fun x => -c1 * FJ x) P := iJ.const_mul (-c1)
    have i2 : Integrable (fun x => -c1 * FJ x + T x) P := i1.add iT
    rw [integral_congr_ae hE, integral_sub i2 iB, integral_add i1 iT, integral_const_mul]
  have hae : centeredUnder P E =ᵐ[P] fun x => (-c1) * centeredUnder P FJ x +
      centeredUnder P T x - centeredUnder P B x := by
    filter_upwards [hE] with x hx
    unfold centeredUnder
    rw [hx, hint]
    ring
  have e1 : eLpNorm (fun x => (-c1) * centeredUnder P FJ x) 2 P =
      ENNReal.ofReal |c1| * eLpNorm (centeredUnder P FJ) 2 P := by
    have := eLpNorm_const_smul (-c1) (centeredUnder P FJ) 2 P
    simp only [smul_eq_mul, Pi.smul_def] at this
    rw [this, Real.enorm_eq_ofReal_abs, abs_neg]
  calc eLpNorm (centeredUnder P E) 2 P
      = eLpNorm (fun x => (-c1) * centeredUnder P FJ x + centeredUnder P T x -
          centeredUnder P B x) 2 P := eLpNorm_congr_ae hae
    _ ≤ eLpNorm (fun x => (-c1) * centeredUnder P FJ x + centeredUnder P T x) 2 P +
          eLpNorm (centeredUnder P B) 2 P := eLpNorm_sub_le one_le_two
    _ ≤ (eLpNorm (fun x => (-c1) * centeredUnder P FJ x) 2 P + eLpNorm (centeredUnder P T) 2 P) +
          eLpNorm (centeredUnder P B) 2 P := by
        gcongr
        exact eLpNorm_add_le one_le_two
    _ ≤ (ENNReal.ofReal |c1| * ENNReal.ofReal (Real.sqrt aJ) + ENNReal.ofReal (Real.sqrt aT)) +
          ENNReal.ofReal (Real.sqrt aB) := by
        rw [e1]
        gcongr
        · exact q84e_eLp_center_le P hJm aJ haJ hJ
        · exact q84e_eLp_center_le P hTm aT haT hT
        · exact q84e_eLp_center_le P hBm aB haB hB
    _ = ENNReal.ofReal (|c1| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _)
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _), ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)]

end HRS.Q84e

end
