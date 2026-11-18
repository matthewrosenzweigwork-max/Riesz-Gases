import HRS.MS.R26T8AP29e
import HRS.MS.R26T8AV2

/-!
# S8.2 T8A P29 (part f): value, gradient and Hessian bounds of the sum `Q0 + Ψ` of a sharp kernel and a smooth weighted kernel
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_smallRadius_nonneg (x y : Euc d) : 0 ≤ smallRadius x y := by
  unfold smallRadius; exact le_min zero_le_one (norm_nonneg _)

theorem r26t8a_p29_value (Q0 Psi : Euc d → Euc d → ℝ) {A1 B M1 MU Mf : ℝ} (hA1 : 0 ≤ A1) (hB : 0 ≤ B)
    (h1 : M1 ≤ Mf) (h2 : MU ≤ Mf)
    (hQ : ∀ x y : Euc d, x ≠ y → |Q0 x y| ≤ A1 * Phase2S82.pairWeight M1 x y * (1 + smallRadius x y ^ (2 - criticalS d) +
        if d = 4 then |Real.log (smallRadius x y)| else 0))
    (hP : ∀ x y : Euc d, |Psi x y| ≤ B * Phase2S82.pairWeight MU x y) {Afin : ℝ} (hA : A1 + B ≤ Afin) (x y : Euc d) (hxy : x ≠ y) :
    |Q0 x y + Psi x y| ≤ Afin * Phase2S82.pairWeight Mf x y * (1 + smallRadius x y ^ (2 - criticalS d) +
        if d = 4 then |Real.log (smallRadius x y)| else 0) := by
  set br : ℝ := 1 + smallRadius x y ^ (2 - criticalS d) + (if d = 4 then |Real.log (smallRadius x y)| else 0) with hbr
  have hbr1 : 1 ≤ br := by
    have : 0 ≤ smallRadius x y ^ (2 - criticalS d) := Real.rpow_nonneg (r26t8a_p29_smallRadius_nonneg x y) _
    have h3 : 0 ≤ (if d = 4 then |Real.log (smallRadius x y)| else 0) := by split_ifs <;> positivity
    rw [hbr]; linarith
  have w1 := r26t8a_p29_pairWeight_mono h1 x y
  have w2 := r26t8a_p29_pairWeight_mono h2 x y
  have w0 : 0 ≤ Phase2S82.pairWeight Mf x y := le_trans (le_trans (by
    unfold Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)) w1) le_rfl
  have a1 := hQ x y hxy
  have a2 := hP x y
  have hA0 : 0 ≤ A1 * Phase2S82.pairWeight M1 x y * br := by
    have : 0 ≤ Phase2S82.pairWeight M1 x y := by
      unfold Phase2S82.pairWeight
      exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)
    positivity
  refine (abs_add_le _ _).trans ?_
  have b1 : A1 * Phase2S82.pairWeight M1 x y * br ≤ A1 * Phase2S82.pairWeight Mf x y * br :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left w1 hA1) (by linarith)
  have b2 : B * Phase2S82.pairWeight MU x y ≤ B * Phase2S82.pairWeight Mf x y * br := by
    calc B * Phase2S82.pairWeight MU x y ≤ B * Phase2S82.pairWeight Mf x y := mul_le_mul_of_nonneg_left w2 hB
      _ ≤ B * Phase2S82.pairWeight Mf x y * br := by nlinarith [mul_nonneg hB w0]
  calc |Q0 x y| + |Psi x y| ≤ A1 * Phase2S82.pairWeight Mf x y * br + B * Phase2S82.pairWeight Mf x y * br := by linarith
    _ = (A1 + B) * Phase2S82.pairWeight Mf x y * br := by ring
    _ ≤ Afin * Phase2S82.pairWeight Mf x y * br := by
        have : 0 ≤ Phase2S82.pairWeight Mf x y * br := mul_nonneg w0 (by linarith)
        nlinarith

end HRS.MS.R26T8A

end
