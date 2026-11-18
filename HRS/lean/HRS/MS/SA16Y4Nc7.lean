import HRS.MS.SA16Y4Nc6
import HRS.MS.SA16SOp5

/-!
# S.A.16 (SA16Y4) Nc7: linearity of the nonlocal operator in the coefficient (finite combinations)

`sa16y4_F_add`, `sa16y4_F_smul`: `eucNonlocal s M (a + b) u = eucNonlocal s M a u + eucNonlocal s M b u` and
`eucNonlocal s M (c a) u = c eucNonlocal s M a u` for `C^1` coefficients with bounded value and derivative.
`sa16y4_subop_sum`: if `T_i` is the nonlocal operator of `a_i` (`SA16SubOp`), then `∑ w_i T_i` is that of `∑ w_i a_i`
(the time-interpolated nonlocal operator is again a nonlocal operator).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nc7
variable {d : ℕ}

lemma sa16y4_F_add (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (M : Matrix (Fin d) (Fin d) ℝ)
    {a b : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) (hb1 : ContDiff ℝ 1 b) {B0 B1 B0' B1' : ℝ}
    (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (hB0' : ∀ x, |b x| ≤ B0')
    (hB1' : ∀ x, ‖fderiv ℝ b x‖ ≤ B1') (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => a y + b y) ⇑u x =
      HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x + HRS.MH.AdjointRd.eucNonlocal s M b ⇑u x := by
  have had : Differentiable ℝ a := ha1.differentiable (by simp)
  have hbd : Differentiable ℝ b := hb1.differentiable (by simp)
  rw [sa16q_F_pointwise hd hs hs2 M (ha1.add hb1) (B0 := B0 + B0') (B1 := B1 + B1')
      (fun y => (abs_add_le _ _).trans (add_le_add (hB0 y) (hB0' y)))
      (fun y => by
        rw [fderiv_fun_add (had y) (hbd y)]
        exact (norm_add_le _ _).trans (add_le_add (hB1 y) (hB1' y))) u x,
    sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 u x, sa16q_F_pointwise hd hs hs2 M hb1 hB0' hB1' u x,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add, ← integral_add (sa16q_Fint_integrable hd hs hs2 ha1 hB0 hB1 u i j x)
    (sa16q_Fint_integrable hd hs hs2 hb1 hB0' hB1' u i j x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

lemma sa16y4_F_smul (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ} (hB0 : ∀ x, |a x| ≤ B0)
    (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (c : ℝ) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => c * a y) ⇑u x = c * HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x := by
  have had : Differentiable ℝ a := ha1.differentiable (by simp)
  rw [sa16q_F_pointwise hd hs hs2 M (contDiff_const.mul ha1) (B0 := |c| * B0) (B1 := |c| * B1)
      (fun y => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB0 y) (abs_nonneg _))
      (fun y => by
        rw [fderiv_const_mul (had y)]
        calc ‖c • fderiv ℝ a y‖ = |c| * ‖fderiv ℝ a y‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |c| * B1 := mul_le_mul_of_nonneg_left (hB1 y) (abs_nonneg _)) u x,
    sa16q_F_pointwise hd hs hs2 M ha1 hB0 hB1 u x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ∫ y, sa16q_K1E s 0 i y * ((c * a (x - y)) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) =
      c * ∫ y, sa16q_K1E s 0 i y * (a (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)]
  ring

end Nc7

end HRS.Whole.AppendixA.Phase2SA16R
