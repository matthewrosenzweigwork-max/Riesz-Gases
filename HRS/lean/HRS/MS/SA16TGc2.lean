import HRS.MS.SA16TGc1
import HRS.MS.SA16SOp5

/-!
# S.A.16 (SA16T) Gc2: `eucNonlocal` is linear in the density, and only sees the density on `supp u`

`sa16t_F_sub`, `sa16t_F_smul`: pointwise linearity of `a ↦ eucNonlocal s M a u x` (`u` Schwartz, `a ∈ C^1` bounded with
bounded gradient).  `sa16t_F_local`: replacing `a` by `χ a` with `χ = 1` on `tsupport u` does not change it.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Q

section Gc2
variable {d : ℕ}

lemma sa16t_F_local (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (a χ F : Euc d → ℝ) {R0 : ℝ}
    (hF : tsupport F ⊆ closedBall (0 : Euc d) R0) (hχ : ∀ y, ‖y‖ ≤ R0 → χ y = 1) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => χ y * a y) F = HRS.MH.AdjointRd.eucNonlocal s M a F := by
  funext x
  unfold HRS.MH.AdjointRd.eucNonlocal
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hfun : (fun x' => ∫ y, rieszKernel d s (x' - y) *
      ((fun y => χ y * a y) y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) =
      fun x' => ∫ y, rieszKernel d s (x' - y) * (a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) := by
    funext x'
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)) = 0
    · simp [hy]
    · have h1 : fderiv ℝ F y ≠ 0 := fun h => hy (by simp [h])
      have h2 : y ∈ tsupport F := support_fderiv_subset ℝ h1
      have h3 := hF h2
      rw [mem_closedBall_zero_iff] at h3
      simp [hχ y h3]
  rw [hfun]

variable (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

lemma sa16t_F_sub (M : Matrix (Fin d) (Fin d) ℝ) {a b : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) (hb1 : ContDiff ℝ 1 b)
    {A0 A1 B0 B1 : ℝ} (hA0 : ∀ x, |a x| ≤ A0) (hA1 : ∀ x, ‖fderiv ℝ a x‖ ≤ A1)
    (hB0 : ∀ x, |b x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ b x‖ ≤ B1) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => a y - b y) ⇑u x =
      HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x - HRS.MH.AdjointRd.eucNonlocal s M b ⇑u x := by
  have hab1 : ContDiff ℝ 1 (fun y => a y - b y) := ha1.sub hb1
  have hab0 : ∀ y, |a y - b y| ≤ A0 + B0 := fun y => (abs_sub _ _).trans (add_le_add (hA0 y) (hB0 y))
  have hda : Differentiable ℝ a := ha1.differentiable (by norm_num)
  have hdb : Differentiable ℝ b := hb1.differentiable (by norm_num)
  have hab2 : ∀ y, ‖fderiv ℝ (fun y => a y - b y) y‖ ≤ A1 + B1 := fun y => by
    rw [fderiv_fun_sub (hda y) (hdb y)]
    exact (norm_sub_le _ _).trans (add_le_add (hA1 y) (hB1 y))
  rw [sa16q_F_pointwise hd hs hs2 M hab1 hab0 hab2 u x, sa16q_F_pointwise hd hs hs2 M ha1 hA0 hA1 u x,
    sa16q_F_pointwise hd hs hs2 M hb1 hB0 hB1 u x, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub, ← integral_sub (sa16q_Fint_integrable hd hs hs2 ha1 hA0 hA1 u i j x)
    (sa16q_Fint_integrable hd hs hs2 hb1 hB0 hB1 u i j x)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  ring

lemma sa16t_F_smul (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {A0 A1 : ℝ}
    (hA0 : ∀ x, |a x| ≤ A0) (hA1 : ∀ x, ‖fderiv ℝ a x‖ ≤ A1) (c : ℝ) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => c * a y) ⇑u x = c * HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x := by
  have hc1 : ContDiff ℝ 1 (fun y => c * a y) := contDiff_const.mul ha1
  have hc0 : ∀ y, |c * a y| ≤ |c| * A0 := fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA0 y) (abs_nonneg _)
  have hda : Differentiable ℝ a := ha1.differentiable (by norm_num)
  have hc2 : ∀ y, ‖fderiv ℝ (fun y => c * a y) y‖ ≤ |c| * A1 := fun y => by
    rw [fderiv_const_mul (hda y)]
    refine (norm_smul c _).le.trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hA1 y) (abs_nonneg _)
  rw [sa16q_F_pointwise hd hs hs2 M hc1 hc0 hc2 u x, sa16q_F_pointwise hd hs hs2 M ha1 hA0 hA1 u x,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ∫ y, sa16q_K1E s 0 i y * (c * a (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) =
      c * ∫ y, sa16q_K1E s 0 i y * (a (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  simp only [this]
  ring

end Gc2

end HRS.Whole.AppendixA.Phase2SA16R
