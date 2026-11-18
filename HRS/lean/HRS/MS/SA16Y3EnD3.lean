import HRS.MS.SA16SEn2
import HRS.MS.SA16Y3EnD2

/-!
# S.A.16 (SA16Y3) EnD3: transport split and smoothness with derivative-only coefficients

Copies of `sa16sy_transport_split` (SA16SEn2) and `sa16so_transportFun_smooth` (SA16SOp2) with the
hypothesis `SA16DerCoef` in place of `SA16BddCoef`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section EnD3
variable {d : ℕ}

lemma sa16y3_transportFun_smoothD {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16DerCoef k B bc)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (sa16so_transportFun bc φ) := by
  unfold sa16so_transportFun
  exact ContDiff.sum fun i _ => (hb.smooth i).mul (sa16so_dir_smooth hφ _)

lemma sa16y3_transport_splitD {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16DerCoef k B bc)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (x : Euc d) :
    |partialDeriv idx (sa16so_transportFun bc φ) x -
        ∑ l, bc l x * fderiv ℝ (partialDeriv idx φ) x (EuclideanSpace.single l 1)| ≤
      (d : ℝ) * (2 ^ j * (B * ((d : ℝ) + 1) ^ j) * ‖wJet j φ x‖) := by
  have hg : ∀ l : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) :=
    fun l => sa16so_dir_smooth hφ _
  have hsplit : ∀ l : Fin d, partialDeriv idx (fun y => bc l y * fderiv ℝ φ y (EuclideanSpace.single l 1)) x =
      partialDeriv idx (fun y => (bc l y - bc l x) * fderiv ℝ φ y (EuclideanSpace.single l 1)) x +
        bc l x * fderiv ℝ (partialDeriv idx φ) x (EuclideanSpace.single l 1) := by
    intro l
    have e1 : (fun y => bc l y * fderiv ℝ φ y (EuclideanSpace.single l 1)) =
        fun y => (bc l y - bc l x) * fderiv ℝ φ y (EuclideanSpace.single l 1) +
          bc l x * fderiv ℝ φ y (EuclideanSpace.single l 1) := by
      funext y; ring
    rw [e1, sa16sy_pd_add ((hb.smooth l).sub contDiff_const |>.mul (hg l)) (contDiff_const.mul (hg l)),
      sa16sy_pd_cmul (hg l)]
    have := congrFun (sa16sy_pd_comm hφ l idx) x
    rw [this]
  have hT : sa16so_transportFun bc φ = fun y => ∑ l : Fin d, bc l y * fderiv ℝ φ y (EuclideanSpace.single l 1) := rfl
  rw [hT, sa16sy_pd_sum Finset.univ (fun l _ => (hb.smooth l).mul (hg l))]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l : Fin d, |partialDeriv idx (fun y => (bc l y - bc l x) * fderiv ℝ φ y (EuclideanSpace.single l 1)) x|
      ≤ ∑ l : Fin d, 2 ^ j * (B * ((d : ℝ) + 1) ^ j) * ‖wJet j φ x‖ :=
        Finset.sum_le_sum fun l _ => sa16y3_sy_comm_termD (hb.smooth l) (fun i hi1 hi y => hb.bound l i hi1 hi y) hb.nonneg hφ l hj idx x
    _ = _ := by simp


end EnD3

end HRS.Whole.AppendixA.Phase2SA16R
