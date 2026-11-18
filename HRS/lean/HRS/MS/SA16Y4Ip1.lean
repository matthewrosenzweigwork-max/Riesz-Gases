import HRS.MS.SA16Y3Dc1
import HRS.MS.SA16SOp3

/-!
# S.A.16 (SA16Y4) Ip1: convex combinations of coefficients (time interpolation)

`sa16y4_derCoef_convex`, `sa16y4_bddCoef_convex`: a finite convex combination `∑ w_i c_i` of coefficient families with the
common constant `B` is again `SA16DerCoef k B` (resp. `SA16BddCoef k B`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Ip1
variable {d : ℕ} {ι : Type*}

lemma sa16y4_iter_convex (s : Finset ι) (w : ι → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    {f : ι → EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) {B : ℝ} {n : ℕ}
    (hB : ∀ i ∈ s, ∀ x, ‖iteratedFDeriv ℝ n (f i) x‖ ≤ B) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ n (fun y => ∑ i ∈ s, w i * f i y) x‖ ≤ B := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (contDiff_const.mul (hf i hi)).contDiffAt.of_le
    (by exact_mod_cast le_top))]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ s, ‖iteratedFDeriv ℝ n (fun y => w i * f i y) x‖ ≤ ∑ i ∈ s, w i * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have h := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := n) (x := x) (a := w i) (f := f i)
          ((hf i hi).contDiffAt.of_le (by exact_mod_cast le_top))
        rw [show (fun y => w i * f i y) = w i • f i from rfl, h]
        calc ‖w i • iteratedFDeriv ℝ n (f i) x‖ = |w i| * ‖iteratedFDeriv ℝ n (f i) x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ w i * B := by
              rw [abs_of_nonneg (hw0 i hi)]
              exact mul_le_mul_of_nonneg_left (hB i hi x) (hw0 i hi)
    _ = B := by rw [← Finset.sum_mul, hw1, one_mul]

lemma sa16y4_derCoef_convex (s : Finset ι) (w : ι → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    {k : ℕ} {B : ℝ} {c : ι → Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hc : ∀ i ∈ s, SA16DerCoef k B (c i)) :
    SA16DerCoef k B (fun j x => ∑ i ∈ s, w i * c i j x) := by
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  obtain ⟨i0, hi0⟩ := hne
  exact ⟨(hc i0 hi0).nonneg, fun j => ContDiff.sum fun i hi => contDiff_const.mul ((hc i hi).smooth j),
    fun j n hn1 hnk x => sa16y4_iter_convex s w hw0 hw1 (fun i hi => (hc i hi).smooth j)
      (fun i hi y => (hc i hi).bound j n hn1 hnk y) x⟩

lemma sa16y4_bddCoef_convex (s : Finset ι) (w : ι → ℝ) (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1)
    {k : ℕ} {B : ℝ} {c : ι → Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hc : ∀ i ∈ s, SA16BddCoef k B (c i)) :
    SA16BddCoef k B (fun j x => ∑ i ∈ s, w i * c i j x) := by
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  obtain ⟨i0, hi0⟩ := hne
  exact ⟨(hc i0 hi0).nonneg, fun j => ContDiff.sum fun i hi => contDiff_const.mul ((hc i hi).smooth j),
    fun j n hn x => sa16y4_iter_convex s w hw0 hw1 (fun i hi => (hc i hi).smooth j)
      (fun i hi y => (hc i hi).bound j n hn y) x⟩

end Ip1

end HRS.Whole.AppendixA.Phase2SA16R
