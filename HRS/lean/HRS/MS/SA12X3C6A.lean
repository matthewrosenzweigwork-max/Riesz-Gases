import HRS.MS.SA12X2R36

/-!
# S.A.12 C6 (SA12X3), part A: translation covariance

Shifting the variable by `q` leaves `partialDeriv`, `jetSq`, `dissipSq`, `jetPair` and `eucNonlocal` covariant.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_pd_shift {n : ℕ} (idx : Fin n → Fin d) (f : Euc d → ℝ) (q x : Euc d) :
    partialDeriv idx (fun y => f (y + q)) x = partialDeriv idx f (x + q) := by
  unfold partialDeriv
  rw [iteratedFDeriv_comp_add_right]

theorem sa12x3_jetSq_shift (m : ℕ) (w F : Euc d → ℝ) (q : Euc d) :
    jetSq m (fun y => w (y + q)) (fun y => F (y + q)) = jetSq m w F := by
  unfold jetSq
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp_rw [sa12x3_pd_shift]
  exact integral_add_right_eq_self (fun x => (w x * partialDeriv idx F x) ^ 2) q

theorem sa12x3_dissipSq_shift (m : ℕ) (w F : Euc d → ℝ) (q : Euc d) :
    dissipSq m (fun y => w (y + q)) (fun y => F (y + q)) = dissipSq m w F := by
  unfold dissipSq
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [sa12x3_pd_shift]
  exact integral_add_right_eq_self (fun x => (w x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2) q

theorem sa12x3_jetPair_shift (m : ℕ) (w F G : Euc d → ℝ) (q : Euc d) :
    jetPair m (fun y => w (y + q)) (fun y => F (y + q)) (fun y => G (y + q)) = jetPair m w F G := by
  unfold jetPair
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  simp_rw [sa12x3_pd_shift]
  exact integral_add_right_eq_self (fun x => w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) q

theorem sa12x3_eucNL_shift (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (a F : Euc d → ℝ) (q x : Euc d) :
    eucNonlocal s M (fun y => a (y + q)) (fun y => F (y + q)) x = eucNonlocal s M a F (x + q) := by
  unfold eucNonlocal
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  set e : Euc d := EuclideanSpace.single j (1 : ℝ)
  have h : (fun x' => ∫ y, rieszKernel d s (x' - y) * (a (y + q) *
        fderiv ℝ (fun y => F (y + q)) y e)) =
      (fun x'' => ∫ y, rieszKernel d s (x'' - y) * (a y * fderiv ℝ F y e)) ∘ (fun x' => x' + q) := by
    funext x'
    simp only [Function.comp, fderiv_comp_add_right]
    have := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
      (fun u => rieszKernel d s (x' + q - u) * (a u * fderiv ℝ F u e)) q
    rw [← this]
    simp only [add_sub_add_right_eq_sub]
  rw [h]
  have hfd := fderiv_comp_add_right (𝕜 := ℝ) (f := fun x'' => ∫ y, rieszKernel d s (x'' - y) *
    (a y * fderiv ℝ F y e)) (x := x) q
  simp only [Function.comp_def] at hfd ⊢
  rw [hfd]

end HRS.MH.AdjointRd.Phase2SA12Construction
