import HRS.MS.SA16E1Liou1

/-!
# S.A.16 E1: Liouville's formula for linear integral equations with measurable bounded coefficients
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution

theorem e1_vec_sum {d : ℕ} (w : Euc d) : w = ∑ k, w k • EuclideanSpace.single k (1 : ℝ) := by
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem e1_aci_const {a b : ℝ} (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

theorem e1_aci_sum {ι : Type*} {a b : ℝ} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ s, f i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using e1_aci_const (a := a) (b := b) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem e1_aci_prod {ι : Type*} {a b : ℝ} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∏ i ∈ s, f i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using e1_aci_const (a := a) (b := b) 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem e1_aci_det {n : ℕ} {a b : ℝ} (N : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, AbsolutelyContinuousOnInterval (fun s => N s i j) a b) :
    AbsolutelyContinuousOnInterval (fun s => (N s).det) a b := by
  have e : (fun s => (N s).det) = fun s => ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ i, N s (π i) i := by
    funext s
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e]
  refine e1_aci_sum _ _ fun π _ => ?_
  exact (e1_aci_prod _ _ fun i _ => h (π i) i).const_mul _

end HRS.Whole.AppendixA.Phase2SA16Evolution
