import HRS.MS.S82P2Grad1
import HRS.MS.CritForceNF3

/-!
# S8.2 A02 (S82V), part 1a: smoothness of rows and the Laplacian of a finite sum
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82v_sum_succAbove {α : Type*} [AddCommGroup α] {m : ℕ} (f : Fin (m + 1) → α) (i : Fin (m + 1)) :
    ∑ k : Fin m, f (i.succAbove k) = ∑ j ∈ Finset.univ.erase i, f j := by
  have h1 := Fin.sum_univ_succAbove f i
  have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 1))) f (Finset.mem_univ i)
  have : f i + ∑ k : Fin m, f (i.succAbove k) = f i + ∑ j ∈ Finset.univ.erase i, f j := by
    rw [← h1, h2]
  exact add_left_cancel this

lemma s82v_Q_contDiffAt {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x z : Euc d) (hxz : x ≠ z) :
    ContDiffAt ℝ 2 (fun y => Q y z) x := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have h1 : ContDiffAt ℝ 8 (Function.uncurry Q) (x, z) :=
    hQ.smooth.contDiffAt (hopen.mem_nhds hxz)
  have h2 : ContDiffAt ℝ 8 (fun y : Euc d => (y, z)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  exact ContDiffAt.of_le (h1.comp x h2) (show (2 : WithTop ℕ∞) ≤ 8 by norm_num)

lemma s82v_laplacian_sum {ι : Type*} (s : Finset ι) (g : ι → Euc d → ℝ) (x : Euc d)
    (hg : ∀ k ∈ s, ContDiffAt ℝ 2 (g k) x) :
    Laplacian.laplacian (fun y => ∑ k ∈ s, g k y) x = ∑ k ∈ s, Laplacian.laplacian (g k) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have e : (fun y : Euc d => ∑ k ∈ (∅ : Finset ι), g k y) = fun _ => (0 : ℝ) := by
        funext y; simp
      rw [e, InnerProductSpace.laplacian_const]; simp
  | insert j s hj ih =>
      have hs : ∀ k ∈ s, ContDiffAt ℝ 2 (g k) x := fun k hk => hg k (Finset.mem_insert_of_mem hk)
      have h1 : ContDiffAt ℝ 2 (g j) x := hg j (Finset.mem_insert_self j s)
      have h2 : ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, g k y) x :=
        ContDiffAt.sum fun k hk => hs k hk
      have e : (fun y => ∑ k ∈ insert j s, g k y) = g j + fun y => ∑ k ∈ s, g k y := by
        funext y; simp [Finset.sum_insert hj]
      rw [e, h1.laplacian_add h2, ih hs, Finset.sum_insert hj]

end HRS.MS.S82V

end
