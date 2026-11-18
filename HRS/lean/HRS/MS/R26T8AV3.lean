import HRS.MS.R26T8AV2

/-!
# S8.2 T8A V3: finite sums of canonical conormal pair functions; `pairA` of a finite sum
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_V3_canonical_zero (mu : Measure (Euc d)) : CanonicalPair mu (fun _ _ : Euc d => (0 : ℝ)) :=
  ⟨fun _ => integrable_zero _ _ _, fun _ => integrable_zero _ _ _, fun _ => by simp, fun _ => by simp⟩

theorem r26t8a_V3_canonical_sum (mu : Measure (Euc d)) {ι : Type*} (s : Finset ι) {F : ι → Euc d → Euc d → ℝ}
    (h : ∀ i ∈ s, CanonicalPair mu (F i)) : CanonicalPair mu (fun x y => ∑ i ∈ s, F i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using r26t8a_V3_canonical_zero mu
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact r26t8a_canonical_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem r26t8a_V3_pairA_zero (C : WholeCoeff d) (mu : Measure (Euc d)) (x y : Euc d) :
    pairA C mu (fun _ _ : Euc d => (0 : ℝ)) x y = 0 := by
  have h0 : ∀ M : Matrix (Fin d) (Fin d) ℝ, Torus.matVec M (0 : Euc d) = 0 := fun M => by
    simp [Torus.matVec]
  unfold pairA HRS.Whole.projGeneratorW generatorW convGradConvW
  simp [gradient, h0]

theorem r26t8a_V3_pairA_sum (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (Q : ℕ → Euc d → Euc d → ℝ) (A : ℕ → ℝ) (n : ℕ) (hA : ∀ j, j < n → 0 ≤ A j)
    (hQ : ∀ j, j < n → Conormal 2 1 M (sigma - 2) (A j) (Q j)) {x y : Euc d} (hxy : x ≠ y) :
    pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (fun x y => ∑ j ∈ Finset.range n, Q j x y) x y =
      ∑ j ∈ Finset.range n, pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (Q j) x y := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact r26t8a_V3_pairA_zero _ _ x y
  | succ n ih =>
    have hs : Conormal 2 1 M (sigma - 2) (∑ j ∈ Finset.range n, A j) (fun x y => ∑ j ∈ Finset.range n, Q j x y) :=
      r26t8a_conormal_sum hchi _ (fun j hj => hQ j (by have := Finset.mem_range.1 hj; omega))
    have hsplit : (fun x y => ∑ j ∈ Finset.range (n + 1), Q j x y) =
        fun x y => (∑ j ∈ Finset.range n, Q j x y) + Q n x y := by
      funext x y; rw [Finset.sum_range_succ]
    rw [hsplit, r26t8a_V2_pairA_add hd a beta M sigma ha hbeta hM hsd rho hrho hchi
      (Finset.sum_nonneg fun j hj => hA j (by have := Finset.mem_range.1 hj; omega)) (hA n (by omega)) hs (hQ n (by omega)) hxy,
      ih (fun j hj => hA j (by omega)) (fun j hj => hQ j (by omega)), Finset.sum_range_succ]

end HRS.MS.R26T8A
