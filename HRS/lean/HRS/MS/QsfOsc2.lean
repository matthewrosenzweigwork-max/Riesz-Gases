import HRS.MS.QsfOsc1

/-!
# S4.5 oscillator clause, part 2: the Fréchet derivative of `h_α`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

/-- `α - e_i` (truncated). -/
def s45_dec (α : MultiIndex d) (i : Fin d) : MultiIndex d := Function.update α i (α i - 1)

/-- `α + e_i`. -/
def s45_inc (α : MultiIndex d) (i : Fin d) : MultiIndex d := Function.update α i (α i + 1)

theorem s45_hermiteFunD_update (α : MultiIndex d) (i : Fin d) (v : ℕ) (x : Euc d) :
    hermiteFunD (Function.update α i v) x =
      (∏ k ∈ Finset.univ.erase i, hermiteFun (α k) (x k)) * hermiteFun v (x i) := by
  unfold hermiteFunD
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rw [Function.update_self]

theorem s45_fderiv_hermiteFunD (α : MultiIndex d) :
    fderiv ℝ (hermiteFunD α) = fun x => ∑ i : Fin d,
      (Real.sqrt ((α i : ℝ) / 2) * hermiteFunD (s45_dec α i) x -
        Real.sqrt (((α i : ℝ) + 1) / 2) * hermiteFunD (s45_inc α i) x) •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
  funext x
  have h : ∀ i : Fin d, HasFDerivAt (fun y : Euc d => hermiteFun (α i) (y i))
      ((Real.sqrt ((α i : ℝ) / 2) * hermiteFun (α i - 1) (x i) -
        Real.sqrt (((α i : ℝ) + 1) / 2) * hermiteFun (α i + 1) (x i)) •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) x := fun i => by
    have h1 := (s45_hasDerivAt_hermiteFun (α i) (x i)).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
    exact h1
  have hp := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => h i)
  have e : hermiteFunD α = fun y => ∏ i ∈ Finset.univ, hermiteFun (α i) (y i) := rfl
  rw [e, hp.fderiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_assoc, smul_eq_mul]
  congr 1
  rw [mul_sub, s45_dec, s45_inc, s45_hermiteFunD_update, s45_hermiteFunD_update]
  ring

theorem s45_degree_inc (α : MultiIndex d) (i : Fin d) : (s45_inc α i).degree = α.degree + 1 := by
  unfold MultiIndex.degree s45_inc
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

theorem s45_degree_dec_le (α : MultiIndex d) (i : Fin d) : (s45_dec α i).degree ≤ α.degree := by
  unfold MultiIndex.degree s45_dec
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : k = i
  · subst h; simp
  · rw [Function.update_of_ne h]

theorem s45_le_degree (α : MultiIndex d) (i : Fin d) : α i ≤ α.degree :=
  Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end S45

end
