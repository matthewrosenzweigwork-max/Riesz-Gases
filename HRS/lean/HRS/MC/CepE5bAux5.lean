import HRS.MC.CepE5bAux4

/-!
# Packet CEPE5B, auxiliary 5: the Hessian trace of the Moreau envelope

`τ_n(z) = ∑_i D²Φ_n(z)(e_i, e_i) ≤ n ∑_p min(N, (2/n) h1'(y_p))`, `y = J_n z`, and the pointwise bound
`(1/n) τ_n(z) ≤ c₁ r Q_n(z) + c₂ r + c₃/(n r²)`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE1 (cepe1_h1 cepe1_pairGrad cepe1_vec cepe1_inner_vec)
open HRS.MC.CepE4 (e4_rho)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

/-- Sum over pairs of the capped Hessian entries. -/
def e5b_T (a : ℝ) (N : ℕ) (n : ℝ) (y : Ch N) : ℝ :=
  ∑ k : Fin N, ∑ l : Fin N, if k < l then min (N : ℝ) (2 / n * e5b_h1' a N (y l - y k)) else 0

/-- The unit vectors. -/
def e5b_e (i : Fin N) : Ch N := EuclideanSpace.single i (1 : ℝ)

theorem e5b_trace_hq (a : ℝ) (y : Ch N) :
    ∑ i : Fin N, e5b_hq a N y (e5b_e i) (e5b_e i) =
      ∑ k : Fin N, ∑ l : Fin N, if k < l then 2 * e5b_h1' a N (y l - y k) else 0 := by
  unfold e5b_hq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    rw [← Finset.mul_sum]
    have : ∑ i : Fin N, ((e5b_e i : Ch N) l - (e5b_e i : Ch N) k) * ((e5b_e i : Ch N) l - (e5b_e i : Ch N) k) = 2 := by
      have hne : l ≠ k := hkl.ne'
      simp only [e5b_e, EuclideanSpace.single_apply]
      have : ∀ i : Fin N, ((if l = i then (1 : ℝ) else 0) - (if k = i then 1 else 0)) *
          ((if l = i then (1 : ℝ) else 0) - (if k = i then 1 else 0)) =
          (if l = i then 1 else 0) + (if k = i then 1 else 0) := by
        intro i
        by_cases h1 : l = i
        · have h2 : k ≠ i := fun h => hne (h1.trans h.symm)
          simp [h1, h2]
        · by_cases h2 : k = i
          · simp [h1, h2]
          · simp [h1, h2]
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      norm_num
    rw [this]; ring
  · simp [hkl]

theorem e5b_min_add_le {m x y : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min m (x + y) ≤ min m x + min m y := by
  by_cases h1 : m ≤ x
  · have : min m x = m := min_eq_left h1
    have : 0 ≤ min m y := le_min hm hy
    calc min m (x + y) ≤ m := min_le_left _ _
      _ ≤ _ := by linarith
  · by_cases h2 : m ≤ y
    · have : min m y = m := min_eq_left h2
      have : 0 ≤ min m x := le_min hm hx
      calc min m (x + y) ≤ m := min_le_left _ _
        _ ≤ _ := by linarith
    · push_neg at h1 h2
      rw [min_eq_right h1.le, min_eq_right h2.le]
      exact min_le_right _ _

theorem e5b_min_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {m : ℝ}
    (hm : 0 ≤ m) : min m (∑ i ∈ s, f i) ≤ ∑ i ∈ s, min m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [hm]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    refine (e5b_min_add_le hm (hf j) (Finset.sum_nonneg fun i _ => hf i)).trans ?_
    linarith

theorem e5b_min_sum2_le {m : ℝ} (hm : 0 ≤ m) (f : Fin N → Fin N → ℝ) (hf : ∀ k l, 0 ≤ f k l) :
    min m (∑ k, ∑ l, f k l) ≤ ∑ k, ∑ l, min m (f k l) := by
  refine (e5b_min_sum_le Finset.univ (fun k => ∑ l, f k l) (fun k => Finset.sum_nonneg fun l _ => hf k l) hm).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  exact e5b_min_sum_le Finset.univ (fun l => f k l) (hf k) hm

theorem e5b_h1'_nonneg' (ha : 0 ≤ a) (y : Ch N) (k l : Fin N) :
    0 ≤ (if k < l then 2 * e5b_h1' a N (y l - y k) else 0) := by
  split_ifs
  · have := e5b_h1'_nonneg (N := N) ha (y l - y k); linarith
  · exact le_rfl

/-- The Hessian trace of the envelope is bounded by `n T`. -/
theorem e5b_trace_le (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i) ≤ n * e5b_T a N n (J n z) := by
  have hb := fun i => e5b_hess_bounds ha hJ hn z (e5b_e i)
  have h1 : ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i) ≤ n * N := by
    calc _ ≤ ∑ _i : Fin N, n := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := (hb i).2.1
          have hn1 : ‖(e5b_e i : Ch N)‖ = 1 := by simp [e5b_e]
          rw [hn1] at this
          simpa using this
      _ = n * N := by simp [mul_comm]
  have h2 : ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i) ≤
      ∑ k : Fin N, ∑ l : Fin N, if k < l then 2 * e5b_h1' a N (J n z l - J n z k) else 0 := by
    rw [← e5b_trace_hq]
    exact Finset.sum_le_sum fun i _ => (hb i).2.2
  have hmin := e5b_min_sum2_le (m := n * N) (by positivity) _ (e5b_h1'_nonneg' ha.le (J n z))
  have h3 : ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i) ≤
      min (n * N) (∑ k : Fin N, ∑ l : Fin N, if k < l then 2 * e5b_h1' a N (J n z l - J n z k) else 0) :=
    le_min h1 h2
  refine h3.trans (hmin.trans ?_)
  unfold e5b_T
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    rw [mul_min_of_nonneg _ _ hn.le]
    refine le_of_eq (congrArg₂ min rfl ?_)
    field_simp
  · simp [hkl]

end HRS.MC.CepE5b
