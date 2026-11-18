import Mathlib

/-!
# Packet CEPE1, auxiliary 1: gradients of pair potentials `z ↦ ∑_{k<l} h(z_l - z_k)` on `ℝ^N`
-/

open scoped RealInnerProductSpace NNReal

noncomputable section

namespace HRS.MC.CepE1

/-- Chamber coordinates (copy of `HRS.MC.Cepa.Ch`). -/
abbrev Ch (N : ℕ) := EuclideanSpace ℝ (Fin N)

variable {N : ℕ}

/-- The vector `e_l - e_k`. -/
def cepe1_vec (k l : Fin N) : Ch N := EuclideanSpace.single l (1 : ℝ) - EuclideanSpace.single k (1 : ℝ)

theorem cepe1_inner_vec (k l : Fin N) (z : Ch N) : inner ℝ (cepe1_vec k l) z = z l - z k := by
  simp [cepe1_vec, inner_sub_left, EuclideanSpace.inner_single_left]

theorem cepe1_vec_apply (k l i : Fin N) :
    (cepe1_vec k l) i = (if i = l then 1 else 0) - (if i = k then 1 else 0) := by
  simp [cepe1_vec, EuclideanSpace.single_apply]

/-- The pair potential. -/
def cepe1_pair (h : ℝ → ℝ) (z : Ch N) : ℝ := ∑ k, ∑ l, if k < l then h (z l - z k) else 0

/-- Its candidate gradient. -/
def cepe1_pairGrad (h' : ℝ → ℝ) (z : Ch N) : Ch N :=
  ∑ k, ∑ l, if k < l then h' (z l - z k) • cepe1_vec k l else 0

theorem cepe1_hasGradientAt_term {h : ℝ → ℝ} {c : ℝ} (v z : Ch N) (hd : HasDerivAt h c (inner ℝ v z)) :
    HasGradientAt (fun w : Ch N => h (inner ℝ v w)) (c • v) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have := hd.comp_hasFDerivAt z (innerSL ℝ v).hasFDerivAt
  have e : InnerProductSpace.toDual ℝ (Ch N) (c • v) = c • innerSL ℝ v := by
    ext w
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  rw [e]
  exact this

theorem cepe1_hasGradientAt_pair {h h' : ℝ → ℝ} {z : Ch N}
    (hd : ∀ k l : Fin N, k < l → HasDerivAt h (h' (z l - z k)) (z l - z k)) :
    HasGradientAt (cepe1_pair h) (cepe1_pairGrad h' z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have key : ∀ k l : Fin N, HasFDerivAt (fun w : Ch N => if k < l then h (w l - w k) else 0)
      (if k < l then InnerProductSpace.toDual ℝ (Ch N) (h' (z l - z k) • cepe1_vec k l) else 0) z := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      have := cepe1_hasGradientAt_term (h := h) (c := h' (z l - z k)) (cepe1_vec k l) z
        (by rw [cepe1_inner_vec]; exact hd k l hkl)
      rw [hasGradientAt_iff_hasFDerivAt] at this
      exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [cepe1_inner_vec])
    · simp only [hkl, ite_false]
      exact hasFDerivAt_const _ _
  have hs := HasFDerivAt.sum (u := Finset.univ) (x := z)
    (A := fun k : Fin N => ∑ l : Fin N, fun w : Ch N => if k < l then h (w l - w k) else 0)
    (A' := fun k => ∑ l : Fin N,
      (if k < l then InnerProductSpace.toDual ℝ (Ch N) (h' (z l - z k) • cepe1_vec k l) else 0))
    (fun k _ => HasFDerivAt.sum (fun l _ => key k l))
  convert hs using 1
  · ext w
    simp [cepe1_pair, Finset.sum_apply]
  · unfold cepe1_pairGrad
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp

theorem cepe1_pairGrad_apply (h' : ℝ → ℝ) (z : Ch N) (i : Fin N) :
    (cepe1_pairGrad h' z) i =
      (∑ k, if k < i then h' (z i - z k) else 0) - ∑ l, if i < l then h' (z l - z i) else 0 := by
  unfold cepe1_pairGrad
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  have : ∀ k l : Fin N, (if k < l then h' (z l - z k) • cepe1_vec k l else 0) i =
      (if i = l then (if k < l then h' (z l - z k) else 0) else 0) -
        (if i = k then (if k < l then h' (z l - z k) else 0) else 0) := by
    intro k l
    by_cases hkl : k < l
    · by_cases h1 : i = l
      · have h2 : ¬ i = k := fun h2 => hkl.ne' (h1.symm.trans h2)
        simp [hkl, h1, h2, cepe1_vec_apply, hkl.ne']
      · by_cases h2 : i = k
        · simp [hkl, h1, h2, cepe1_vec_apply, hkl.ne]
        · simp [hkl, h1, h2, cepe1_vec_apply]
    · simp [hkl]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem cepe1_lip_sum {ι E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] (s : Finset ι)
    (f : ι → E → F) (K : ι → ℝ≥0) (h : ∀ i ∈ s, LipschitzWith (K i) (f i)) :
    LipschitzWith (∑ i ∈ s, K i) (fun x => ∑ i ∈ s, f i x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  calc dist (∑ i ∈ s, f i x) (∑ i ∈ s, f i y) ≤ ∑ i ∈ s, dist (f i x) (f i y) := dist_sum_sum_le _ _ _
    _ ≤ ∑ i ∈ s, (K i : ℝ) * dist x y :=
        Finset.sum_le_sum fun i hi => (h i hi).dist_le_mul x y
    _ = ((∑ i ∈ s, K i : ℝ≥0) : ℝ) * dist x y := by
        rw [NNReal.coe_sum, Finset.sum_mul]

theorem cepe1_lip_term {h' : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h') (v : Ch N) :
    LipschitzWith (L * ‖v‖₊ * ‖v‖₊) (fun z : Ch N => h' (inner ℝ v z) • v) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
  have h1 := hL.dist_le_mul (inner ℝ v x) (inner ℝ v y)
  have h2 : dist (inner ℝ v x) (inner ℝ v y) ≤ ‖v‖ * dist x y := by
    rw [Real.dist_eq, ← inner_sub_right, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _)
  calc dist (h' (inner ℝ v x)) (h' (inner ℝ v y)) * ‖v‖ ≤ (L * (‖v‖ * dist x y)) * ‖v‖ := by
        gcongr
        exact h1.trans (by gcongr)
    _ = ((L * ‖v‖₊ * ‖v‖₊ : ℝ≥0) : ℝ) * dist x y := by
        push_cast
        ring

theorem cepe1_lip_pairGrad {h' : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L h') :
    ∃ K : ℝ≥0, LipschitzWith K (cepe1_pairGrad (N := N) h') := by
  refine ⟨∑ k : Fin N, ∑ l : Fin N, L * ‖cepe1_vec k l‖₊ * ‖cepe1_vec k l‖₊, ?_⟩
  have : cepe1_pairGrad (N := N) h' = fun z => ∑ k, ∑ l, if k < l then h' (z l - z k) • cepe1_vec k l else 0 :=
    rfl
  rw [this]
  refine cepe1_lip_sum Finset.univ _ _ fun k _ => ?_
  refine cepe1_lip_sum Finset.univ _ _ fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    have h := cepe1_lip_term hL (cepe1_vec k l)
    simpa only [cepe1_inner_vec] using h
  · simp only [hkl, ite_false]
    exact (LipschitzWith.const 0).weaken zero_le

theorem cepe1_contDiff_pair {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 1 (cepe1_pair (N := N) h) := by
  unfold cepe1_pair
  refine ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    exact hh.comp (((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ).contDiff).sub
      ((EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).contDiff))
  · simp only [hkl, ite_false]
    exact contDiff_const

theorem cepe1_hasGradientAt_add {f g : Ch N → ℝ} {f' g' : Ch N} {x : Ch N}
    (hf : HasGradientAt f f' x) (hg : HasGradientAt g g' x) :
    HasGradientAt (fun w => f w + g w) (f' + g') x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_add]
  exact hf.add hg

theorem cepe1_hasGradientAt_sum {ι : Type*} (s : Finset ι) {f : ι → Ch N → ℝ} {f' : ι → Ch N} {x : Ch N}
    (h : ∀ i ∈ s, HasGradientAt (f i) (f' i) x) :
    HasGradientAt (fun w => ∑ i ∈ s, f i w) (∑ i ∈ s, f' i) x := by
  simp only [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_sum]
  exact HasFDerivAt.fun_sum h

theorem cepe1_lip_const_mul {f : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L f) (c : ℝ) :
    LipschitzWith (‖c‖₊ * L) (fun u => c * f u) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  have := hL.dist_le_mul x y
  simp only [Real.dist_eq] at this
  push_cast
  simp only [Real.norm_eq_abs]
  calc |c| * |f x - f y| ≤ |c| * (L * |x - y|) := by gcongr
    _ = _ := by rw [Real.dist_eq]; ring

end HRS.MC.CepE1
