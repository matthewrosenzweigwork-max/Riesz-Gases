import HRS.MS.R26T8AP06d3

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 4): permutation invariance of iterated directional derivatives
`r26t8a_iterDir_perm`: for `f` of class `C^(length l)` and `l ~ l'` (list permutation), `iterDir l f = iterDir l' f`
(only the symmetry of the second derivative is used).  Together with `r26t8a_nest_apply` this lets one swap the order of the `X`- and `z`-derivatives.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section Perm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem r26t8a_iterDir_swap (a b : E) (l : List E) {f : E → V}
    (hf : ContDiff ℝ (((a :: b :: l).length : ℕ) : WithTop ℕ∞) f) :
    r26t8a_iterDir (a :: b :: l) f = r26t8a_iterDir (b :: a :: l) f := by
  have hg : ContDiff ℝ (2 : WithTop ℕ∞) (r26t8a_iterDir l f) := by
    have e : 2 + l.length = (a :: b :: l).length := by simp; omega
    have := r26t8a_iterDir_contDiff 2 l f (by rw [e]; exact hf)
    simpa using this
  have hd : Differentiable ℝ (fderiv ℝ (r26t8a_iterDir l f)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  funext x
  have hs : ∀ u v, fderiv ℝ (fderiv ℝ (r26t8a_iterDir l f)) x u v = fderiv ℝ (fderiv ℝ (r26t8a_iterDir l f)) x v u :=
    fun u v => hg.contDiffAt.isSymmSndFDerivAt (by simp) u v
  have key : ∀ u v : E, r26t8a_iterDir (u :: v :: l) f x = fderiv ℝ (fderiv ℝ (r26t8a_iterDir l f)) x u v := by
    intro u v
    show fderiv ℝ (fun y => fderiv ℝ (r26t8a_iterDir l f) y v) x u = _
    have h := fderiv_clm_apply (𝕜 := ℝ) (c := fun y => fderiv ℝ (r26t8a_iterDir l f) y) (u := fun _ : E => v) (x := x)
      (hd x) (differentiableAt_const v)
    rw [h]
    simp
  rw [key a b, key b a, hs]

theorem r26t8a_iterDir_perm {l l' : List E} (h : l.Perm l') {f : E → V}
    (hf : ContDiff ℝ ((l.length : ℕ) : WithTop ℕ∞) f) : r26t8a_iterDir l f = r26t8a_iterDir l' f := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    rename_i l₁ l₂
    have hf' : ContDiff ℝ ((l₁.length : ℕ) : WithTop ℕ∞) f := hf.of_le (by simp)
    funext y
    show fderiv ℝ (r26t8a_iterDir l₁ f) y x = fderiv ℝ (r26t8a_iterDir l₂ f) y x
    rw [ih hf']
  | swap x y l => exact r26t8a_iterDir_swap y x l hf
  | trans h1 h2 ih1 ih2 =>
    rename_i l₁ l₂ l₃
    rw [ih1 hf, ih2 (by rw [← h1.length_eq]; exact hf)]

theorem r26t8a_nest_swap {Φ : E × E → V} (p q : ℕ) (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) (X z : E)
    (u : Fin p → E) (v : Fin q → E) :
    r26t8a_nest p q Φ X z u v = iteratedFDeriv ℝ q
      (fun z' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E)) Φ (X, z')) z v := by
  set A := (List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) with hA
  set B := (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E) with hB
  have hH : ContDiff ℝ (q : WithTop ℕ∞) (r26t8a_iterDir A Φ) :=
    r26t8a_iterDir_contDiff q A Φ (by simpa [hA, add_comm] using hΦ)
  have hlen : (A ++ B).length = p + q := by simp [hA, hB]
  have hs : ContDiff ℝ (q : WithTop ℕ∞) (fun z' => r26t8a_iterDir A Φ (X, z')) :=
    hH.comp (contDiff_const.prodMk contDiff_id)
  rw [r26t8a_nest_apply p q hΦ X z u v,
    r26t8a_iterDir_perm (List.perm_append_comm : (A ++ B).Perm (B ++ A)) (by rw [hlen]; exact hΦ),
    r26t8a_iterDir_append, hB, r26t8a_iterDir_inr (List.ofFn v) (by simpa using hH) X z,
    ← r26t8a_iteratedFDeriv_eq_iterDir q _ hs z v]

end Perm

end HRS.MS.R26T8A
