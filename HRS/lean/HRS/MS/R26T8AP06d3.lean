import HRS.MS.R26T8AP06b1

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 3): evaluation of nested jets as iterated directional derivatives
`iterDir l f` is the iterated directional derivative along the list of vectors `l` (head outermost).  For `f` of class `C^n`,
`D^n f x (m) = iterDir (ofFn m) f x`; and `r26t8a_nest_apply`: for `Phi` of class `C^(p+q)`,
`nest p q Phi X z u v = iterDir ((ofFn u).map inl ++ (ofFn v).map inr) Phi (X,z)`.
`r26t8a_nest_eq_joint`: the same as the joint jet `D^(p+q) Phi (X,z)` evaluated on the list (as a function `Fin (p+q) -> E x E`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section Dir

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Iterated directional derivative along a list (head = outermost derivative). -/
def r26t8a_iterDir : List E → (E → V) → (E → V)
  | [], f => f
  | m :: ms, f => fun x => fderiv ℝ (r26t8a_iterDir ms f) x m

theorem r26t8a_iterDir_append (l1 l2 : List E) (f : E → V) :
    r26t8a_iterDir (l1 ++ l2) f = r26t8a_iterDir l1 (r26t8a_iterDir l2 f) := by
  induction l1 with
  | nil => rfl
  | cons m l1 ih => simp only [List.cons_append, r26t8a_iterDir, ih]

theorem r26t8a_iterDir_contDiff (a : ℕ) : ∀ (l : List E) (g : E → V),
    ContDiff ℝ ((a + l.length : ℕ) : WithTop ℕ∞) g → ContDiff ℝ (a : WithTop ℕ∞) (r26t8a_iterDir l g)
  | [], g, hg => by simpa [r26t8a_iterDir] using hg
  | m :: ms, g, hg => by
    have h1 : ContDiff ℝ ((a + 1 : ℕ) : WithTop ℕ∞) (r26t8a_iterDir ms g) :=
      r26t8a_iterDir_contDiff (a + 1) ms g (by simpa [List.length_cons, add_assoc, add_comm, add_left_comm] using hg)
    have h2 := h1.fderiv_right (m := (a : WithTop ℕ∞)) (by push_cast; exact le_rfl)
    exact h2.clm_apply contDiff_const

theorem r26t8a_iteratedFDeriv_eq_iterDir : ∀ (n : ℕ) (f : E → V), ContDiff ℝ (n : WithTop ℕ∞) f →
    ∀ (x : E) (m : Fin n → E), iteratedFDeriv ℝ n f x m = r26t8a_iterDir (List.ofFn m) f x
  | 0, f, _, x, m => by simp [r26t8a_iterDir, iteratedFDeriv_zero_apply]
  | n + 1, f, hf, x, m => by
    rw [iteratedFDeriv_succ_apply_left, List.ofFn_succ]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      (hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)) x
    have hfun : (fun y => iteratedFDeriv ℝ n f y (Fin.tail m)) =
        r26t8a_iterDir (List.ofFn (Fin.tail m)) f := funext fun y =>
      r26t8a_iteratedFDeriv_eq_iterDir n f (hf.of_le (by exact_mod_cast Nat.le_succ n)) y (Fin.tail m)
    have := fderiv_continuousMultilinear_apply_const hd (Fin.tail m)
    rw [hfun] at this
    show (fderiv ℝ (iteratedFDeriv ℝ n f) x (m 0)) (Fin.tail m) = _
    rw [show r26t8a_iterDir (m 0 :: List.ofFn fun i => m i.succ) f x =
      fderiv ℝ (r26t8a_iterDir (List.ofFn (Fin.tail m)) f) x (m 0) from rfl, this]
    rfl

theorem r26t8a_iterDir_inr {g : E × E → V} : ∀ (ms : List E), ContDiff ℝ (ms.length : WithTop ℕ∞) g →
    ∀ Y w : E, r26t8a_iterDir (ms.map (ContinuousLinearMap.inr ℝ E E)) g (Y, w) =
      r26t8a_iterDir ms (fun w' => g (Y, w')) w
  | [], _, Y, w => rfl
  | m :: ms, hg, Y, w => by
    have hg' : ContDiff ℝ (ms.length : WithTop ℕ∞) g := hg.of_le (by simp)
    have ih := r26t8a_iterDir_inr ms hg'
    have hK : Differentiable ℝ (r26t8a_iterDir (ms.map (ContinuousLinearMap.inr ℝ E E)) g) :=
      (r26t8a_iterDir_contDiff 1 _ g (by simpa [add_comm] using hg)).differentiable (by simp)
    show fderiv ℝ (r26t8a_iterDir (ms.map (ContinuousLinearMap.inr ℝ E E)) g) (Y, w) (ContinuousLinearMap.inr ℝ E E m) =
      fderiv ℝ (r26t8a_iterDir ms (fun w' => g (Y, w'))) w m
    have e : r26t8a_iterDir ms (fun w' => g (Y, w')) =
        fun w' => r26t8a_iterDir (ms.map (ContinuousLinearMap.inr ℝ E E)) g (Y, w') := funext fun w' => (ih Y w').symm
    rw [e]
    have := (hK (Y, w)).hasFDerivAt.comp w (hasFDerivAt_prodMk_right (𝕜 := ℝ) Y w)
    rw [show (fun w' => r26t8a_iterDir (ms.map (ContinuousLinearMap.inr ℝ E E)) g (Y, w')) =
      (r26t8a_iterDir (ms.map (ContinuousLinearMap.inr ℝ E E)) g) ∘ (fun w' => (Y, w')) from rfl, this.fderiv]
    simp

theorem r26t8a_iterDir_inl {g : E × E → V} : ∀ (ms : List E), ContDiff ℝ (ms.length : WithTop ℕ∞) g →
    ∀ X z : E, r26t8a_iterDir (ms.map (ContinuousLinearMap.inl ℝ E E)) g (X, z) =
      r26t8a_iterDir ms (fun Y => g (Y, z)) X
  | [], _, X, z => rfl
  | m :: ms, hg, X, z => by
    have hg' : ContDiff ℝ (ms.length : WithTop ℕ∞) g := hg.of_le (by simp)
    have ih := r26t8a_iterDir_inl ms hg'
    have hK : Differentiable ℝ (r26t8a_iterDir (ms.map (ContinuousLinearMap.inl ℝ E E)) g) :=
      (r26t8a_iterDir_contDiff 1 _ g (by simpa [add_comm] using hg)).differentiable (by simp)
    show fderiv ℝ (r26t8a_iterDir (ms.map (ContinuousLinearMap.inl ℝ E E)) g) (X, z) (ContinuousLinearMap.inl ℝ E E m) =
      fderiv ℝ (r26t8a_iterDir ms (fun Y => g (Y, z))) X m
    have e : r26t8a_iterDir ms (fun Y => g (Y, z)) =
        fun Y => r26t8a_iterDir (ms.map (ContinuousLinearMap.inl ℝ E E)) g (Y, z) := funext fun Y => (ih Y z).symm
    rw [e]
    have := (hK (X, z)).hasFDerivAt.comp X (hasFDerivAt_prodMk_left (𝕜 := ℝ) X z)
    rw [show (fun Y => r26t8a_iterDir (ms.map (ContinuousLinearMap.inl ℝ E E)) g (Y, z)) =
      (r26t8a_iterDir (ms.map (ContinuousLinearMap.inl ℝ E E)) g) ∘ (fun Y => (Y, z)) from rfl, this.fderiv]
    simp

theorem r26t8a_nest_apply {Φ : E × E → V} (p q : ℕ) (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) (X z : E)
    (u : Fin p → E) (v : Fin q → E) :
    r26t8a_nest p q Φ X z u v = r26t8a_iterDir
      ((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++ (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E)) Φ (X, z) := by
  set K' := r26t8a_iterDir ((List.ofFn v).map (ContinuousLinearMap.inr ℝ E E)) Φ with hK'
  have hq : ContDiff ℝ (q : WithTop ℕ∞) Φ := hΦ.of_le (by exact_mod_cast Nat.le_add_left q p)
  have hK'd : ContDiff ℝ (p : WithTop ℕ∞) K' :=
    r26t8a_iterDir_contDiff p _ Φ (by simpa using hΦ)
  have step1 : ∀ Y : E, iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z v = K' (Y, z) := fun Y => by
    have hs : ContDiff ℝ (q : WithTop ℕ∞) (fun w => Φ (Y, w)) :=
      hq.comp (contDiff_const.prodMk contDiff_id)
    rw [r26t8a_iteratedFDeriv_eq_iterDir q _ hs z v, hK', r26t8a_iterDir_inr (List.ofFn v) (by simpa using hq) Y z]
  set G : E → ContinuousMultilinearMap ℝ (fun _ : Fin q => E) V := fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z with hG
  have hGd : ContDiff ℝ (p : WithTop ℕ∞) G := r26t8a_nest_contDiff q p Φ z hΦ
  set L : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) V →L[ℝ] V :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => E) V v with hL
  have e1 : iteratedFDeriv ℝ p (fun Y => L (G Y)) X =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ p G X) :=
    ContinuousLinearMap.iteratedFDeriv_comp_left L hGd.contDiffAt le_rfl
  have e2 : (fun Y => L (G Y)) = fun Y => K' (Y, z) := funext fun Y => step1 Y
  have e3 : r26t8a_nest p q Φ X z u v = iteratedFDeriv ℝ p (fun Y => K' (Y, z)) X u := by
    rw [← e2, e1]
    rfl
  rw [e3, r26t8a_iteratedFDeriv_eq_iterDir p _ (show ContDiff ℝ (p : WithTop ℕ∞) (fun Y => K' (Y, z)) from hK'd.comp (contDiff_id.prodMk contDiff_const)) X u,
    ← r26t8a_iterDir_inl (List.ofFn u) (by simpa using hK'd) X z, hK', ← r26t8a_iterDir_append]

theorem r26t8a_ofFn_getD (l : List (E × E)) (n : ℕ) (h : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i 0) = l := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_ofFn, List.getD_eq_getElem?_getD, h2]

theorem r26t8a_nest_eq_joint {Φ : E × E → V} (p q : ℕ) (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) (X z : E)
    (u : Fin p → E) (v : Fin q → E) :
    r26t8a_nest p q Φ X z u v = iteratedFDeriv ℝ (p + q) Φ (X, z) (fun i : Fin (p + q) =>
      (((List.ofFn u).map (ContinuousLinearMap.inl ℝ E E) ++ (List.ofFn v).map (ContinuousLinearMap.inr ℝ E E)).getD i 0)) := by
  rw [r26t8a_nest_apply p q hΦ X z u v, r26t8a_iteratedFDeriv_eq_iterDir (p + q) Φ hΦ,
    r26t8a_ofFn_getD _ (p + q) (by simp)]

end Dir

end HRS.MS.R26T8A
