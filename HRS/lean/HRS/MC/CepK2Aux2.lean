import HRS.Stochastic.SelectedFlow
import HRS.MC.CepK2Aux1

/-!
# Packet K2 (aux 2): coordinates of the lifted drift, gaps of ordered configurations
-/

open Real

noncomputable section

namespace HRS.MC.CepK2

open HRS

lemma cepk2_mk_sub (y z : Euc 1) : Torus.mk (y - z) = Torus.mk y - Torus.mk z := by
  funext i
  simp [Torus.mk]

/-- Integer differences give torus-equal points. -/
lemma cepk2_mk_eq_of_int {y z : Euc 1} {n : ℤ} (h : y 0 - z 0 = n) : Torus.mk y = Torus.mk z := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  simp only [Torus.mk]
  have h2 : (((y 0 - z 0 : ℝ)) : UnitAddCircle) = 0 := by
    rw [(AddCircle.coe_eq_zero_iff (1 : ℝ))]
    exact ⟨n, by simp [h]⟩
  rw [AddCircle.coe_sub] at h2
  exact sub_eq_zero.mp h2

lemma cepk2_free {N : ℕ} {y : Fin N → Euc 1}
    (hfree : (fun i => Torus.mk (y i)) ∉ collisionSet 1 N) :
    ∀ i j, i ≠ j → ∀ n : ℤ, y i 0 - y j 0 ≠ n := by
  intro i j hij n hn
  exact hfree ⟨i, j, hij, cepk2_mk_eq_of_int hn⟩

/-- Gaps of a cyclically ordered, collision-free configuration. -/
lemma cepk2_gap {N : ℕ} {σ : Equiv.Perm (Fin N)} {y : Fin N → Euc 1}
    (hord : CyclicallyOrdered σ y)
    (hfree : (fun i => Torus.mk (y i)) ∉ collisionSet 1 N) {i j : Fin N} (hij : i ≠ j) :
    (σ.symm i < σ.symm j → 0 < y j 0 - y i 0 ∧ y j 0 - y i 0 < 1) := by
  intro hlt
  have h0 := hord 0
  have hle := h0.1 (σ.symm i) (σ.symm j) hlt.le
  have hb := h0.2 (σ.symm i) (σ.symm j)
  simp only [Equiv.apply_symm_apply] at hle hb
  have hf := cepk2_free hfree j i (Ne.symm hij)
  refine ⟨?_, ?_⟩
  · rcases hle.lt_or_eq with h | h
    · linarith
    · exact absurd (by simp [h] : y j 0 - y i 0 = ((0 : ℤ) : ℝ)) (hf 0)
  · rcases hb.lt_or_eq with h | h
    · linarith
    · exact absurd (by rw [h]; simp : y j 0 - y i 0 = ((1 : ℤ) : ℝ)) (hf 1)

/-- Pair configuration: for `i ≠ j` both differences lie in the same unit interval. -/
lemma cepk2_pair_case {N : ℕ} {σ : Equiv.Perm (Fin N)} {y y' : Fin N → Euc 1}
    (hord : CyclicallyOrdered σ y) (hord' : CyclicallyOrdered σ y')
    (hfree : (fun i => Torus.mk (y i)) ∉ collisionSet 1 N)
    (hfree' : (fun i => Torus.mk (y' i)) ∉ collisionSet 1 N) {i j : Fin N} (hij : i ≠ j) :
    (0 < y i 0 - y j 0 ∧ y i 0 - y j 0 < 1 ∧ 0 < y' i 0 - y' j 0 ∧ y' i 0 - y' j 0 < 1) ∨
    (-1 < y i 0 - y j 0 ∧ y i 0 - y j 0 < 0 ∧ -1 < y' i 0 - y' j 0 ∧ y' i 0 - y' j 0 < 0) := by
  rcases lt_trichotomy (σ.symm i) (σ.symm j) with h | h | h
  · right
    have a := cepk2_gap hord hfree hij h
    have b := cepk2_gap hord' hfree' hij h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [a.1, a.2, b.1, b.2]
  · exact absurd (σ.symm.injective h) hij
  · left
    have a := cepk2_gap hord hfree hij.symm h
    have b := cepk2_gap hord' hfree' hij.symm h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [a.1, a.2, b.1, b.2]

/-- The gradient of the lift is `ℤ`-periodic, so `Torus.grad` is the gradient of the lift at any lift. -/
lemma cepk2_grad_eq (V : Torus 1 → ℝ) (y : Euc 1) :
    Torus.grad V (Torus.mk y) = gradient (Torus.lift V) y := by
  have hmk : Torus.mk (Torus.rep (Torus.mk y)) = Torus.mk y := Torus.mk_rep _
  have hex : ∃ m : Lattice 1, Torus.rep (Torus.mk y) = y + Lattice.toEuc m := by
    have : ∀ i, ∃ n : ℤ, (n : ℝ) = Torus.rep (Torus.mk y) i - y i := by
      intro i
      have hi := congrFun hmk i
      simp only [Torus.mk] at hi
      have h2 : ((Torus.rep (Torus.mk y) i - y i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, hi, sub_self]
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h2
      exact ⟨n, by simpa using hn⟩
    choose m hm using this
    refine ⟨m, ?_⟩
    ext i
    simp [Lattice.toEuc, hm]
  obtain ⟨m, hm⟩ := hex
  unfold Torus.grad
  rw [hm]
  have hper : (fun z => Torus.lift V (z + Lattice.toEuc m)) = Torus.lift V :=
    funext fun z => Torus.lift_periodic V z m
  unfold gradient
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := Torus.lift V) (x := y) (Lattice.toEuc m)
  rw [hper] at this
  rw [← this]

end HRS.MC.CepK2
