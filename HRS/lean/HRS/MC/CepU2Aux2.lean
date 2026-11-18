import HRS.MC.CepU2Aux1

/-!
# Packet CEPU2 (aux 2): torus helpers, strictness of an ordered contact-free lift, lift transfer
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepU2

open HRS

theorem cepu2_mk_sub {d : ℕ} (x y : Euc d) : Torus.mk (x - y) = Torus.mk x - Torus.mk y := by
  funext i
  simp [Torus.mk, AddCircle.coe_sub]

theorem cepu2_isLattice_neg {N : ℕ} {w : Fin N → Euc 1} (hw : IsLatticeVec w) : IsLatticeVec (-w) := by
  intro i
  obtain ⟨n, hn⟩ := hw i
  refine ⟨-n, ?_⟩
  rw [Pi.neg_apply, hn]
  ext j
  simp [Lattice.toEuc]

theorem cepu2_mk_sub_lattice {N : ℕ} {w : Fin N → Euc 1} (hw : IsLatticeVec w) (Y : Fin N → Euc 1) :
    (fun j => Torus.mk ((Y - w) j)) = fun j => Torus.mk (Y j) := by
  rw [sub_eq_add_neg]
  exact mk_add_lattice_vec (cepu2_isLattice_neg hw) Y

/-- A cyclically ordered lift with no contact is strictly ordered. -/
theorem cepu2_strict {N : ℕ} {π : Equiv.Perm (Fin N)} {y : Fin N → Euc 1}
    (h : CyclicallyOrdered π y) (hfree : (fun i => Torus.mk (y i)) ∉ collisionSet 1 N) :
    HRS.MC.CepK0.cep_StrictlyOrdered π y := by
  obtain ⟨h1, h2⟩ := h 0
  have hmk : ∀ a b : Fin N, y a 0 = y b 0 → Torus.mk (y a) = Torus.mk (y b) := by
    intro a b hab
    have : y a = y b := by
      ext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact hab
    rw [this]
  refine ⟨fun k k' hkk' => lt_of_le_of_ne (h1 k k' hkk'.le) fun heq => hfree ?_,
    fun k k' => lt_of_le_of_ne (h2 k k') fun heq => ?_⟩
  · exact ⟨π k, π k', fun e => hkk'.ne (π.injective e), hmk _ _ heq⟩
  · by_cases hkk : k = k'
    · subst hkk; linarith
    · apply hfree
      refine ⟨π k', π k, fun e => hkk (π.injective e).symm, ?_⟩
      funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp only [Torus.mk]
      rw [heq]
      simp [AddCircle.coe_add]

end HRS.MC.CepU2
