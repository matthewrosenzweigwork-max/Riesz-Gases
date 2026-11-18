import HRS.Sections.QuenchAux25

/-!
# Packet QUENCH (Q27), part 26: the spectral gap `λ_* > 0` (attained, `ℐ_*` finite) and test forms
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

section Gap

variable {s β : ℝ}

lemma finite_lattice_ball (R : ℝ) : {x : Lattice d | Lattice.enorm x ≤ R}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-⌈R⌉) ⌈R⌉) fun _ => Set.finite_Icc _ _).subset ?_
  intro x hx i _
  have h1 : |(x i : ℝ)| ≤ Lattice.enorm x := by
    have := PiLp.norm_apply_le (Lattice.toEuc x) i
    simpa [Lattice.toEuc, Lattice.enorm] using this
  have h2 : |(x i : ℝ)| ≤ R := h1.trans hx
  have h3 : (x i : ℝ) ≤ ⌈R⌉ := (le_abs_self _).trans (h2.trans (Int.le_ceil R))
  have h4 : -(x i : ℝ) ≤ ⌈R⌉ := (neg_le_abs _).trans (h2.trans (Int.le_ceil R))
  constructor
  · have : (-(⌈R⌉ : ℤ) : ℝ) ≤ x i := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast h3

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
lemma lamMode_ge_enorm (k : NonzeroLattice d) :
    (2 * Real.pi * Lattice.enorm k.1) ^ 2 / β ≤ lamMode d s β k.1 := by
  have h2 := rieszCoeff_pos hd hs0 hsd k
  unfold lamMode
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

include hd hs0 hsd hβ in
lemma finite_sublevel (c : ℝ) : {k : PosHalf d | lamMode d s β k.1 ≤ c}.Finite := by
  have hfin := finite_lattice_ball (d := d) (1 + β * c / (4 * Real.pi ^ 2))
  refine (hfin.preimage (Subtype.val_injective.injOn)).subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  show Lattice.enorm k.1 ≤ _
  have h1 := lamMode_ge_enorm hd hs0 hsd hβ ⟨k.1, ne_zero_of_posHalf k.2⟩
  have h2 : (2 * Real.pi * Lattice.enorm k.1) ^ 2 ≤ β * c := by
    have := h1.trans hk
    rwa [div_le_iff₀ hβ, mul_comm c] at this
  have hpi := Real.pi_pos
  have h3 : Lattice.enorm k.1 ^ 2 ≤ β * c / (4 * Real.pi ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h0 : 0 ≤ Lattice.enorm k.1 := norm_nonneg _
  nlinarith [sq_nonneg (Lattice.enorm k.1 - 1), sq_nonneg (Lattice.enorm k.1), h3]

lemma nonempty_posHalf (hd : 2 ≤ d) : Nonempty (PosHalf d) := by
  have : NeZero d := ⟨by omega⟩
  let j : NonzeroLattice d := ⟨Pi.single 0 1, fun h => by
    have := congrFun h 0
    simp at this⟩
  exact ⟨((equiv d).symm j).1⟩

include hd hs0 hsd hβ in
lemma exists_min_lam : ∃ k0 : PosHalf d, ∀ k : PosHalf d, lamMode d s β k0.1 ≤ lamMode d s β k.1 := by
  obtain ⟨k1⟩ := nonempty_posHalf hd
  have hfin := finite_sublevel hd hs0 hsd hβ (lamMode d s β k1.1)
  obtain ⟨k0, hk0, hmin⟩ := Set.exists_min_image {k : PosHalf d | lamMode d s β k.1 ≤ lamMode d s β k1.1} (fun k : PosHalf d => lamMode d s β k.1) hfin
    ⟨k1, show lamMode d s β k1.1 ≤ lamMode d s β k1.1 from le_rfl⟩
  refine ⟨k0, fun k => ?_⟩
  by_cases hk : lamMode d s β k.1 ≤ lamMode d s β k1.1
  · exact hmin k hk
  · exact hk0.trans (le_of_lt (not_le.1 hk))

include hd hs0 hsd hβ in
lemma lamStar_eq (k0 : PosHalf d) (h : ∀ k : PosHalf d, lamMode d s β k0.1 ≤ lamMode d s β k.1) :
    lamStar d s β = lamMode d s β k0.1 := by
  unfold lamStar
  haveI : Nonempty (PosHalf d) := ⟨k0⟩
  refine le_antisymm (ciInf_le ⟨lamMode d s β k0.1, ?_⟩ k0) (le_ciInf fun k => h k)
  rintro _ ⟨k, rfl⟩
  exact h k

include hd hs0 hsd hβ in
lemma lamMode_pos' (k : PosHalf d) : 0 < lamMode d s β k.1 :=
  lamMode_pos hd hs0 hsd hβ ⟨k.1, ne_zero_of_posHalf k.2⟩

include hd hs0 hsd hβ in
theorem gap_facts : 0 < lamStar d s β ∧ {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Finite ∧
      {k : PosHalf d | lamMode d s β k.1 = lamStar d s β}.Nonempty := by
  obtain ⟨k0, hk0⟩ := exists_min_lam hd hs0 hsd hβ
  have he := lamStar_eq hd hs0 hsd hβ k0 hk0
  refine ⟨he ▸ lamMode_pos' hd hs0 hsd hβ k0, ?_, ⟨k0, he.symm⟩⟩
  exact (finite_sublevel hd hs0 hsd hβ (lamMode d s β k0.1)).subset fun k hk => by
    simp only [Set.mem_setOf_eq] at hk ⊢
    rw [hk, he]

end Gap

end Qch

end HRS
