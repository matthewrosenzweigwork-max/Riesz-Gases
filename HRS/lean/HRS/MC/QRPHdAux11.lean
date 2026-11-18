import HRS.MC.QRPHdAux1

/-!
# Packet HD, part 11: summing a band-supported function over pairs of nonzero frequencies
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ}

open Classical in
theorem hd_pair_sum (φ : Lattice d → Lattice d) (w : Lattice d → ℝ) (hw : ∀ c, 0 ≤ w c)
    (Q : Lattice d → Prop) (F : Finset (NonzeroLattice d)) (hF : ∀ a : NonzeroLattice d, Q a.1 → a ∈ F)
    (hW : Summable (fun a : NonzeroLattice d => if Q a.1 ∧ Q (φ a.1) then (0 : ℝ) else w a.1)) :
    Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
      if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else if p.2.1 = φ p.1.1 then w p.1.1 else 0) ∧
    ∑' p : NonzeroLattice d × NonzeroLattice d,
      (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else if p.2.1 = φ p.1.1 then w p.1.1 else 0) ≤
      ∑' a : NonzeroLattice d, (if Q a.1 ∧ Q (φ a.1) then (0 : ℝ) else w a.1) := by
  set W : NonzeroLattice d → ℝ := fun a => if Q a.1 ∧ Q (φ a.1) then (0 : ℝ) else w a.1 with hWdef
  have hW0 : ∀ a, 0 ≤ W a := by
    intro a; simp only [hWdef]; split_ifs
    · exact le_rfl
    · exact hw _
  set H' : NonzeroLattice d × NonzeroLattice d → ℝ :=
    fun p => if p.2.1 = φ p.1.1 then W p.1 else 0 with hH'
  have hH'nn : 0 ≤ H' := by
    intro p; simp only [hH', Pi.zero_apply]; split_ifs
    · exact hW0 _
    · exact le_rfl
  have hfin : ∀ a : NonzeroLattice d, Summable (fun b : NonzeroLattice d => H' (a, b)) := by
    intro a
    refine summable_of_finite_support (Set.Finite.subset (s := {b : NonzeroLattice d | b.1 = φ a.1}) ?_ ?_)
    · refine Set.Subsingleton.finite ?_
      intro x hx y hy
      exact Subtype.ext (hx.trans hy.symm)
    · intro b hb
      by_contra hne
      apply hb
      simp only [hH']
      exact if_neg hne
  have htsum : ∀ a : NonzeroLattice d, ∑' b : NonzeroLattice d, H' (a, b) ≤ W a := by
    intro a
    by_cases hex : ∃ b0 : NonzeroLattice d, b0.1 = φ a.1
    · obtain ⟨b0, hb0⟩ := hex
      rw [tsum_eq_single b0]
      · simp only [hH', hb0, if_true]; exact le_rfl
      · intro b hb
        simp only [hH']
        rw [if_neg]
        intro h
        exact hb (Subtype.ext (h.trans hb0.symm))
    · push Not at hex
      have : ∀ b : NonzeroLattice d, H' (a, b) = 0 := by
        intro b; simp only [hH']; rw [if_neg (hex b)]
      simp only [this, tsum_zero]
      exact hW0 a
  have hsumo : Summable (fun a : NonzeroLattice d => ∑' b : NonzeroLattice d, H' (a, b)) :=
    Summable.of_nonneg_of_le (fun a => tsum_nonneg fun b => hH'nn (a, b)) htsum hW
  have hH'sum : Summable H' := (summable_prod_of_nonneg hH'nn).mpr ⟨hfin, hsumo⟩
  have hpt : ∀ p : NonzeroLattice d × NonzeroLattice d,
      (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else if p.2.1 = φ p.1.1 then w p.1.1 else 0) ≤ H' p := by
    intro p
    by_cases hb : p.2.1 = φ p.1.1
    · by_cases hFF : p.1 ∈ F ∧ p.2 ∈ F
      · simp only [hFF, and_self, if_true, hH', hb]; exact hW0 _
      · simp only [hFF, if_false, hb, if_true, hH', hWdef]
        have : ¬ (Q p.1.1 ∧ Q (φ p.1.1)) := by
          rintro ⟨h1, h2⟩
          apply hFF
          exact ⟨hF _ h1, hF _ (hb ▸ h2)⟩
        rw [if_neg this]
    · simp only [hb, if_false, hH']
      split_ifs <;> exact le_rfl
  have hnn : ∀ p : NonzeroLattice d × NonzeroLattice d,
      0 ≤ (if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else if p.2.1 = φ p.1.1 then w p.1.1 else 0) := by
    intro p; split_ifs
    · exact le_rfl
    · exact hw _
    · exact le_rfl
  have hs : Summable (fun p : NonzeroLattice d × NonzeroLattice d =>
      if p.1 ∈ F ∧ p.2 ∈ F then (0 : ℝ) else if p.2.1 = φ p.1.1 then w p.1.1 else 0) :=
    Summable.of_nonneg_of_le hnn hpt hH'sum
  refine ⟨hs, ?_⟩
  calc _ ≤ ∑' p, H' p := Summable.tsum_le_tsum hpt hs hH'sum
    _ = ∑' a, ∑' b, H' (a, b) := hH'sum.tsum_prod' hfin
    _ ≤ ∑' a, W a := Summable.tsum_le_tsum htsum hsumo hW

end HRS.MC.QRSpec.Hd

end
