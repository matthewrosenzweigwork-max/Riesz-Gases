import HRS.Main.A9Aux20

/-!
# Packet A9, part 21: Proposition A.9, the comparison statement and the moment bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

/-- finite sets of modes with small tail. -/
theorem a9_exists_finite_tail (Λ₁ t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℕ) (k : Fin q → NonzeroLattice d), Function.Injective k ∧ a9tail d Λ₁ t k ≤ ε := by
  classical
  have h := tendsto_tsum_compl_atTop_zero (a9K d Λ₁ t)
  obtain ⟨s, hs⟩ := ((tendsto_order.1 h).2 ε hε).exists
  refine ⟨s.card, fun a => ((s.equivFin.symm a : {x // x ∈ s}) : NonzeroLattice d), ?_, ?_⟩
  · intro a b hab
    have := Subtype.ext hab
    exact s.equivFin.symm.injective this
  · have hrange : Set.range (fun a : Fin s.card => ((s.equivFin.symm a : {x // x ∈ s}) : NonzeroLattice d))
        = (s : Set (NonzeroLattice d)) := by
      ext j
      constructor
      · rintro ⟨a, rfl⟩; exact (s.equivFin.symm a).2
      · intro hj
        exact ⟨s.equivFin ⟨j, hj⟩, by simp⟩
    unfold a9tail
    have e : (∑' j, if j ∈ Set.range (fun a : Fin s.card =>
          ((s.equivFin.symm a : {x // x ∈ s}) : NonzeroLattice d)) then (0 : ℝ) else a9K d Λ₁ t j) =
        ∑' a : {x // x ∉ s}, a9K d Λ₁ t a := by
      rw [show (∑' a : {x // x ∉ s}, a9K d Λ₁ t a) =
        ∑' a : ↥({x | x ∉ s} : Set (NonzeroLattice d)), a9K d Λ₁ t a from rfl,
        tsum_subtype ({x | x ∉ s} : Set (NonzeroLattice d)) (a9K d Λ₁ t)]
      refine tsum_congr fun j => ?_
      by_cases hj : j ∈ s
      · rw [if_pos (by rw [hrange]; exact hj)]
        simp [hj]
      · rw [if_neg (by rw [hrange]; exact hj)]
        simp [hj, Set.indicator]
    rw [e]
    exact hs.le

theorem a9K_tsum_le (Λ₁ : ℝ) {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∑' j, a9K d Λ₁ t j ≤
      Real.exp (|Λ₁| * T) * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := by
  have e : ∀ j : NonzeroLattice d, a9K d Λ₁ t j =
      Real.exp (|Λ₁| * t) * Lattice.jp j.1 ^ (-((d : ℝ) + 3)) := by
    intro j; unfold a9K a8pK; rw [a9phi_sobolevNorm_mStar]
  simp_rw [e]
  rw [tsum_mul_left]
  have hZ0 : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 3)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _))) hZ0

end HRS.Main.A9
