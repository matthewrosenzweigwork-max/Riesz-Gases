import HRS.Energy.Commutator.RenormCoul

/-!
# Route S, packet S4: radii and bookkeeping
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

theorem nnDist_le {N : ℕ} (X : Config d N) {i j : Fin N} (hij : j ≠ i) :
    nnDist X i ≤ KernelGrad.tdist (X i) (X j) := by
  unfold nnDist
  exact ciInf_le (f := fun k : {k : Fin N // k ≠ i} => KernelGrad.tdist (X i) (X k))
    ⟨0, by rintro _ ⟨k, rfl⟩; exact KernelGrad.tdist_nonneg _ _⟩ ⟨j, hij⟩

theorem nnDist_pos {N : ℕ} (hN : 2 ≤ N) (X : Config d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) (i : Fin N) :
    0 < nnDist X i := by
  have hne : Nonempty {j : Fin N // j ≠ i} := by
    by_cases h : i.val = 0
    · exact ⟨⟨⟨1, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩⟩
    · exact ⟨⟨⟨0, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := fun k : {k : Fin N // k ≠ i} => KernelGrad.tdist (X i) (X k))
  unfold nnDist
  rw [← hj]
  refine KernelGrad.tdist_pos (z := X i - X j.1) ?_ |>.trans_eq ?_
  · exact sub_ne_zero.mpr (hX i j.1 (Ne.symm j.2))
  · unfold KernelGrad.tdist; simp

theorem radii_facts {N : ℕ} (hd : 1 ≤ d) (hN : 2 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) (X : Config d N)
    (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    (∀ i, 0 < smearRadius Λ X i) ∧ (∀ i, smearRadius Λ X i ≤ smearScale d N Λ / 8) ∧
    (∀ i, smearRadius Λ X i ≤ 1 / 8) ∧
    (∀ i j, i ≠ j → smearRadius Λ X i + smearRadius Λ X j < KernelGrad.tdist (X i) (X j)) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hΛ0 : 0 < Λ := by linarith
  have hlam0 : 0 < smearScale d N Λ := CoercAux.smearScale_pos (by omega) hΛ0
  have hlam1 : smearScale d N Λ < 1 := CoercAux.smearScale_lt_one hd (by nlinarith)
  have hth : thetaStar = 1 / 8 := rfl
  have hrle : ∀ i, smearRadius Λ X i ≤ nnDist X i / 4 := fun i => min_le_left _ _
  have hrle2 : ∀ i, smearRadius Λ X i ≤ smearScale d N Λ / 8 := fun i => by
    have : smearRadius Λ X i ≤ thetaStar * smearScale d N Λ := min_le_right _ _
    rw [hth] at this; linarith
  have hpos : ∀ i, 0 < smearRadius Λ X i := fun i =>
    lt_min (by have := nnDist_pos hN X hX i; positivity) (by rw [hth]; positivity)
  refine ⟨hpos, hrle2, fun i => by have := hrle2 i; linarith, fun i j hij => ?_⟩
  have h1 := nnDist_le X (i := i) (j := j) (Ne.symm hij)
  have h2 := nnDist_le X (i := j) (j := i) hij
  rw [tdist_symm' (X j) (X i)] at h2
  have h3 := hrle i
  have h4 := hrle j
  have h5 : 0 < KernelGrad.tdist (X i) (X j) := by
    have := nnDist_pos hN X hX i
    linarith
  linarith

end HRS.Commutator.Renorm
