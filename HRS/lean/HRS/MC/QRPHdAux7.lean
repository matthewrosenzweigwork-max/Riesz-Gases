import HRS.MC.QRPHdAux6

/-!
# Packet HD, part 7: the two lattice-sum bounds for `D(α,λ)²`
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ} {s : ℝ}

theorem hdS1_nonneg (lam : Lattice d) (L : ℕ) (α : Lattice d) : 0 ≤ hdS1 d s lam L α := by
  unfold hdS1
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

open Classical in
theorem hd_tailA (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : 2 * s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : Lattice d, lam ≠ 0 → ∀ L : ℕ, 1 ≤ L → 2 * Lattice.enorm lam ≤ L →
      Summable (hdS1 d s lam L) ∧
      ∑' α, hdS1 d s lam L α ≤ C * Lattice.enorm lam ^ 2 * (L : ℝ) ^ (-((d : ℝ) - 2 * s)) := by
  have hp : 0 < (d : ℝ) - 2 * s := by linarith
  obtain ⟨At, hAt0, hAt⟩ := hd_tail_tsum (d := d) (by omega) hp
  set C1 := |hdκ d s| * (1 + 3 * |s - (d : ℝ)|) * 2 ^ ((d : ℝ) - s) with hC1
  refine ⟨C1 ^ 2 * At, by positivity, fun lam hlam L hL h2 => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hsum, htsum⟩ := hAt (L : ℝ) hL1
  set T : Lattice d → ℝ := fun k => if (L : ℝ) ≤ Lattice.enorm k then
    Lattice.enorm k ^ (-(d : ℝ) - ((d : ℝ) - 2 * s)) else 0 with hT
  have hTnn : ∀ α, 0 ≤ T α := by
    intro α; simp only [hT]
    split_ifs
    · exact Real.rpow_nonneg (hd_enorm_nonneg α) _
    · exact le_rfl
  have hpt : ∀ α, hdS1 d s lam L α ≤ (C1 ^ 2 * Lattice.enorm lam ^ 2) * T α := by
    intro α
    by_cases hc : ∀ i, |α i| ≤ (L : ℤ)
    · have : hdS1 d s lam L α = 0 := by simp [hdS1, hc]
      rw [this]
      exact mul_nonneg (by positivity) (hTnn α)
    · have hge := hd_enorm_ge_of_out hc
      have hα : α ≠ 0 := by
        rintro rfl
        have : Lattice.enorm (0 : Lattice d) = 0 := by
          rw [hd_enorm_def, hd_toEuc_zero, norm_zero]
        linarith
      have h2' : 2 * Lattice.enorm lam ≤ Lattice.enorm α := h2.trans hge
      have hsd' : s < d := by linarith
      have := hdD_sq_far hsd' hα h2'
      have e1 : hdS1 d s lam L α = hdD d s lam α ^ 2 := by simp [hdS1, hc]
      rw [e1]
      simp only [hT, if_pos hge]
      calc hdD d s lam α ^ 2 ≤ _ := this
        _ = _ := by ring
  have hM : Summable (fun α => (C1 ^ 2 * Lattice.enorm lam ^ 2) * T α) := hsum.mul_left _
  refine ⟨Summable.of_nonneg_of_le (hdS1_nonneg lam L) hpt hM, ?_⟩
  calc ∑' α, hdS1 d s lam L α ≤ ∑' α, (C1 ^ 2 * Lattice.enorm lam ^ 2) * T α :=
        Summable.tsum_le_tsum hpt (Summable.of_nonneg_of_le (hdS1_nonneg lam L) hpt hM) hM
    _ = (C1 ^ 2 * Lattice.enorm lam ^ 2) * ∑' α, T α := tsum_mul_left
    _ ≤ (C1 ^ 2 * Lattice.enorm lam ^ 2) * (At * (L : ℝ) ^ (-((d : ℝ) - 2 * s))) :=
        mul_le_mul_of_nonneg_left htsum (by positivity)
    _ = _ := by ring

end HRS.MC.QRSpec.Hd

end
