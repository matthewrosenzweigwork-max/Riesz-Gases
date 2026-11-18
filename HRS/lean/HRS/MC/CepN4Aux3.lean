import Mathlib
import HRS.MC.CepN4Aux2

/-!
# Packet CEPN4 (aux 3): bound of the explicit gap remainder on `r`-isolated configurations
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace HRS.MC.CepN4

open HRS Real

variable {N : ℕ}

lemma cepn4_h_bound {a : ℝ} (ha : 0 < a) {ρ : ℝ → ℝ} {Bρ r u : ℝ} (hBρ : ∀ u, |ρ u| ≤ Bρ)
    (hr : 0 < r) (h : ∀ m : ℤ, r ≤ |u - m|) :
    |cepn4_h a ρ u| ≤ a * (π / (2 * r) + Bρ) := by
  unfold cepn4_h
  rw [abs_mul, abs_of_pos ha]
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  calc |π * (Real.cos (π * u) / Real.sin (π * u)) - ρ u|
      ≤ |π * (Real.cos (π * u) / Real.sin (π * u))| + |ρ u| := abs_sub _ _
    _ ≤ π / (2 * r) + Bρ := add_le_add (cepn4_cot_bound hr h) (hBρ u)

lemma cepn4_E_eq (a : ℝ) (ρ : ℝ → ℝ) (hρ : ∀ u, ρ (-u) = -ρ u) (V : Torus 1 → ℝ)
    (y : Fin N → Euc 1) {i0 i1 : Fin N} (hne : i0 ≠ i1) (hN : 0 < N) :
    cepn4_E a ρ V y i0 i1 =
      (2 * a / N) * ((π * (Real.cos (π * (y i1 0 - y i0 0)) / Real.sin (π * (y i1 0 - y i0 0)))
          - 1 / (y i1 0 - y i0 0)) - ρ (y i1 0 - y i0 0))
      + (1 / (N : ℝ)) * ∑ j ∈ (Finset.univ.erase i1).erase i0,
          (cepn4_h a ρ (y i1 0 - y j 0) - cepn4_h a ρ (y i0 0 - y j 0))
      - (cepn4_gV V (y i1) - cepn4_gV V (y i0)) := by
  unfold cepn4_E cepn4_bdrift
  have h1 : ∑ j ∈ Finset.univ.erase i1, cepn4_h a ρ (y i1 0 - y j 0) =
      cepn4_h a ρ (y i1 0 - y i0 0) + ∑ j ∈ (Finset.univ.erase i1).erase i0, cepn4_h a ρ (y i1 0 - y j 0) :=
    (Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)).symm
  have h0 : ∑ j ∈ Finset.univ.erase i0, cepn4_h a ρ (y i0 0 - y j 0) =
      cepn4_h a ρ (y i0 0 - y i1 0) + ∑ j ∈ (Finset.univ.erase i0).erase i1, cepn4_h a ρ (y i0 0 - y j 0) :=
    (Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩)).symm
  rw [h1, h0, Finset.erase_right_comm, Finset.sum_sub_distrib]
  have hneg : cepn4_h a ρ (y i0 0 - y i1 0) = - cepn4_h a ρ (y i1 0 - y i0 0) := by
    rw [← cepn4_h_neg a ρ hρ]; congr 1; ring
  rw [hneg]
  unfold cepn4_h
  have hN' : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma cepn4_E_bound {a : ℝ} (ha : 0 < a) {ρ : ℝ → ℝ} (hρ : ∀ u, ρ (-u) = -ρ u) {Bρ BH BV : ℝ}
    (hBρ : ∀ u, |ρ u| ≤ Bρ) (hBρ0 : 0 ≤ Bρ)
    (hBH : ∀ u : ℝ, 0 < u → u < 1 / 4 → |π * (Real.cos (π * u) / Real.sin (π * u)) - 1 / u| ≤ BH)
    {V : Torus 1 → ℝ} (hBV : ∀ y, |cepn4_gV V y| ≤ BV) {r : ℝ} (hr : 0 < r) (hN : 0 < N)
    {y : Fin N → Euc 1} {i0 i1 : Fin N} (hne : i0 ≠ i1)
    (hiso : ∀ k : Fin N, k ≠ i0 → k ≠ i1 → ∀ m : ℤ,
      r ≤ |y k 0 - y i0 0 - m| ∧ r ≤ |y k 0 - y i1 0 - m|)
    (hG0 : 0 < y i1 0 - y i0 0) (hG1 : y i1 0 - y i0 0 < 1 / 4) :
    |cepn4_E a ρ V y i0 i1| ≤
      (2 * a / N) * (BH + Bρ) + 2 * a * (π / (2 * r) + Bρ) + 2 * BV := by
  rw [cepn4_E_eq a ρ hρ V y hne hN]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set M : ℝ := 2 * (a * (π / (2 * r) + Bρ)) with hM
  have hterm : ∀ j ∈ (Finset.univ.erase i1).erase i0,
      |cepn4_h a ρ (y i1 0 - y j 0) - cepn4_h a ρ (y i0 0 - y j 0)| ≤ M := by
    intro j hj
    obtain ⟨hj0, hj'⟩ := Finset.mem_erase.1 hj
    have hj1 := (Finset.mem_erase.1 hj').1
    have b1 := cepn4_h_bound ha hBρ hr (u := y i1 0 - y j 0) (fun m => by
      have := (hiso j hj0 hj1 (-m)).2
      calc r ≤ |y j 0 - y i1 0 - ((-m : ℤ) : ℝ)| := this
        _ = |y i1 0 - y j 0 - m| := by
          rw [← abs_neg]; congr 1; push_cast; ring)
    have b0 := cepn4_h_bound ha hBρ hr (u := y i0 0 - y j 0) (fun m => by
      have := (hiso j hj0 hj1 (-m)).1
      calc r ≤ |y j 0 - y i0 0 - ((-m : ℤ) : ℝ)| := this
        _ = |y i0 0 - y j 0 - m| := by
          rw [← abs_neg]; congr 1; push_cast; ring)
    calc _ ≤ |cepn4_h a ρ (y i1 0 - y j 0)| + |cepn4_h a ρ (y i0 0 - y j 0)| := abs_sub _ _
      _ ≤ M := by rw [hM]; linarith
  have hsum : |∑ j ∈ (Finset.univ.erase i1).erase i0,
      (cepn4_h a ρ (y i1 0 - y j 0) - cepn4_h a ρ (y i0 0 - y j 0))| ≤ N * M := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ M hterm) ?_
    rw [nsmul_eq_mul]
    have hM0 : 0 ≤ M := by rw [hM]; positivity
    have hcard : (((Finset.univ.erase i1).erase i0).card : ℝ) ≤ N := by
      have : ((Finset.univ.erase i1).erase i0).card ≤ N := by
        calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = N := by simp
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hcard hM0
  have hX : |(π * (Real.cos (π * (y i1 0 - y i0 0)) / Real.sin (π * (y i1 0 - y i0 0)))
          - 1 / (y i1 0 - y i0 0)) - ρ (y i1 0 - y i0 0)| ≤ BH + Bρ :=
    le_trans (abs_sub _ _) (add_le_add (hBH _ hG0 hG1) (hBρ _))
  have hg : |cepn4_gV V (y i1) - cepn4_gV V (y i0)| ≤ 2 * BV :=
    le_trans (abs_sub _ _) (by linarith [hBV (y i1), hBV (y i0)])
  have hc1 : |(2 * a / N) * ((π * (Real.cos (π * (y i1 0 - y i0 0)) / Real.sin (π * (y i1 0 - y i0 0)))
          - 1 / (y i1 0 - y i0 0)) - ρ (y i1 0 - y i0 0))| ≤ (2 * a / N) * (BH + Bρ) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have hc2 : |(1 / (N : ℝ)) * ∑ j ∈ (Finset.univ.erase i1).erase i0,
          (cepn4_h a ρ (y i1 0 - y j 0) - cepn4_h a ρ (y i0 0 - y j 0))| ≤ M := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (N * M) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = M := by field_simp
  calc _ ≤ |(2 * a / N) * ((π * (Real.cos (π * (y i1 0 - y i0 0)) / Real.sin (π * (y i1 0 - y i0 0)))
          - 1 / (y i1 0 - y i0 0)) - ρ (y i1 0 - y i0 0))
      + (1 / (N : ℝ)) * ∑ j ∈ (Finset.univ.erase i1).erase i0,
          (cepn4_h a ρ (y i1 0 - y j 0) - cepn4_h a ρ (y i0 0 - y j 0))| +
        |cepn4_gV V (y i1) - cepn4_gV V (y i0)| := abs_sub _ _
    _ ≤ _ := by
      have := abs_add_le ((2 * a / N) * ((π * (Real.cos (π * (y i1 0 - y i0 0)) / Real.sin (π * (y i1 0 - y i0 0)))
          - 1 / (y i1 0 - y i0 0)) - ρ (y i1 0 - y i0 0)))
        ((1 / (N : ℝ)) * ∑ j ∈ (Finset.univ.erase i1).erase i0,
          (cepn4_h a ρ (y i1 0 - y j 0) - cepn4_h a ρ (y i0 0 - y j 0)))
      rw [hM] at hc2
      linarith
