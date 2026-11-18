import HRS.MC.CepN6Aux9

/-!
# Packet CEPN6 (aux 10): the parameters
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace HRS.MC.CepN6

theorem n6_params {N : ℕ} (hN : 0 < N) {Bd C κ ν σ5 T q ε₀ r : ℝ} (hBd : 0 ≤ Bd) (hC : 0 ≤ C)
    (hκ : 0 < κ) (hν : 0 < ν) (hσ5 : 0 < σ5) (hT : 0 < T) (hq : 0 < q) (hε₀ : 0 < ε₀) (hr : 0 < r) :
    ∃ η dur ε : ℝ, 0 < η ∧ 0 < dur ∧ 0 < ε ∧ dur ≤ T / 2 ∧
      r / 2 + 2 * (Bd * dur + 2 * ν * η + r / 16) < r ∧
      (κ / (r / 16) + C) * dur + 4 * ν * η < r / 16 ∧
      N * dur / η ^ 2 ≤ q / 4 ∧
      ε ≤ ε₀ ∧ ε ≤ 1 / 8 ∧ ε / 2 ≤ r / 16 ∧ C * ε ≤ κ ∧ ε ^ 2 / (σ5 ^ 2 * dur) ≤ q / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set η : ℝ := r / (128 * ν) with hη
  have hη0 : 0 < η := by positivity
  have hνη : ν * η = r / 128 := by
    rw [hη]; field_simp
  set L : ℝ := r / 16 with hL
  have hL0 : 0 < L := by positivity
  set K0 : ℝ := κ / L + C with hK0
  have hK00 : 0 ≤ K0 := by positivity
  set dur : ℝ := min (min (T / 2) (r / (16 * (Bd + 1)))) (min (L / (4 * (K0 + 1))) (q * η ^ 2 / (4 * N)))
    with hdur
  have hdur0 : 0 < dur := by
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hd1 : dur ≤ T / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : dur ≤ r / (16 * (Bd + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : dur ≤ L / (4 * (K0 + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hd4 : dur ≤ q * η ^ 2 / (4 * N) := (min_le_right _ _).trans (min_le_right _ _)
  have hBdd : Bd * dur ≤ r / 16 := by
    calc Bd * dur ≤ Bd * (r / (16 * (Bd + 1))) := mul_le_mul_of_nonneg_left hd2 hBd
      _ = (Bd / (Bd + 1)) * (r / 16) := by field_simp
      _ ≤ 1 * (r / 16) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one (by positivity)]; linarith
      _ = r / 16 := one_mul _
  have hKd : K0 * dur ≤ L / 4 := by
    calc K0 * dur ≤ K0 * (L / (4 * (K0 + 1))) := mul_le_mul_of_nonneg_left hd3 hK00
      _ = (K0 / (K0 + 1)) * (L / 4) := by field_simp
      _ ≤ 1 * (L / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one (by positivity)]; linarith
      _ = L / 4 := one_mul _
  set ε : ℝ := min ε₀ (min (1 / 8) (min (2 * L) (min (κ / (C + 1)) (q * σ5 ^ 2 * dur / 2)))) with hε
  have hε0 : 0 < ε := by
    refine lt_min hε₀ (lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity)
      (by positivity))))
  have he1 : ε ≤ ε₀ := min_le_left _ _
  have he2 : ε ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : ε ≤ 2 * L := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : ε ≤ κ / (C + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he5 : ε ≤ q * σ5 ^ 2 * dur / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨η, dur, ε, hη0, hdur0, hε0, hd1, ?_, ?_, ?_, he1, he2, ?_, ?_, ?_⟩
  · have : 2 * ν * η = r / 64 := by linarith
    nlinarith
  · have : 4 * ν * η = r / 32 := by linarith
    have h2 : K0 * dur ≤ r / 64 := by rw [hL] at hKd; linarith
    show K0 * dur + 4 * ν * η < r / 16
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have := hd4
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  · linarith
  · calc C * ε ≤ C * (κ / (C + 1)) := mul_le_mul_of_nonneg_left he4 hC
      _ = (C / (C + 1)) * κ := by field_simp
      _ ≤ 1 * κ := by
        apply mul_le_mul_of_nonneg_right _ hκ.le
        rw [div_le_one (by positivity)]; linarith
      _ = κ := one_mul _
  · have hsd : 0 < σ5 ^ 2 * dur := by positivity
    rw [div_le_iff₀ hsd]
    have h1 : ε ^ 2 ≤ ε := by nlinarith
    nlinarith

end HRS.MC.CepN6
