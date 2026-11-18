import HRS.MC.CepE5bAux5

/-!
# Packet CEPE5B, auxiliary 6: the pointwise trace bound by the Lyapunov functional

`(1/n) tr D²Φ_n(z) ≤ (8N³ r/(aπ)) Q_n(z) + 16 N⁵ r + 2aπ² N/(n r²)` for `r ∈ (0, 1/2]`, `Q_n(z) = ⟨z - ρ, G_n z⟩`.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE1 (cepe1_h1 cepe1_pairGrad cepe1_vec cepe1_inner_vec)
open HRS.MC.CepE4 (e4_rho)

variable {N : ℕ} {a : ℝ} {J : ℝ → Ch N → Ch N}

/-- The Lyapunov functional along the Yosida force. -/
def e5b_Q (J : ℝ → Ch N → Ch N) (n : ℝ) (z : Ch N) : ℝ := inner ℝ (z - e4_rho N) (n • (z - J n z))

theorem e5b_T_le (ha : 0 < a) {y : Ch N} (hy : y ∈ cep_Alcove N) {n r : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hr2 : r ≤ 1 / 2) :
    e5b_T a N n y ≤ (2 * (N : ℝ) ^ 2 * r / (a * Real.pi)) * e5b_W a N y +
      2 * a * Real.pi ^ 2 * N / (n * r ^ 2) := by
  have hpi := Real.pi_pos
  by_cases hN : N = 0
  · subst hN
    simp [e5b_T, e5b_W]
  have hNp : 0 < N := Nat.pos_of_ne_zero hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  set A : ℝ := N * (2 * N * r / (a * Real.pi)) with hA
  set B : ℝ := 2 * a * Real.pi ^ 2 / (N * n * r ^ 2) with hB
  have hterm : ∀ k l : Fin N, (if k < l then min (N : ℝ) (2 / n * e5b_h1' a N (y l - y k)) else 0) ≤
      (if k < l then A * |cepe1_h1 a N (y l - y k)| else 0) + (if k < l then B else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      exact e5b_pair_min ha hNp hn hr hr2 (e5b_gap hy hkl)
    · simp [hkl]
  have h1 : e5b_T a N n y ≤ A * e5b_W a N y + B * (N : ℝ) ^ 2 := by
    calc e5b_T a N n y ≤ ∑ k : Fin N, ∑ l : Fin N,
          ((if k < l then A * |cepe1_h1 a N (y l - y k)| else 0) + (if k < l then B else 0)) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
      _ = A * e5b_W a N y + ∑ k : Fin N, ∑ l : Fin N, (if k < l then B else 0) := by
          simp only [Finset.sum_add_distrib]
          congr 1
          unfold e5b_W
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          split_ifs <;> ring
      _ ≤ A * e5b_W a N y + B * (N : ℝ) ^ 2 := by
          have hBn : 0 ≤ B := by positivity
          have : ∑ k : Fin N, ∑ l : Fin N, (if k < l then B else 0) ≤ ∑ _k : Fin N, ∑ _l : Fin N, B :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by split_ifs <;> simp [hBn]
          have e : ∑ _k : Fin N, ∑ _l : Fin N, B = B * (N : ℝ) ^ 2 := by simp; ring
          linarith
  have e1 : A = N * (2 * N * r / (a * Real.pi)) := rfl
  have e2 : A * e5b_W a N y = (2 * (N : ℝ) ^ 2 * r / (a * Real.pi)) * e5b_W a N y := by
    rw [e1]; congr 1; field_simp
  have e3 : B * (N : ℝ) ^ 2 = 2 * a * Real.pi ^ 2 * N / (n * r ^ 2) := by
    rw [hB]; field_simp
  linarith

theorem e5b_Q_ge (ha : 0 < a) (hJ : cep_Yosida a N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    inner ℝ (J n z - e4_rho N) (e5b_pg a N (J n z)) ≤ e5b_Q J n z := by
  have hf := e5b_force hJ hn z
  unfold e5b_Q
  rw [hf]
  have hz : z - e4_rho N = (J n z - e4_rho N) + n⁻¹ • e5b_pg a N (J n z) := by
    rw [← hf, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
    abel
  rw [hz, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have : 0 ≤ n⁻¹ * ‖e5b_pg a N (J n z)‖ ^ 2 := by positivity
  linarith

theorem e5b_trace_final (ha : 0 < a) (hJ : cep_Yosida a N J) {n r : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hr2 : r ≤ 1 / 2) (z : Ch N) :
    (1 / n) * ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i) ≤
      (8 * (N : ℝ) ^ 3 * r / (a * Real.pi)) * e5b_Q J n z + 16 * (N : ℝ) ^ 5 * r +
        2 * a * Real.pi ^ 2 * N / (n * r ^ 2) := by
  have hpi := Real.pi_pos
  have hy := hJ.mem n z hn
  have h1 := e5b_trace_le ha hJ hn z
  have h2 := e5b_T_le ha hy hn hr hr2
  have h3 := e5b_W_le ha hy
  have h4 := e5b_Q_ge ha hJ hn z
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hc : 0 ≤ 2 * (N : ℝ) ^ 2 * r / (a * Real.pi) := by positivity
  have h5 : (1 / n) * ∑ i : Fin N, fderiv ℝ (fderiv ℝ (e5b_Pn a N J n)) z (e5b_e i) (e5b_e i) ≤
      e5b_T a N n (J n z) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn]
    linarith
  have h6 : e5b_W a N (J n z) ≤ 4 * N * e5b_Q J n z + 8 * Real.pi * N * a * (N : ℝ) ^ 2 := by
    have : 4 * (N : ℝ) * inner ℝ (J n z - e4_rho N) (e5b_pg a N (J n z)) ≤ 4 * N * e5b_Q J n z :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith
  have h7 := mul_le_mul_of_nonneg_left h6 hc
  have e1 : (2 * (N : ℝ) ^ 2 * r / (a * Real.pi)) * (4 * N * e5b_Q J n z + 8 * Real.pi * N * a * (N : ℝ) ^ 2) =
      (8 * (N : ℝ) ^ 3 * r / (a * Real.pi)) * e5b_Q J n z + 16 * (N : ℝ) ^ 5 * r := by
    field_simp
    ring
  linarith

end HRS.MC.CepE5b
