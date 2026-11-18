import HRS.MC.CepE6aA4

/-!
# Packet CEPE6A, file 6: inverse circle distances are controlled by `‖∇Φ‖₁`

For `z` in the open alcove, `∑_{k<l} 1 / min(d_{kl}, 1 - d_{kl}) ≤ c₁ ‖∇Φ(z)‖₁ + c₂` (`d_{kl} = z_l - z_k`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa HRS.MC.CepE4 HRS.MC.CepE6

variable {N : ℕ}

theorem e6a_inv_half {d : ℝ} (h0 : 0 < d) (h1 : d ≤ 1 / 2) :
    1 / d ≤ 2 * |Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d))| + 4 := by
  by_cases hd : d ≤ 1 / 4
  · have hcos := e4_cos_ge_half h0.le hd
    have hsin_pos : 0 < Real.sin (Real.pi * d) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    have hsin_le : Real.sin (Real.pi * d) ≤ Real.pi * d := Real.sin_le (by positivity)
    have hpd : 0 < Real.pi * d := by positivity
    have hcpos : 0 < Real.cos (Real.pi * d) := by linarith
    have key : 1 / (2 * d) ≤ |Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d))| := by
      have habs : |Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d))| =
          Real.pi * Real.cos (Real.pi * d) / Real.sin (Real.pi * d) := by
        rw [abs_of_pos (by positivity)]; ring
      rw [habs, div_le_div_iff₀ (by positivity) hsin_pos]
      nlinarith [mul_pos Real.pi_pos h0]
    have : 1 / d = 2 * (1 / (2 * d)) := by field_simp
    rw [this]
    nlinarith [abs_nonneg (Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d)))]
  · push_neg at hd
    have : 1 / d ≤ 4 := by
      rw [div_le_iff₀ h0]; linarith
    nlinarith [abs_nonneg (Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d)))]

theorem e6a_inv_pair {d : ℝ} (h0 : 0 < d) (h1 : d < 1) :
    1 / min d (1 - d) ≤ 2 * |Real.pi * (Real.cos (Real.pi * d) / Real.sin (Real.pi * d))| + 4 := by
  rcases le_total d (1 / 2) with hd | hd
  · rw [min_eq_left (by linarith)]
    exact e6a_inv_half h0 hd
  · rw [min_eq_right (by linarith)]
    have := e6a_inv_half (d := 1 - d) (by linarith) (by linarith)
    have e1 : Real.pi * (1 - d) = Real.pi - Real.pi * d := by ring
    rw [e1, Real.cos_pi_sub, Real.sin_pi_sub, neg_div, mul_neg, abs_neg] at this
    exact this

theorem e6a_pair_inv_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∃ c1 c2 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧ ∀ z : Ch N, z ∈ cep_Alcove N →
      (∑ k : Fin N, ∑ l : Fin N, (if k < l then 1 / min (z l - z k) (1 - (z l - z k)) else 0)) ≤
        c1 * (∑ i, |(gradient (cep_chamberPot a N) z) i|) + c2 := by
  obtain ⟨C, hC0, hC⟩ := cep_pair_cot_le ha N
  refine ⟨2 * C, 2 * C + 4 * (N : ℝ) ^ 2, by positivity, by positivity, fun z hz => ?_⟩
  have h1 := (hC z hz).1
  set S : ℝ := ∑ i, |(gradient (cep_chamberPot a N) z) i| with hS
  set T : ℝ := ∑ k : Fin N, ∑ l : Fin N, (if k < l then
          |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))| else 0) with hT
  have hpair : ∀ k l : Fin N, (if k < l then 1 / min (z l - z k) (1 - (z l - z k)) else (0 : ℝ)) ≤
      2 * (if k < l then |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))| else 0)
        + 4 := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, if_true]
      exact e6a_inv_pair (by linarith [hz.1 k l hkl]) (by linarith [hz.2 k l])
    · simp only [hkl, if_false]; norm_num
  have hsum : (∑ k : Fin N, ∑ l : Fin N, (if k < l then 1 / min (z l - z k) (1 - (z l - z k)) else (0 : ℝ))) ≤
      ∑ k : Fin N, ∑ l : Fin N, (2 * (if k < l then
        |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))| else 0) + 4) :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpair k l
  have hexp : (∑ k : Fin N, ∑ l : Fin N, (2 * (if k < l then
        |Real.pi * (Real.cos (Real.pi * (z l - z k)) / Real.sin (Real.pi * (z l - z k)))| else 0) + 4)) =
      2 * T + 4 * (N : ℝ) ^ 2 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hT]
    simp
    ring
  rw [hexp] at hsum
  have : T ≤ C * (S + 1) := h1
  nlinarith

end HRS.MC.CepE6A
