import HRS.MS.SA16QFin2

/-!
# S.A.16 (SA16Q), E6 part 17: the uniform bound

`sa16q_term_unif`: for smooth `a` with `‖D^κ a(x)‖ ≤ W (1+|x|)^{-(d+3)}` (`κ ≤ m+1`),
`‖ ‖D^κ a‖ ‖D^n u‖ ‖_R ≤ K ‖u‖_{W^{m,p}}` (`n ≤ m`) with `K` independent of `a, u`.
`sa16q_unif_master`: the resulting uniform bound on `‖∂^idx eucNonlocal s M a u‖_p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Fin3
variable {d : ℕ}

lemma sa16q_omega_le_one (x : Euc d) : (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
    (by have : (0 : ℝ) ≤ ((d + 3 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)

theorem sa16q_term_unif (hd1 : 1 ≤ d) {p r : ℝ} (hp : 1 < p) (hr1 : 1 < r)
    (hr : r = p ∨ (r < p ∧ ∃ ra : ℝ, 1 ≤ ra ∧ 1 / r = 1 / ra + 1 / p)) (m : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {a : Euc d → ℝ}, ContDiff ℝ ∞ a →
      (∀ κ ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
      ∀ (u : 𝓢(Euc d, ℝ)) {κ n : ℕ}, κ ≤ m + 1 → n ≤ m →
        eLpNorm (fun x => ‖iteratedFDeriv ℝ κ a x‖ * ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal r) volume ≤
          K * eLpNorm (wJet m (⇑u)) (ENNReal.ofReal p) volume := by
  rcases hr with rfl | ⟨hrlt, ra, hra, h⟩
  · refine ⟨ENNReal.ofReal (W * (d : ℝ) ^ m), ENNReal.ofReal_ne_top, fun {a} ha hκ u {κ n} hκ' hn => ?_⟩
    exact sa16q_unif_CZ hd1 ha hW (fun x => (hκ κ hκ' x).trans
      (mul_le_of_le_one_right hW (sa16q_omega_le_one x))) u hn
  · refine ⟨ENNReal.ofReal W * eLpNorm (fun x : Euc d => (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)))
        (ENNReal.ofReal ra) volume * ENNReal.ofReal ((d : ℝ) ^ m),
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (sa16q_omega_lp hra).ne)
        ENNReal.ofReal_ne_top, fun {a} ha hκ u {κ n} hκ' hn => ?_⟩
    refine (sa16q_unif_HLS hd1 ha hW (hκ κ hκ') u hn (by linarith) (by linarith) (by linarith) h).trans
      (le_of_eq ?_)
    ring

end Fin3

section Fin3b
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

/-- the exponents of the master estimate have Holder partners -/
lemma sa16q_master_exps {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ q r C1 C2 : ℝ, 1 < q ∧ q < p ∧ (∃ ra : ℝ, 1 ≤ ra ∧ 1 / q = 1 / ra + 1 / p) ∧
      1 < r ∧ (r = p ∨ (r < p ∧ ∃ ra : ℝ, 1 ≤ ra ∧ 1 / r = 1 / ra + 1 / p)) ∧ 0 < C1 ∧ 0 < C2 ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ), (∀ i j, |M i j| ≤ MB) →
        ∀ {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) {l : ℕ} (idx : Fin l → Fin d),
        eLpNorm (partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)) (ENNReal.ofReal p) volume ≤
          ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
            (ENNReal.ofReal C2 * sa16q_NP a u l r + ENNReal.ofReal C1 * sa16q_NQ a u l q) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨q, r, C1, C2, ⟨hq1, hqp, hq⟩, ⟨hr1, hrp, hr⟩, hC1, hC2, hmaster⟩ :=
    sa16q_master hd hs hs2 hp hfar
  refine ⟨q, r, C1, C2, hq1, hqp, ?_, hr1, ?_, hC1, hC2, hmaster⟩
  · refine ⟨(((d : ℝ) - s - 1) / d)⁻¹, ?_, ?_⟩
    · rw [le_inv_comm₀ one_pos (by apply div_pos <;> linarith), inv_one, div_le_one hd0]
      linarith
    · rw [one_div (((d : ℝ) - s - 1) / d)⁻¹, inv_inv]
      linarith
  · rcases hr with h | ⟨hlt, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨hlt, (((d : ℝ) - s - 2) / d)⁻¹, ?_, ?_⟩
      · have hpos : 0 < ((d : ℝ) - s - 2) / d := by
          have h1 : 1 / p < 1 / r := one_div_lt_one_div_of_lt (by linarith) hlt
          have : ((d : ℝ) - s - 2) / d = 1 / r - 1 / p := by linarith
          linarith
        rw [le_inv_comm₀ one_pos hpos, inv_one, div_le_one hd0]
        linarith
      · rw [one_div (((d : ℝ) - s - 2) / d)⁻¹, inv_inv]
        linarith

end Fin3b

end HRS.Whole.AppendixA.Phase2SA16Q
