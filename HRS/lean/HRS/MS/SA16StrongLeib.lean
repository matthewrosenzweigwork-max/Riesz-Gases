import HRS.MS.SA16StrongWnormAlg

/-!
# S.A.16: Leibniz bound for jets

`sa16y_prod_jet_le`: pointwise, `‖wJet n (f g) x‖ ≤ B (d+1)^n ‖wJet n g x‖` if `‖D^i f x‖ ≤ B` for `i ≤ n`.
`sa16y_jet_mono`: `‖wJet m g x‖ ≤ ‖wJet n g x‖` for `m ≤ n`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Leib
variable {d : ℕ}

lemma sa16y_jet_mono {m n : ℕ} (hmn : m ≤ n) (g : Euc d → ℝ) (x : Euc d) :
    ‖wJet m g x‖ ≤ ‖wJet n g x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_
  rw [Real.norm_eq_abs]
  exact sa16j_pd_le_jet n g x (by have := τ.1.2; omega) τ.2

lemma sa16y_pd_le_iter (g : Euc d → ℝ) (x : Euc d) {j : ℕ} (idx : Fin j → Fin d) :
    |partialDeriv idx g x| ≤ ‖iteratedFDeriv ℝ j g x‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ j g x).le_opNorm (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at h
  simpa [Real.norm_eq_abs] using h

lemma sa16y_iter_le_jet (g : Euc d → ℝ) (x : Euc d) {n l : ℕ} (hl : l ≤ n) :
    ‖iteratedFDeriv ℝ l g x‖ ≤ (d : ℝ) ^ l * ‖wJet n g x‖ := by
  refine (sa16j_norm_iter_le g x l).trans ?_
  calc ∑ r : Fin l → Fin d, |partialDeriv r g x|
      ≤ ∑ r : Fin l → Fin d, ‖wJet n g x‖ :=
        Finset.sum_le_sum fun r _ => sa16j_pd_le_jet n g x hl r
    _ = (d : ℝ) ^ l * ‖wJet n g x‖ := by simp [Finset.sum_const]

lemma sa16y_prod_jet_le {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : Euc d)
    {B : ℝ} (hB : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ B) :
    ‖wJet n (fun y => f y * g y) x‖ ≤ B * ((d : ℝ) + 1) ^ n * ‖wJet n g x‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hJ0 := norm_nonneg (wJet n g x)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
  rw [Real.norm_eq_abs]
  have hj : (τ.1 : ℕ) ≤ n := by have := τ.1.2; omega
  set j : ℕ := (τ.1 : ℕ) with hjdef
  refine (sa16y_pd_le_iter _ x τ.2).trans ?_
  have hfg : ContDiff ℝ ∞ (fun y => f y * g y) := hf.mul hg
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hf.of_le (by exact_mod_cast le_top))
    (hg.of_le (by exact_mod_cast le_top)) x (n := j) (N := (j : ℕ∞ω)) le_rfl
  refine hL.trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖ ≤
      B * ‖wJet n g x‖ * ((1 : ℝ) ^ i * (d : ℝ) ^ (j - i) * ((j.choose i : ℕ) : ℝ)) := by
    intro i hi
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have h1 := hB i (hi'.trans hj)
    have h2 := sa16y_iter_le_jet g x (n := n) (show j - i ≤ n by omega)
    have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (j.choose i))) h2
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hB0)
    refine h3.trans (le_of_eq ?_)
    simp only [one_pow, one_mul]
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, ← add_pow]
  have hpow : (d + 1 : ℝ) ^ j ≤ ((d : ℝ) + 1) ^ n :=
    pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith) hj
  have : (1 + (d : ℝ)) ^ j = ((d : ℝ) + 1) ^ j := by rw [add_comm]
  rw [this]
  calc B * ‖wJet n g x‖ * ((d : ℝ) + 1) ^ j ≤ B * ‖wJet n g x‖ * ((d : ℝ) + 1) ^ n :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hB0 hJ0)
    _ = B * ((d : ℝ) + 1) ^ n * ‖wJet n g x‖ := by ring

end Leib

end HRS.Whole.AppendixA.Phase2SA16
