import HRS.MS.Mov63GAux15

/-!
# S6.3, packet N8 (part 16): from the jets of `Q` to the decay clauses of `MovDecayBounds`

Namespace `HRS.MS.Mov63`, prefix `mng_`.  `mng_log_deriv`: derivatives of `log` on `[1/2,2]`; `mng_logQ_bound`: `‖D^n (log ∘ Q)(x)‖ ≤ n! (1+n!2^n) ε`
when `‖D^iQ(x)‖ ≤ ε ≤ 1` (`1 ≤ i ≤ n`), linear in `ε` (Faà di Bruno bound `norm_iteratedFDeriv_comp_le'` with `D = ε^{1/n}`);
`mng_cbVecE_le`: `cbNormVecE j F ≤ ofReal ((j+1) B)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma mng_log_deriv (i : ℕ) {t : ℝ} (ht1 : 1 / 2 ≤ t) (ht2 : t ≤ 2) :
    ‖iteratedFDeriv ℝ i Real.log t‖ ≤ 1 + (i.factorial : ℝ) * 2 ^ i := by
  have ht0 : 0 < t := by linarith
  have hfa : (0 : ℝ) ≤ (i.factorial : ℝ) * 2 ^ i := by positivity
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_sub_one_of_pos ht0
    have h2 := Real.one_sub_inv_le_log_of_pos ht0
    have h3 : t⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
    constructor <;> simp <;> linarith
  | succ k =>
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate,
      iter_deriv_inv]
    have hinv : t⁻¹ ≤ 2 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
    have hz : t ^ (-1 - (k : ℤ)) = (t⁻¹) ^ (k + 1) := by
      rw [inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1; push_cast; ring
    rw [hz, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k.factorial : ℝ)), abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t⁻¹) ^ (k + 1))]
    have h1 : (t⁻¹) ^ (k + 1) ≤ 2 ^ (k + 1) := pow_le_pow_left₀ (by positivity) hinv _
    have h2 : (k.factorial : ℝ) ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_le (Nat.le_succ k)
    have : (k.factorial : ℝ) * (t⁻¹) ^ (k + 1) ≤ ((k + 1).factorial : ℝ) * 2 ^ (k + 1) :=
      mul_le_mul h2 h1 (by positivity) (by positivity)
    linarith

lemma mng_logQ_bound {Q : Euc d → ℝ} {n : ℕ} (hn0 : 1 ≤ n) (hQ : ContDiff ℝ n Q) (hpos : ∀ y, 0 < Q y) (x : Euc d)
    (hx1 : 1 / 2 ≤ Q x) (hx2 : Q x ≤ 2) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hb : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Q x‖ ≤ ε) :
    ‖iteratedFDeriv ℝ n (fun y => Real.log (Q y)) x‖ ≤
      (n.factorial : ℝ) * (1 + (n.factorial : ℝ) * 2 ^ n) * ε := by
  set D : ℝ := ε ^ ((1 : ℝ) / n) with hD
  have hDn : D ^ n = ε := by
    rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hε0]
    have : (1 : ℝ) / n * n = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hlog : ContDiffOn ℝ n Real.log (Ioi (0 : ℝ)) :=
    (Real.contDiffOn_log (n := n)).mono (fun t ht => ne_of_gt ht)
  have hrange : Set.range Q ⊆ Ioi 0 := by rintro _ ⟨y, rfl⟩; exact hpos y
  have h := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) (g := Real.log) (f := Q) (n := n) (N := n) hrange
    (isOpen_Ioi.uniqueDiffOn) hlog hQ le_rfl x (C := 1 + (n.factorial : ℝ) * 2 ^ n) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (hpos x)]
      exact (mng_log_deriv i hx1 hx2).trans (by
        have : (i.factorial : ℝ) * 2 ^ i ≤ (n.factorial : ℝ) * 2 ^ n :=
          mul_le_mul (by exact_mod_cast Nat.factorial_le hi) (pow_le_pow_right₀ (by norm_num) hi)
            (by positivity) (by positivity)
        linarith))
    (fun i hi1 hin => by
      refine (hb i hi1 hin).trans ?_
      have hDi : D ^ i = ε ^ ((i : ℝ) / n) := by
        rw [hD, ← Real.rpow_natCast, ← Real.rpow_mul hε0]; congr 1; ring
      rw [hDi]
      by_cases he : ε = 0
      · subst he
        rw [Real.zero_rpow (by positivity)]
      · have hε : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm he)
        calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
          _ ≤ ε ^ ((i : ℝ) / n) := by
            apply Real.rpow_le_rpow_of_exponent_ge hε hε1
            rw [div_le_one (by exact_mod_cast hn0)]; exact_mod_cast hin)
  rw [hDn] at h
  exact h

lemma mng_cbVecE_le {F : Euc d → Euc d} {j : ℕ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ k ≤ j, ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ B) :
    cbNormVecE j F ≤ ENNReal.ofReal ((j + 1) * B) := by
  unfold cbNormVecE
  have h1 : ∀ k ∈ Finset.range (j + 1), (⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ k F x‖) ≤ ENNReal.ofReal B := by
    intro k hk
    exact iSup_le fun x => ENNReal.ofReal_le_ofReal (h k (by have := Finset.mem_range.1 hk; omega) x)
  calc _ ≤ ∑ k ∈ Finset.range (j + 1), ENNReal.ofReal B := Finset.sum_le_sum h1
    _ = ENNReal.ofReal ((j + 1) * B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl

end HRS.MS.Mov63

end
