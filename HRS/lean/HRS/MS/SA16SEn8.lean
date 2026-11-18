import HRS.MS.SA16SEn7

/-!
# S.A.16 (SA16S) En8: the transport term of the energy (packet P7, step 9)

`sa16sz_transport`: for `φ ∈ C_c^∞` and `b` smooth with `‖D^i b_l‖ ≤ B` for `i ≤ m+1`:
`∫ sa16sz_dens m p φ (b·∇φ) ≤ cTr · ∑_j ∫ |D^jφ|^p`, `cTr = d B / p + (∑_j d^j) d 2^m B (d+1)^m`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En8
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the energy density `∑_j |D^jφ|^p` -/
def sa16sz_E (m : ℕ) (p : ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j : Fin (m + 1), sa16sz_vn φ j x ^ p

lemma sa16sz_vn_cs {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (j : ℕ) : HasCompactSupport (sa16sz_vn φ j) := by
  have hT := sa16sy_T_cc (W := fun idx : Fin j → Fin d => partialDeriv idx φ)
    (fun idx => sa16s_cc_partialDeriv hφ idx)
  have := hT.2.comp_left (g := Real.sqrt) Real.sqrt_zero
  exact this

lemma sa16sz_vn_pow_cs {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (j : ℕ) {q : ℝ} (hq : 0 < q) :
    HasCompactSupport (fun x => sa16sz_vn φ j x ^ q) :=
  (sa16sz_vn_cs hφ j).comp_left (g := fun t : ℝ => t ^ q) (Real.zero_rpow hq.ne')

lemma sa16sz_abs_le_vn (φ : Euc d → ℝ) (j : ℕ) (idx : Fin j → Fin d) (x : Euc d) :
    |partialDeriv idx φ x| ≤ sa16sz_vn φ j x := by
  unfold sa16sz_vn vnorm
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun idx : Fin j → Fin d => partialDeriv idx φ x ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ idx)

lemma sa16sz_pow_aux {a M p : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hp : 1 < p) : a ^ (p - 1) * M ≤ M ^ p := by
  have hM0 : 0 ≤ M := ha.trans haM
  rcases eq_or_lt_of_le hM0 with h0 | hpos
  · have : a = 0 := le_antisymm (h0 ▸ haM) ha
    rw [this, ← h0, Real.zero_rpow (by linarith : p - 1 ≠ 0), Real.zero_rpow (by linarith : p ≠ 0)]
    simp
  · calc a ^ (p - 1) * M ≤ M ^ (p - 1) * M :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha haM (by linarith)) hM0
      _ = M ^ p := by rw [← Real.rpow_add_one hpos.ne']; congr 1; ring

lemma sa16sz_vn_le_E (m : ℕ) (φ : Euc d → ℝ) (x : Euc d) (j : Fin (m + 1)) :
    sa16sz_vn φ j x ^ p ≤ sa16sz_E m p φ x := by
  unfold sa16sz_E
  exact Finset.single_le_sum (f := fun j' : Fin (m + 1) => sa16sz_vn φ j' x ^ p)
    (fun j' _ => Real.rpow_nonneg (sa16sz_vn_nonneg φ j' x) _) (Finset.mem_univ j)

lemma sa16sz_E_nonneg (m : ℕ) (φ : Euc d → ℝ) (x : Euc d) : 0 ≤ sa16sz_E m p φ x :=
  Finset.sum_nonneg fun j _ => Real.rpow_nonneg (sa16sz_vn_nonneg φ j x) _

lemma sa16sz_wjet_le (m : ℕ) (φ : Euc d → ℝ) (x : Euc d) {j : ℕ} (hj : j ≤ m) :
    ‖wJet j φ x‖ ≤ sa16sz_E m p φ x ^ (1 / p) := by
  have hp0 : 0 < p := by linarith [Fact.out (p := 2 ≤ p)]
  have hE0 := sa16sz_E_nonneg (p := p) m φ x
  refine (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hE0 _)).2 fun τ => ?_
  rw [Real.norm_eq_abs]
  have hτ : (τ.1 : ℕ) ≤ m := by have := τ.1.2; omega
  refine (sa16sz_abs_le_vn φ (τ.1 : ℕ) τ.2 x).trans ?_
  rw [one_div, Real.le_rpow_inv_iff_of_pos (sa16sz_vn_nonneg φ _ x) hE0 hp0]
  exact sa16sz_vn_le_E (p := p) m φ x ⟨τ.1, by omega⟩

/-- pointwise bound of the commutator contribution -/
lemma sa16sz_remainder_le (m : ℕ) (φ : Euc d → ℝ) (x : Euc d) {j : ℕ} (hj : j ≤ m) {cR : ℝ}
    (R : (Fin j → Fin d) → ℝ) (hR : ∀ idx, |R idx| ≤ cR * ‖wJet j φ x‖) (hcR : 0 ≤ cR) :
    |∑ idx : Fin j → Fin d, sa16sz_vn φ j x ^ (p - 2) * partialDeriv idx φ x * R idx| ≤
      (Fintype.card (Fin j → Fin d) : ℝ) * cR * sa16sz_E m p φ x := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  set a := sa16sz_vn φ j x with ha
  have ha0 : 0 ≤ a := sa16sz_vn_nonneg φ j x
  set E := sa16sz_E m p φ x with hE
  have hE0 : 0 ≤ E := sa16sz_E_nonneg (p := p) m φ x
  set M := E ^ (1 / p) with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg hE0 _
  have hMp : M ^ p = E := by
    rw [hM, ← Real.rpow_mul hE0, one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hN := sa16sz_wjet_le (p := p) m φ x hj
  have haM : a ≤ M := by
    rw [hM, one_div, Real.le_rpow_inv_iff_of_pos ha0 hE0 hp0]
    exact sa16sz_vn_le_E (p := p) m φ x ⟨j, by omega⟩
  have hterm : ∀ idx : Fin j → Fin d, |a ^ (p - 2) * partialDeriv idx φ x * R idx| ≤ a ^ (p - 1) * (cR * M) := by
    intro idx
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha0 _)]
    have h1 : |partialDeriv idx φ x| ≤ a := sa16sz_abs_le_vn φ j idx x
    have h2 : |R idx| ≤ cR * M := (hR idx).trans (mul_le_mul_of_nonneg_left hN hcR)
    have h3 : a ^ (p - 2) * a = a ^ (p - 1) := by
      rcases eq_or_lt_of_le ha0 with h0 | hpos
      · rw [← h0]
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ p - 2 by linarith) with hz | hz
        · rw [← hz]; simp; rw [show p - 1 = 1 by linarith]; simp
        · rw [Real.zero_rpow hz.ne', Real.zero_rpow (by linarith : p - 1 ≠ 0)]; simp
      · rw [← Real.rpow_add_one hpos.ne']; congr 1; ring
    calc a ^ (p - 2) * |partialDeriv idx φ x| * |R idx|
        ≤ a ^ (p - 2) * a * (cR * M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ha0 _)) h2 (abs_nonneg _)
            (mul_nonneg (Real.rpow_nonneg ha0 _) ha0)
      _ = a ^ (p - 1) * (cR * M) := by rw [h3]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun idx _ => hterm idx).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 := sa16sz_pow_aux ha0 haM (by linarith : 1 < p)
  rw [hMp] at h4
  have hcard : (0 : ℝ) ≤ (Fintype.card (Fin j → Fin d) : ℝ) := Nat.cast_nonneg _
  calc (Fintype.card (Fin j → Fin d) : ℝ) * (a ^ (p - 1) * (cR * M))
      = (Fintype.card (Fin j → Fin d) : ℝ) * cR * (a ^ (p - 1) * M) := by ring
    _ ≤ (Fintype.card (Fin j → Fin d) : ℝ) * cR * E :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg hcard hcR)

end En8

end HRS.Whole.AppendixA.Phase2SA16R
