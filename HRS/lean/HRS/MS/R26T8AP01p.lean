import HRS.MS.R26T8AP01

/-!
# S8.2 nonlocal layer: pure conormal class and the annular source bound for any sign of the order (sigma < 0 input)
`ConormalP k b M sigma A F`: the same jet bounds as `Conormal` but with the PURE envelope `rho^(-(sigma+q)) (1+|log rho|)^b` (no additive `1`);
for `sigma >= 0` this is equivalent to `Conormal` up to a factor 2, for `sigma < 0` it is the Taylor-subtracted class.
`r26t8a_annular_sourceP` is `r26t8a_annular_source` for `ConormalP` and every real `sigma` (the numeric comparison holds for `|sigma+q-i|`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

def ConormalP {d : ℕ} (k b : ℕ) (M sigma A : ℝ) (F : Euc d → Euc d → ℝ) : Prop :=
  ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2} ∧
  ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d, z ≠ 0 →
    ‖mixedJet p q F X z‖ ≤
      A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        ((min 1 ‖z‖) ^ (-(sigma + q)) * (1 + |Real.log (min 1 ‖z‖)|) ^ b)

theorem ConormalP.toConormal {d : ℕ} {k b : ℕ} {M sigma A : ℝ} {F : Euc d → Euc d → ℝ} (hA : 0 ≤ A)
    (h : ConormalP k b M sigma A F) : Conormal k b M sigma A F := by
  refine And.intro h.1 fun p q hpq X z hz => (h.2 p q hpq X z hz).trans ?_
  have hpw0 : 0 ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
    mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _))
  refine mul_le_mul_of_nonneg_left ?_ hpw0
  linarith

theorem r26t8a_p01p_numeric (q i : ℕ) (hi : i ≤ q) (σ : ℝ) (b : ℕ) (R ρ : ℝ) (hR : 0 < R)
    (hR1 : R ≤ 1) (hρ1 : ρ ≤ 1) (hρ2 : R / 2 ≤ ρ) (hρ3 : ρ ≤ 2 * R) :
    R ^ (-(i : ℝ)) * (ρ ^ (-(σ + ((q - i : ℕ) : ℝ))) * (1 + |Real.log ρ|) ^ b) ≤
      (2 ^ (|σ| + (q : ℝ)) * (1 + Real.log 2) ^ b) * (R ^ (-(σ + (q : ℝ))) * (1 + |Real.log R|) ^ b) := by
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) hρ2
  set e : ℝ := σ + ((q - i : ℕ) : ℝ) with he
  have hcast : ((q - i : ℕ) : ℝ) = (q : ℝ) - i := Nat.cast_sub hi
  have hie : (i : ℝ) + e = σ + q := by rw [he, hcast]; ring
  have h1 : ρ ^ (-e) ≤ 2 ^ |e| * R ^ (-e) := by
    rcases le_total 0 e with he0 | he0
    · rw [Real.rpow_neg hρ.le, Real.rpow_neg hR.le]
      have : (R / 2) ^ e ≤ ρ ^ e := Real.rpow_le_rpow (by positivity) hρ2 he0
      calc (ρ ^ e)⁻¹ ≤ ((R / 2) ^ e)⁻¹ := inv_anti₀ (by positivity) this
        _ = 2 ^ e * (R ^ e)⁻¹ := by
            rw [Real.div_rpow hR.le (by norm_num), inv_div, div_eq_mul_inv]
        _ ≤ 2 ^ |e| * (R ^ e)⁻¹ := by
            refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_abs_self e)) (by positivity)
    · have hne : 0 ≤ -e := by linarith
      have : ρ ^ (-e) ≤ (2 * R) ^ (-e) := Real.rpow_le_rpow hρ.le hρ3 hne
      calc ρ ^ (-e) ≤ (2 * R) ^ (-e) := this
        _ = 2 ^ (-e) * R ^ (-e) := Real.mul_rpow (by norm_num) hR.le
        _ ≤ 2 ^ |e| * R ^ (-e) := by
            refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_abs e)) (by positivity)
  have hlogR : |Real.log R| = -Real.log R := abs_of_nonpos (Real.log_nonpos hR.le hR1)
  have hlogρ : |Real.log ρ| = -Real.log ρ := abs_of_nonpos (Real.log_nonpos hρ.le hρ1)
  have h2 : 1 + |Real.log ρ| ≤ (1 + Real.log 2) * (1 + |Real.log R|) := by
    have hl : Real.log (R / 2) ≤ Real.log ρ := Real.log_le_log (by positivity) hρ2
    rw [Real.log_div hR.ne' (by norm_num)] at hl
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hR0 : 0 ≤ |Real.log R| := abs_nonneg _
    rw [hlogρ]
    rw [hlogR] at hR0 ⊢
    nlinarith
  have h3 : (1 + |Real.log ρ|) ^ b ≤ (1 + Real.log 2) ^ b * (1 + |Real.log R|) ^ b := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 b
  have e1 : R ^ (-(i : ℝ)) * R ^ (-e) = R ^ (-(σ + (q : ℝ))) := by
    rw [← Real.rpow_add hR]; congr 1; linarith
  have hRi : 0 < R ^ (-(i : ℝ)) := Real.rpow_pos_of_pos hR _
  have habs : |e| ≤ |σ| + (q : ℝ) := by
    calc |e| ≤ |σ| + |((q - i : ℕ) : ℝ)| := abs_add_le _ _
      _ ≤ |σ| + q := by
          rw [Nat.abs_cast]
          have : ((q - i : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q i
          linarith
  have h2e : (2 : ℝ) ^ |e| ≤ 2 ^ (|σ| + (q : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) habs
  have hlg0 : 0 ≤ (1 + Real.log 2) ^ b := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hp0 : 0 ≤ ρ ^ (-e) := Real.rpow_nonneg hρ.le _
  calc R ^ (-(i : ℝ)) * (ρ ^ (-e) * (1 + |Real.log ρ|) ^ b)
      ≤ R ^ (-(i : ℝ)) * ((2 ^ |e| * R ^ (-e)) * ((1 + Real.log 2) ^ b * (1 + |Real.log R|) ^ b)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h3 (by positivity) (by positivity)) hRi.le
    _ = 2 ^ |e| * (1 + Real.log 2) ^ b * (R ^ (-(σ + (q : ℝ))) * (1 + |Real.log R|) ^ b) := by
        rw [← e1]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right h2e hlg0

theorem r26t8a_annular_sourceP {d : ℕ} (k b : ℕ) (M sigma : ℝ) (hM : 0 ≤ M)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ,
      ConormalP k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 →
      (tsupport (r26t8a_annulus chi R) ⊆ {z | R/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 2*R}) ∧
      ∀ p q : ℕ, p+q ≤ k → ∀ X z,
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (fun w => r26t8a_annulus chi R w * midPair F Y w) z) X‖ ≤
          C*A*jbracket X^(2*M) * R^(-(sigma+q)) * (1+|Real.log R|)^b := by
  obtain ⟨Kc, hKc0, hKc⟩ := r26t8a_annulus_jets hchi k
  set K1 : ℝ := 2 ^ (|sigma| + (k : ℝ)) * (1 + Real.log 2) ^ b with hK1
  have hlg0 : 0 ≤ (1 + Real.log 2) ^ b := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  refine ⟨2 ^ k * Kc * 3 ^ (2 * M) * K1, by positivity, fun A hA F hF R hR hR1 =>
    ⟨r26t8a_annulus_tsupport hchi hR, ?_⟩⟩
  intro p q hpq X z
  have ha : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_annulus chi R) :=
    (r26t8a_annulus_contDiff hchi hR).of_le (by exact_mod_cast le_top)
  have hG : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) :=
    (r26t8a_gtilde_contDiff hchi hR hF.1).of_le (by exact_mod_cast hpq)
  have hgoal : iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun w => r26t8a_annulus chi R w * midPair F Y w) z) X =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_annulus chi R Yw.2 *
        (r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2)) X z := by
    unfold r26t8a_nest
    congr 1
    funext Y
    congr 1
    funext w
    by_cases h : ‖w‖ ≤ R / 2
    · simp only [r26t8a_annulus_zero_small hchi hR h, zero_mul]
    · push Not at h
      simp only [r26t8a_psiCut_one hchi hR (by linarith : R / 4 ≤ ‖w‖), one_mul]
  rw [hgoal]
  refine (r26t8a_nest_product_bound p q (r26t8a_annulus chi R) _ X z ha hG).trans ?_
  have hRq : 0 ≤ R ^ (-(sigma + (q : ℝ))) := Real.rpow_nonneg hR.le _
  have hlogb : 0 ≤ (1 + |Real.log R|) ^ b := by positivity
  by_cases hz : z ∈ tsupport (r26t8a_annulus chi R)
  · obtain ⟨hz1, hz2⟩ := r26t8a_annulus_tsupport hchi hR hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz1; linarith
    have hρ1 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
    have hρ2 : R / 2 ≤ min 1 ‖z‖ := le_min (by linarith) hz1
    have hρ3 : min 1 ‖z‖ ≤ 2 * R := (min_le_right _ _).trans hz2
    have hwt := r26t8a_p01_weight hM (X := X) (z := z) (by linarith)
    set W : ℝ := 3 ^ (2 * M) * jbracket X ^ (2 * M) with hW
    have hW0 : 0 ≤ W := by
      rw [hW]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (s83_jb_pos X).le _)
    set Q : ℝ := Kc * A * W * K1 * (R ^ (-(sigma + (q : ℝ))) * (1 + |Real.log R|) ^ b) with hQ
    have hQ0 : 0 ≤ Q := by
      rw [hQ]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hKc0 hA) hW0) hK10) (mul_nonneg hRq hlogb)
    have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (r26t8a_annulus chi R) z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z‖ ≤
        (q.choose i : ℝ) * Q := by
      intro i hi
      have hiq : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [r26t8a_nest_gtilde hchi hR p (q - i) X z (by linarith)]
      have hjet := hKc R hR hR1 i (by omega) z
      have hconf := hF.2 p (q - i) (by omega) X z hz0
      have hnum := r26t8a_p01p_numeric q i hiq sigma b R (min 1 ‖z‖) hR hR1 hρ1 hρ2 hρ3
      have hK2 : 2 ^ (|sigma| + (q : ℝ)) * (1 + Real.log 2) ^ b ≤ K1 := by
        have : (2 : ℝ) ^ (|sigma| + (q : ℝ)) ≤ 2 ^ (|sigma| + (k : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have : (q : ℝ) ≤ k := by exact_mod_cast (by omega : q ≤ k)
            linarith)
        rw [hK1]; exact mul_le_mul_of_nonneg_right this (by positivity)
      have hRi : 0 ≤ R ^ (-(i : ℝ)) := Real.rpow_nonneg hR.le _
      have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
        unfold pairWeight
        exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
      have hT0 : 0 ≤ (min 1 ‖z‖) ^ (-(sigma + ((q - i : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by
        have : 0 ≤ (min 1 ‖z‖) ^ (-(sigma + ((q - i : ℕ) : ℝ))) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
        positivity
      have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
      calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (r26t8a_annulus chi R) z‖ * ‖mixedJet p (q - i) F X z‖
          ≤ (q.choose i : ℝ) * (Kc * R ^ (-(i : ℝ))) *
              (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
                ((min 1 ‖z‖) ^ (-(sigma + ((q - i : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hjet hch) hconf (norm_nonneg _) (by positivity)
        _ = (q.choose i : ℝ) * (Kc * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) *
              (R ^ (-(i : ℝ)) * ((min 1 ‖z‖) ^ (-(sigma + ((q - i : ℕ) : ℝ))) *
                (1 + |Real.log (min 1 ‖z‖)|) ^ b)) := by ring
        _ ≤ (q.choose i : ℝ) * (Kc * A * W) * (K1 * (R ^ (-(sigma + (q : ℝ))) * (1 + |Real.log R|) ^ b)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwt (by positivity)) hch)
              (hnum.trans (mul_le_mul_of_nonneg_right hK2 (by positivity))) (by positivity) (by positivity)
        _ = (q.choose i : ℝ) * Q := by rw [hQ]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsum : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) = 2 ^ q := by
      exact_mod_cast Nat.sum_range_choose q
    rw [hsum]
    have h2k : (2 : ℝ) ^ q ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2 : ℝ) ^ q * Q ≤ 2 ^ k * Q := mul_le_mul_of_nonneg_right h2k hQ0
      _ = _ := by rw [hQ, hW]; ring
  · have h0 : ∀ i, iteratedFDeriv ℝ i (r26t8a_annulus chi R) z = 0 := fun i =>
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_iteratedFDeriv_subset i h))
    simp only [h0, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hA) (Real.rpow_nonneg (s83_jb_pos X).le _)) hRq) hlogb

end HRS.MS.R26T8A
