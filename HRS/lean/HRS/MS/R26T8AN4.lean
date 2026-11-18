import HRS.MS.R26T8AN3

/-!
# S8.2 local Newton layer, smooth part (N), step 4: jets of the raw Newton integral of a smooth pair function
`r26t8a_rawNewton_smooth_jets`: if `P` is `C^k` with `‖nest p q (midPair P) X z‖ <= B pw(X +- z/2)` for `p + q <= k`, then the same holds for
`midPair (rawNewton nu chi P)` with a constant `C` independent of `P`, `B`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_N4_mid_eq (nu : ℝ) (chi : Euc d → ℝ) (P : Euc d → Euc d → ℝ) (Y w : Euc d) :
    midPair (rawNewton nu chi P) Y w =
      chi w * ∫ u, newtonKernel d nu u * (chi (w - u) * midPair P Y (w - u)) := by
  rw [r26t8a_p07_raw_mid_int]
  congr 1
  rw [← integral_sub_left_eq_self (fun z : Euc d => newtonKernel d nu (w - z) * chi z * midPair P Y z) volume w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [sub_sub_cancel]
  ring

theorem r26t8a_rawNewton_smooth_jets (hd : 2 ≤ d) (k : ℕ) (nu M : ℝ) (hM : 0 ≤ M) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 ≤ B → ∀ P : Euc d → Euc d → ℝ,
      ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry P) →
      (∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) X z‖ ≤
          B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) →
      ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi P) Yw.1 Yw.2) X z‖ ≤
          C * B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  obtain ⟨Dc, hDc0, hDc⟩ := r26t8a_chi_jets hchi k
  set I : ℝ := ∫ u in ball (0 : Euc d) 5, |newtonKernel d nu u| with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball (fun u _ => abs_nonneg _)
  set c1 : ℝ := Dc * 2 ^ k * 16 ^ M with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  refine ⟨2 ^ k * Dc * c1 * I * 3 ^ (2 * M), by positivity, fun B hB P hPc hPj p q hpq X z => ?_⟩
  have hchic : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) chi := contDiff_infty.1 hchi.1 (p + q)
  have hL : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) :=
    (contDiff_fst.add (contDiff_snd.const_smul _)).prodMk (contDiff_fst.sub (contDiff_snd.const_smul _))
  have hMid : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) := hPc.comp hL
  have hSc : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => chi Yw.2 * midPair P Yw.1 Yw.2) :=
    ((contDiff_infty.1 hchi.1 k).comp contDiff_snd).mul hMid
  have hSv : ∀ Y w : Euc d, 2 < ‖w‖ → chi w * midPair P Y w = 0 := fun Y w hw => by
    rw [hchi.2.2.2.2 w hw.le, zero_mul]
  by_cases hz2 : 2 < ‖z‖
  · have hz0 : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi P) Yw.1 Yw.2) X z =
        r26t8a_nest p q (fun _ => (0 : ℝ)) X z :=
      r26t8a_p07_congr_ball p q _ _ (by linarith : 0 < ‖z‖ - 2) X z fun Y w hw => by
        have h1 : 2 < ‖w‖ := by
          have := norm_sub_norm_le z w
          rw [norm_sub_rev] at this
          linarith
        rw [r26t8a_p07_raw_mid_int, hchi.2.2.2.2 w h1.le]; simp
    rw [hz0]
    have : r26t8a_nest p q (fun _ : Euc d × Euc d => (0 : ℝ)) X z = 0 := by
      unfold r26t8a_nest
      have : (fun Y : Euc d => iteratedFDeriv ℝ q (fun _ : Euc d => (0 : ℝ)) z) = fun _ => 0 := by
        funext Y; simp
      simp [this]
    rw [this, norm_zero]
    have : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
      mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
    positivity
  · push Not at hz2
    set W : ℝ := jbracket X ^ (2 * M) with hW
    have hW0 : 0 ≤ W := Real.rpow_nonneg (s83_jb_pos X).le _
    have hWpw : W ≤ 3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
      r26t8a_jb_le_pairWeight hM X z hz2
    have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
      mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
    set N : Euc d × Euc d → ℝ := fun Yw => ∫ u, newtonKernel d nu u * (chi (Yw.2 - u) * midPair P Yw.1 (Yw.2 - u)) with hN
    have hNc : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) N :=
      r26t8a_N1_conv_contDiff (r26t8a_N2_locInt fun r => r26t8a_K_integrableOn hd nu r)
        (hSc.of_le (by exact_mod_cast hpq)) 2 hSv
    have hfun : (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi P) Yw.1 Yw.2) =
        fun Yw => chi Yw.2 * N Yw := by
      funext Yw; exact r26t8a_N4_mid_eq nu chi P Yw.1 Yw.2
    -- bound of the nested jets of the source
    set B' : ℝ := c1 * B * W with hB'
    have hB'0 : 0 ≤ B' := by rw [hB']; positivity
    have hSjet : ∀ j : ℕ, j ≤ q → ∀ i : ℕ, i ≤ p → ∀ Y : Euc d, ‖Y - X‖ < 1 → ∀ w : Euc d,
        ‖r26t8a_nest i j (fun Yw : Euc d × Euc d => chi Yw.2 * midPair P Yw.1 Yw.2) Y w‖ ≤ B' := by
      intro j hj i hi Y hY w
      by_cases hw : 2 < ‖w‖
      · rw [r26t8a_nest_vanish i j _ 2 hSv Y w hw, norm_zero]; exact hB'0
      · push Not at hw
        have hprod := r26t8a_nest_product_bound i j chi (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) Y w
          (contDiff_infty.1 hchi.1 (i + j))
          (hMid.of_le (by exact_mod_cast (by omega : i + j ≤ k)))
        refine hprod.trans ?_
        have hpwb := r26t8a_N3_pw_le hM X Y w hY hw
        calc ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l chi w‖ *
              ‖r26t8a_nest i (j - l) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) Y w‖
            ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * (Dc * (B * (16 ^ M * W))) := by
              refine Finset.sum_le_sum fun l hl => ?_
              have hl' : l ≤ j := by have := Finset.mem_range.1 hl; omega
              have h1 := hDc l (by omega) w
              have h2 := hPj i (j - l) (by omega) Y w
              have h3 : B * pairWeight M (Y + (1 / 2 : ℝ) • w) (Y - (1 / 2 : ℝ) • w) ≤ B * (16 ^ M * W) :=
                mul_le_mul_of_nonneg_left hpwb hB
              have hch : (0 : ℝ) ≤ j.choose l := Nat.cast_nonneg _
              calc (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l chi w‖ *
                    ‖r26t8a_nest i (j - l) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) Y w‖
                  ≤ (j.choose l : ℝ) * Dc * (B * (16 ^ M * W)) :=
                    mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) (h2.trans h3) (norm_nonneg _) (by positivity)
                _ = _ := by ring
          _ = (2 ^ j : ℝ) * (Dc * (B * (16 ^ M * W))) := by
              rw [← Finset.sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose j
          _ ≤ B' := by
              rw [hB', hc1]
              have h2j : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
              have : 0 ≤ Dc * (B * (16 ^ M * W)) := by positivity
              nlinarith
    rw [hfun]
    have hprod := r26t8a_nest_product_bound p q chi N X z hchic hNc
    refine hprod.trans ?_
    calc ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ * ‖r26t8a_nest p (q - i) N X z‖
        ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * (Dc * (B' * I)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hiq : i ≤ q := by have := Finset.mem_range.1 hi; omega
          have h1 := hDc i (by omega) z
          have h2 := r26t8a_N2_conv_nest hd nu p (q - i) (S := fun Yw : Euc d × Euc d => chi Yw.2 * midPair P Yw.1 Yw.2)
            (hSc.of_le (by exact_mod_cast (by omega : p + (q - i) ≤ k))) 2 hSv B' X z
            (fun i' hi' j hj Y hY w => hSjet j (by omega) i' hi' Y hY w) 5 (by linarith)
          have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
          calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ * ‖r26t8a_nest p (q - i) N X z‖
              ≤ (q.choose i : ℝ) * Dc * (B' * I) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _) (by positivity)
            _ = _ := by ring
      _ = (2 ^ q : ℝ) * (Dc * (B' * I)) := by
          rw [← Finset.sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose q
      _ ≤ 2 ^ k * Dc * c1 * I * 3 ^ (2 * M) * B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
          have h2q : (2 : ℝ) ^ q ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
          have hrest : 0 ≤ Dc * (c1 * B * W * I) := by positivity
          have h3 : (2 : ℝ) ^ q * (Dc * (B' * I)) ≤ 2 ^ k * (Dc * (c1 * B * W * I)) := by
            rw [hB']
            exact mul_le_mul h2q (le_of_eq (by ring)) (by positivity) (by positivity)
          refine h3.trans ?_
          have h4 : 2 ^ k * (Dc * (c1 * B * W * I)) ≤ 2 ^ k * (Dc * (c1 * B * (3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) * I)) := by
            gcongr
          refine h4.trans (le_of_eq ?_)
          ring

end HRS.MS.R26T8A
