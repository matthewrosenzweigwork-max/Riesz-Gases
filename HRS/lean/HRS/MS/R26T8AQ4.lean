import HRS.MS.R26T8AQ3

/-!
# S8.2 Taylor split (Q), step 4: nested jets of the local Riesz potential of a smooth function
`r26t8a_localRiesz_smooth_jets`: for `P` of class `C^k` with `‖nest p q (midPair P)‖ <= B pairWeight` (`p+q <= k`):
`‖nest p q (midPair (localRiesz alpha chi P))‖ <= C B pairWeight`, `C` independent of `P`, `B`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_localRiesz_smooth_jets (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (alpha M : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 ≤ B → ∀ P : Euc d → Euc d → ℝ,
      ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry P) →
      (∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) X z‖ ≤
          B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) →
      ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_localRiesz alpha chi P) Yw.1 Yw.2) X z‖ ≤
          C * B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  obtain ⟨Cv, hCv0, hCv⟩ := r26t8a_Vg_near d hd k alpha M halpha had hM
  obtain ⟨Dχ, hDχ0, hDχ⟩ := r26t8a_chi_jet_bound hchi k
  set T3 : ℝ := 3 ^ (2 * M) with hT3
  have hT30 : 0 ≤ T3 := by rw [hT3]; positivity
  refine ⟨2 ^ k * Dχ * Cv * (2 ^ k * Dχ * T3) * T3, by positivity, ?_⟩
  intro B hB P hP hjet p q hpq X z
  have hjb0 : ∀ Y : Euc d, 0 ≤ jbracket Y ^ (2 * M) := fun Y => Real.rpow_nonneg (s83_jb_pos Y).le _
  have hpw0 : ∀ Y w : Euc d, 0 ≤ pairWeight M (Y + (1 / 2 : ℝ) • w) (Y - (1 / 2 : ℝ) • w) := fun Y w =>
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hchic : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) chi := fun n => hchi.1.of_le (by exact_mod_cast le_top)
  -- the source
  set srcP : Euc d × Euc d → ℝ := fun Yw => chi Yw.2 * midPair P Yw.1 Yw.2 with hsrcP
  have hmidP : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) := by
    have hlin : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) :=
      (contDiff_fst.add (contDiff_snd.const_smul _)).prodMk (contDiff_fst.sub (contDiff_snd.const_smul _))
    exact hP.comp hlin
  have hsrc_cd : ContDiff ℝ (k : WithTop ℕ∞) srcP := ((hchic k).comp contDiff_snd).mul hmidP
  have hSv : ∀ Y v : Euc d, 2 < ‖v‖ → srcP (Y, v) = 0 := fun Y v hv => by
    simp only [hsrcP, hchi.2.2.2.2 v hv.le, zero_mul]
  have hbdsrc : ∀ i j : ℕ, i + j ≤ k → ∀ Y v : Euc d,
      ‖r26t8a_nest i j srcP Y v‖ ≤ (2 ^ k * Dχ * T3 * B) * jbracket Y ^ (2 * M) := by
    intro i j hij Y v
    by_cases hv : ‖v‖ ≤ 2
    · refine (r26t8a_nest_product_bound i j chi _ Y v (hchic _) (hmidP.of_le (by exact_mod_cast hij))).trans ?_
      have hterm : ∀ t ∈ Finset.range (j + 1), (j.choose t : ℝ) * ‖iteratedFDeriv ℝ t chi v‖ *
          ‖r26t8a_nest i (j - t) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) Y v‖ ≤
          (j.choose t : ℝ) * (Dχ * (T3 * B * jbracket Y ^ (2 * M))) := by
        intro t ht
        have htj : t ≤ j := by rw [Finset.mem_range] at ht; omega
        have h1 := hDχ t (by omega) v
        have h2 := hjet i (j - t) (by omega) Y v
        have h3 := r26t8a_p01_weight hM (X := Y) (z := v) hv
        have hch : (0 : ℝ) ≤ j.choose t := Nat.cast_nonneg _
        calc (j.choose t : ℝ) * ‖iteratedFDeriv ℝ t chi v‖ *
              ‖r26t8a_nest i (j - t) (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) Y v‖
            ≤ (j.choose t : ℝ) * Dχ * (B * (T3 * jbracket Y ^ (2 * M))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) (h2.trans (mul_le_mul_of_nonneg_left h3 hB))
                (norm_nonneg _) (by positivity)
          _ = (j.choose t : ℝ) * (Dχ * (T3 * B * jbracket Y ^ (2 * M))) := by ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hsum : (∑ t ∈ Finset.range (j + 1), (j.choose t : ℝ)) = 2 ^ j := by exact_mod_cast Nat.sum_range_choose j
      rw [hsum]
      have h2k : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      have hR0 : 0 ≤ Dχ * (T3 * B * jbracket Y ^ (2 * M)) := by have := hjb0 Y; positivity
      calc (2 : ℝ) ^ j * (Dχ * (T3 * B * jbracket Y ^ (2 * M))) ≤ 2 ^ k * (Dχ * (T3 * B * jbracket Y ^ (2 * M))) :=
            mul_le_mul_of_nonneg_right h2k hR0
        _ = (2 ^ k * Dχ * T3 * B) * jbracket Y ^ (2 * M) := by ring
    · rw [r26t8a_nest_eq_zero i j srcP Y v ?_, norm_zero]
      · have := hjb0 Y; positivity
      · filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (show (2 : ℝ) < ‖v‖ by linarith [not_le.1 hv])]
          with w hw Y'
        exact hSv Y' w hw
  have hBs0 : 0 ≤ 2 ^ k * Dχ * T3 * B := by positivity
  -- the potential `Sfun` as a sheared `Wg`
  have hS : (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi P Yw.1 Yw.2) =
      fun Yw : Euc d × Euc d => r26t8a_Wg alpha srcP (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2) Yw.2 := by
    funext Yw
    unfold r26t8a_Sfun r26t8a_Wg
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hsrcP, midPair]
    have e1 : Yw.1 + (-(1 / 2 : ℝ)) • Yw.2 + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = Yw.1 + (-(1 / 2 : ℝ)) • Yw.2 + v := by module
    have e2 : Yw.1 + (-(1 / 2 : ℝ)) • Yw.2 + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = Yw.1 + (-(1 / 2 : ℝ)) • Yw.2 := by module
    rw [e1, e2]
  have hmid : (fun Yw : Euc d × Euc d => midPair (r26t8a_localRiesz alpha chi P) Yw.1 Yw.2) =
      fun Yw => chi Yw.2 * r26t8a_Sfun alpha chi P Yw.1 Yw.2 := funext fun Yw => r26t8a_pu_midPair_localRiesz alpha chi P Yw.1 Yw.2
  have hSsm : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi P Yw.1 Yw.2) := by
    rw [hS]
    have hW := r26t8a_Wg_contDiff d hd alpha halpha had srcP (n := p + q) (hsrc_cd.of_le (by exact_mod_cast hpq)) hSv
    exact hW.comp ((contDiff_fst.add (contDiff_snd.const_smul (-(1 / 2 : ℝ)))).prodMk contDiff_snd)
  rw [hmid]
  by_cases hz : ‖z‖ ≤ 2
  · refine (r26t8a_nest_product_bound p q chi _ X z (hchic _) hSsm).trans ?_
    have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi P Yw.1 Yw.2) X z‖ ≤
        (q.choose i : ℝ) * (Dχ * (Cv * (2 ^ k * Dχ * T3 * B) * jbracket X ^ (2 * M))) := by
      intro i hi
      have hiq : i ≤ q := by rw [Finset.mem_range] at hi; omega
      have h1 := hDχ i (by omega) z
      have h2 := hCv srcP hsrc_cd hSv _ hBs0 hbdsrc X z (by linarith) p (q - i) (by omega)
      rw [hS]
      have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
      calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
            ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Wg alpha srcP (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2) Yw.2) X z‖
          ≤ (q.choose i : ℝ) * Dχ * (Cv * (2 ^ k * Dχ * T3 * B) * jbracket X ^ (2 * M)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _) (by positivity)
        _ = (q.choose i : ℝ) * (Dχ * (Cv * (2 ^ k * Dχ * T3 * B) * jbracket X ^ (2 * M))) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hsum : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) = 2 ^ q := by exact_mod_cast Nat.sum_range_choose q
    rw [hsum]
    have h2k : (2 : ℝ) ^ q ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have hjbX := hjb0 X
    have hR0 : 0 ≤ Dχ * (Cv * (2 ^ k * Dχ * T3 * B) * jbracket X ^ (2 * M)) := by positivity
    have hjw := r26t8a_jb_le_pairWeight hM X z hz
    have hpw := hpw0 X z
    calc (2 : ℝ) ^ q * (Dχ * (Cv * (2 ^ k * Dχ * T3 * B) * jbracket X ^ (2 * M)))
        ≤ 2 ^ k * (Dχ * (Cv * (2 ^ k * Dχ * T3 * B) * jbracket X ^ (2 * M))) := mul_le_mul_of_nonneg_right h2k hR0
      _ = (2 ^ k * Dχ * Cv * (2 ^ k * Dχ * T3 * B)) * jbracket X ^ (2 * M) := by ring
      _ ≤ (2 ^ k * Dχ * Cv * (2 ^ k * Dχ * T3 * B)) * (T3 * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) :=
          mul_le_mul_of_nonneg_left hjw (by positivity)
      _ = 2 ^ k * Dχ * Cv * (2 ^ k * Dχ * T3) * T3 * B * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by ring
  · rw [r26t8a_nest_eq_zero p q _ X z ?_, norm_zero]
    · have := hpw0 X z; positivity
    · filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (show (2 : ℝ) < ‖z‖ by linarith [not_le.1 hz])]
        with w hw Y
      simp only [hchi.2.2.2.2 w hw.le, zero_mul]

end HRS.MS.R26T8A
