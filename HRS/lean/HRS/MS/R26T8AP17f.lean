import HRS.MS.R26T8AP17e

/-!
# S8.2 local Newton layer, packet T8A.P17 (part f): `Conormal k 0 0 (criticalS d) (C*A) (hSource f)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_p17_h_conormal (hd : 2 ≤ d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ f : Euc d → ℝ, TestBound (k + 2) A f →
      Conormal k 0 0 (criticalS d) (C * A) (hSource f) := by
  obtain ⟨Cu, hCu0, hCu⟩ := r26t8a_p17_force_jets hd k
  refine ⟨2 ^ (k + 1) * Cu, by positivity, fun A hA f hf => ?_⟩
  refine And.intro ((r26t8a_p17_h_contDiffOn hd hf).of_le (by exact_mod_cast le_top)) fun p q hpq X z hz => ?_
  set s : ℝ := criticalS d with hs
  have hs0 : 0 < s := r26t8a_p17_s_pos hd
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  set r : ℝ := ‖z‖ with hrdef
  have hGc : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_p17_G f) := by
    have hg := r26t8a_p17_grad_contDiff hf.1
    have hgp : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (gradient f) := contDiff_infty.1 hg (p + q)
    have l1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => gradient f (Yw.1 + (1 / 2 : ℝ) • Yw.2)) :=
      hgp.comp (contDiff_fst.add (contDiff_snd.const_smul _))
    have l2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => gradient f (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2)) :=
      hgp.comp (contDiff_fst.add (contDiff_snd.const_smul _))
    exact l1.sub l2
  have huc : ContDiffOn ℝ ((p + q : ℕ) : WithTop ℕ∞) (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) {w : Euc d | w ≠ 0} :=
    fun w hw => ((r26t8a_p17_g_contDiffAt hd hw).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hmj : mixedJet p q (hSource f) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => (ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ))
        (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d)) Yw.2) (r26t8a_p17_G f Yw)) X z := by
    show r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (hSource f) Yw.1 Yw.2) X z = _
    congr 1
    funext Yw
    exact r26t8a_p17_mid_eq hd f Yw.1 Yw.2
  rw [hmj]
  refine (r26t8a_p17_local_bilinear (ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)) p q huc hGc X z hz).trans ?_
  have hB1 : ‖ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hA0 := hA
  set ρ : ℝ := min 1 r with hρ
  have hρ0 : 0 < ρ := lt_min zero_lt_one hr
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  -- the envelope
  set E : ℝ := 1 + ρ ^ (-(s + (q : ℝ))) * (1 + |Real.log ρ|) ^ 0 with hE
  have hE1 : 1 ≤ E := by
    rw [hE]; simp only [pow_zero, mul_one]
    have := Real.rpow_nonneg hρ0.le (-(s + (q : ℝ)))
    linarith
  have hEρ : ρ ^ (-(s + (q : ℝ))) ≤ E := by rw [hE]; simp only [pow_zero, mul_one]; linarith
  -- each term of the Leibniz sum
  have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i
        (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) z‖ * ‖r26t8a_nest p (q - i) (r26t8a_p17_G f) X z‖ ≤
      (q.choose i : ℝ) * (2 * Cu * A * E) := by
    intro i hi
    have hiq : i ≤ q := by have := Finset.mem_range.1 hi; omega
    have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
    have h1 := hCu i (by omega) z hz
    have hGb := r26t8a_p17_G_bound hf p (q - i) (by omega) X z
    have hCuA : 0 ≤ Cu * A := mul_nonneg hCu0 hA
    have hrpow : 0 ≤ r ^ (-criticalS d - 1 - (i : ℝ)) := Real.rpow_nonneg hr.le _
    -- the key inequality  ‖D^i u‖ * ‖nest‖ <= 2 Cu A E
    have key : ‖iteratedFDeriv ℝ i (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) z‖ *
        ‖r26t8a_nest p (q - i) (r26t8a_p17_G f) X z‖ ≤ 2 * Cu * A * E := by
      by_cases hiq' : i < q
      · calc _ ≤ (Cu * r ^ (-criticalS d - 1 - (i : ℝ))) * (2 * A) :=
              mul_le_mul h1 hGb (norm_nonneg _) (by positivity)
          _ = 2 * (Cu * A) * r ^ (-criticalS d - 1 - (i : ℝ)) := by ring
          _ ≤ 2 * (Cu * A) * E := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              by_cases hr1 : r ≤ 1
              · have hρr : ρ = r := min_eq_right hr1
                have : r ^ (-criticalS d - 1 - (i : ℝ)) ≤ r ^ (-(s + (q : ℝ))) := by
                  refine Real.rpow_le_rpow_of_exponent_ge hr hr1 ?_
                  have : (i : ℝ) + 1 ≤ q := by exact_mod_cast hiq'
                  rw [hs]; linarith
                rw [hρr] at hEρ
                exact this.trans hEρ
              · push Not at hr1
                have : r ^ (-criticalS d - 1 - (i : ℝ)) ≤ 1 :=
                  Real.rpow_le_one_of_one_le_of_nonpos hr1.le (by
                    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
                    linarith)
                linarith
          _ = 2 * Cu * A * E := by ring
      · have hiq2 : i = q := le_antisymm hiq (not_lt.1 hiq')
        have hq0 : q - i = 0 := by omega
        have hiR : (i : ℝ) = q := by exact_mod_cast hiq2
        have hgain := r26t8a_p17_G_gain hf p (by omega) X z
        rw [hq0]
        calc _ ≤ (Cu * r ^ (-criticalS d - 1 - (i : ℝ))) * (A * r) :=
              mul_le_mul h1 hgain (norm_nonneg _) (by positivity)
          _ = (Cu * A) * (r ^ (-criticalS d - 1 - (i : ℝ)) * r) := by ring
          _ = (Cu * A) * r ^ (-criticalS d - (i : ℝ)) := by
              congr 1
              rw [show -criticalS d - (i : ℝ) = (-criticalS d - 1 - (i : ℝ)) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
          _ ≤ (Cu * A) * E := by
              refine mul_le_mul_of_nonneg_left ?_ hCuA
              by_cases hr1 : r ≤ 1
              · have hρr : ρ = r := min_eq_right hr1
                rw [hρr] at hEρ
                have : r ^ (-criticalS d - (i : ℝ)) = r ^ (-(s + (i : ℝ))) := by
                  congr 1; rw [hs]; ring
                rw [this, hiR]; exact hEρ
              · push Not at hr1
                have : r ^ (-criticalS d - (i : ℝ)) ≤ 1 :=
                  Real.rpow_le_one_of_one_le_of_nonpos hr1.le (by
                    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
                    linarith)
                linarith
          _ ≤ 2 * Cu * A * E := by nlinarith [mul_nonneg hCuA (by linarith : (0 : ℝ) ≤ E)]
    calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) z‖ *
          ‖r26t8a_nest p (q - i) (r26t8a_p17_G f) X z‖
        = (q.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) z‖ *
          ‖r26t8a_nest p (q - i) (r26t8a_p17_G f) X z‖) := by ring
      _ ≤ (q.choose i : ℝ) * (2 * Cu * A * E) := mul_le_mul_of_nonneg_left key hch
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul, show ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q by exact_mod_cast Nat.sum_range_choose q] at hsum
  have hpw : pairWeight 0 (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) = 1 := by
    unfold pairWeight; simp
  rw [hpw]
  calc ‖ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)‖ * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i
        (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) z‖ * ‖r26t8a_nest p (q - i) (r26t8a_p17_G f) X z‖
      ≤ 1 * (2 ^ q * (2 * Cu * A * E)) := by
        refine mul_le_mul hB1 hsum (Finset.sum_nonneg fun i _ => by positivity) zero_le_one
    _ ≤ 2 ^ (k + 1) * Cu * A * 1 * E := by
        have h2q : (2 : ℝ) ^ q * 2 ≤ 2 ^ (k + 1) := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hCuA : 0 ≤ Cu * A := mul_nonneg hCu0 hA
        have : (2 : ℝ) ^ q * (2 * Cu * A * E) = ((2 : ℝ) ^ q * 2) * (Cu * A * E) := by ring
        rw [one_mul, this]
        calc ((2 : ℝ) ^ q * 2) * (Cu * A * E) ≤ 2 ^ (k + 1) * (Cu * A * E) :=
              mul_le_mul_of_nonneg_right h2q (by positivity)
          _ = 2 ^ (k + 1) * Cu * A * 1 * E := by ring
    _ = _ := by simp only [hE]

end HRS.MS.R26T8A
