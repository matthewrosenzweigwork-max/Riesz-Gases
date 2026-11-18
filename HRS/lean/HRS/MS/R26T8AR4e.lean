import HRS.MS.R26T8AR4d
import HRS.MS.R26T8AR3e

/-!
# S8.2 T8A R4e: sharp mixed jets of order `≤ 2` of the Newton potential `R_L = rawNewton β⁻¹ χ (src f)` of the leading source
`r26t8a_R4_RL_jets`: `‖mixedJet p q R_L X z‖ ≤ C A w (1 + r^(-((s-2)+q)) + [q=0][d=4] |log r|)`, `r = min 1 |z|`, `p + q ≤ 2`.
For `|z| < 1` the jets are the nested jets of `Φ(Y,w) = LI(D²f(Y))(w) + S0(D²f(Y))(w)` (R3a, R3e); for `|z| ≥ 1` the conormal class (R4d) gives a bounded envelope.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

theorem r26t8a_R4_norm_D2 {f : Euc d → ℝ} {A : ℝ} {k : ℕ} (hf : TestBound k A f) (p : ℕ) (hp : p + 2 ≤ k) (X : Euc d) :
    ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ ≤ A := by
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ f) (x := X) (n := p)
  have h2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := X) (n := p + 1)
  rw [h1, h2]
  exact hf.2 (p + 2) (by omega) hp X

set_option maxHeartbeats 3200000 in
theorem r26t8a_R4_RL_jets (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ)
    (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      ∀ (p q : ℕ), p + q ≤ 2 → ∀ X z : Euc d, z ≠ 0 →
      ‖mixedJet p q (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) X z‖ ≤
        C * A * HRS.MS.Phase2S82.pairWeight (2 * (iterationCount d : ℝ))
          (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (1 + (min 1 ‖z‖) ^ (-((criticalS d - 2) + (q : ℝ))) +
          if q = 0 then (if d = 4 then |Real.log (min 1 ‖z‖)| else 0) else 0) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C3, hC30, hC3⟩ := r26t8a_R3_nest_Phi hd beta⁻¹ (inv_pos.2 hbeta) hchi
  obtain ⟨C4, hC40, hC4⟩ := r26t8a_R4_W_class hd a beta ha hbeta chi hchi
  refine ⟨C3 + 2 * C4, by positivity, fun rho hrho f A hA hf p q hpq X z hz => ?_⟩
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set M : ℝ := 2 * (iterationCount d : ℝ) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  set w : ℝ := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hw
  have hw1 : 1 ≤ w := by
    have h1 : 1 ≤ jbracket (X + (1 / 2 : ℝ) • z) ^ M := Real.one_le_rpow (s83_one_le_jb _) hM0
    have h2 : 1 ≤ jbracket (X - (1 / 2 : ℝ) • z) ^ M := Real.one_le_rpow (s83_one_le_jb _) hM0
    rw [hw]; unfold HRS.MS.Phase2S82.pairWeight; nlinarith
  set r : ℝ := min 1 ‖z‖ with hr
  have hr0 : 0 < r := lt_min one_pos hzn
  set env : ℝ := 1 + r ^ (-((criticalS d - 2) + (q : ℝ))) +
    (if q = 0 then (if d = 4 then |Real.log r| else 0) else 0) with henv
  have henv1 : 1 ≤ env := by
    have h1 : 0 ≤ r ^ (-((criticalS d - 2) + (q : ℝ))) := Real.rpow_nonneg hr0.le _
    have h2 : 0 ≤ (if q = 0 then (if d = 4 then |Real.log r| else (0 : ℝ)) else 0) := by
      split_ifs <;> positivity
    rw [henv]; linarith
  have hCA : 0 ≤ (C3 + 2 * C4) * A := mul_nonneg (by positivity) hA
  by_cases hz1 : ‖z‖ < 1
  · -- small `z`: nested jets of Φ
    have hrz : r = ‖z‖ := min_eq_right hz1.le
    have hfs : ContDiff ℝ ∞ f := hf.1
    have hnest := hC3 f hfs X z hz hz1.le p q (by omega)
    have hD := r26t8a_R4_norm_D2 hf p (by unfold testOrder; omega) X
    have hid : mixedJet p q (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) X z =
        r26t8a_nest p q (fun Yw : Euc d × Euc d =>
          s82n_leadingInverse beta⁻¹ (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2 +
            r26t8a_p22_S0 beta⁻¹ chi (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2) X z := by
      show r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) Yw.1 Yw.2) X z = _
      have hρ : 0 < min (‖z‖ / 2) ((1 - ‖z‖) / 2) := lt_min (by linarith) (by linarith)
      refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
      have hw1 : ‖w‖ < 1 := by
        have h1 := norm_le_norm_add_norm_sub' w z
        have h2 := min_le_right (‖z‖ / 2) ((1 - ‖z‖) / 2)
        linarith
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, zero_sub, norm_neg] at hw
        have h2 := min_le_left (‖z‖ / 2) ((1 - ‖z‖) / 2)
        linarith
      have hxy : Y + (1 / 2 : ℝ) • w ≠ Y - (1 / 2 : ℝ) • w := by
        intro h
        apply hw0
        have : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
        rw [← this, h, sub_self]
      have e1 : ‖(Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w)‖ < 1 := by
        have : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
        rw [this]; exact hw1
      have h := r26t8a_R3_raw_eq hd beta⁻¹ (inv_pos.2 hbeta) hchi hfs hxy e1
      have e2 : (1 / 2 : ℝ) • ((Y + (1 / 2 : ℝ) • w) + (Y - (1 / 2 : ℝ) • w)) = Y := by module
      have e3 : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
      rw [e2, e3] at h
      exact h
    rw [hid]
    refine hnest.trans ?_
    have e : ‖z‖ ^ (-((s82n_critS d - 2) + (q : ℝ))) = r ^ (-((criticalS d - 2) + (q : ℝ))) := by
      rw [hrz]; rfl
    have e' : (if q = 0 then (if d = 4 then |Real.log ‖z‖| else 0) else 0) =
        (if q = 0 then (if d = 4 then |Real.log r| else 0) else 0) := by rw [hrz]
    rw [e, e']
    have hEn : 0 ≤ env := by linarith
    calc C3 * ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ * env
        ≤ C3 * A * env := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hC30) hEn
      _ ≤ (C3 + 2 * C4) * A * w * env := by
          have h1 : 0 ≤ C4 * A := mul_nonneg hC40 hA
          have h2 : 0 ≤ C3 * A := mul_nonneg hC30 hA
          nlinarith [mul_nonneg h2 (sub_nonneg.2 hw1), mul_nonneg h1 hEn, mul_nonneg (mul_nonneg h2 (sub_nonneg.2 hw1)) hEn,
            mul_nonneg (mul_nonneg h1 (sub_nonneg.2 hw1)) hEn]
  · -- large `z`: the conormal class
    have hr1 : min 1 ‖z‖ = 1 := min_eq_left (not_lt.1 hz1)
    obtain ⟨hRL, -⟩ := hC4 rho hrho f A hA hf
    have hb := hRL.2 p q (by omega) X z hz
    have hb' : ‖mixedJet p q (rawNewton beta⁻¹ chi (r26t8a_R3_src f)) X z‖ ≤ C4 * A * w * 2 := by
      rw [hr1] at hb
      simp only [Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one] at hb
      linarith
    have hw0 : 0 ≤ C4 * A * w := mul_nonneg (mul_nonneg hC40 hA) (by linarith)
    refine hb'.trans ?_
    have h1 : 0 ≤ C3 * A * w := mul_nonneg (mul_nonneg hC30 hA) (by linarith)
    nlinarith [mul_nonneg hw0 (sub_nonneg.2 henv1), mul_nonneg h1 (sub_nonneg.2 henv1)]

end HRS.MS.R26T8A
