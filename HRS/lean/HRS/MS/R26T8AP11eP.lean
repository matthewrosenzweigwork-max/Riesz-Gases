import HRS.MS.R26T8AP11e
import HRS.MS.R26T8AP11snP

/-!
# S8.2 nonlocal layer: the local Riesz gain for the PURE conormal class (any sign of the order)
Copies of the `Conormal`/`0 <= sigma` versions with `ConormalP` (see `R26T8AP01p`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_local_riesz_gainP (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → ConormalP k b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun v => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y)) ∧
      Conormal k (b + 1) M (sigma - alpha) (C * A) (r26t8a_localRiesz alpha chi F) := by
  obtain ⟨CS, hCS0, hCS⟩ := r26t8a_Sfun_nestP d hd k b alpha M sigma halpha had hM hsd chi hchi
  obtain ⟨D, hD0, hD⟩ := r26t8a_chi_jet_bound hchi k
  set K : ℝ := 1 + 2 ^ (b + 1) * 2 ^ (|alpha - sigma| + k) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨3 ^ (2 * M) * (2 ^ k * (D * (CS * K))), by positivity, ?_⟩
  intro F A hA hF
  have hFc : Conormal k b M sigma A F := hF.toConormal hA
  refine ⟨fun x y hxy => r26t8a_loc_integrand_integrable d hd k b alpha M sigma halpha had hM hsd chi hchi
    A hA F hFc x y hxy, And.intro (r26t8a_localRiesz_contDiffOn d hd k b alpha M sigma halpha had hM hsd chi
    hchi A hA F hFc) ?_⟩
  intro p q hpq X z hz
  have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hlb := r26t8a_mid_nest_leibniz d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F hFc X z hz p q hpq
  have hmj : mixedJet p q (r26t8a_localRiesz alpha chi F) X z = r26t8a_nest p q
      (fun Yw : Euc d × Euc d => midPair (r26t8a_localRiesz alpha chi F) Yw.1 Yw.2) X z := rfl
  rw [hmj]
  set Env : ℝ := 1 + (min 1 ‖z‖) ^ (-((sigma - alpha) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) with hEnv
  have hEnv0 : 0 ≤ Env := by rw [hEnv]; positivity
  have hCA : 0 ≤ 3 ^ (2 * M) * (2 ^ k * (D * (CS * K))) * A := by positivity
  by_cases hz2 : ‖z‖ < 2
  · have hjb := r26t8a_jb_le_pairWeight hM X z hz2.le
    have hJ0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
    have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ ≤
        (q.choose i : ℝ) * (D * (CS * A * jbracket X ^ (2 * M) * K * Env)) := by
      intro i hi
      have hiq : i ≤ q := by rw [Finset.mem_range] at hi; omega
      have h1 := hCS F A hA hF X z hz hz2 p (q - i) (by omega)
      have h2 := hD i (by omega) z
      have h3 := r26t8a_env_shift b k alpha sigma q i hiq (by omega) ‖z‖ (norm_pos_iff.2 hz) hz2
      have hS0 : 0 ≤ CS * A * jbracket X ^ (2 * M) := by positivity
      have h4 : ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ ≤
          CS * A * jbracket X ^ (2 * M) * K * Env :=
        h1.trans (by
          calc CS * A * jbracket X ^ (2 * M) * (1 + ‖z‖ ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) *
                (1 + |Real.log ‖z‖|) ^ (b + 1))
              ≤ CS * A * jbracket X ^ (2 * M) * (K * Env) := mul_le_mul_of_nonneg_left h3 hS0
            _ = CS * A * jbracket X ^ (2 * M) * K * Env := by ring)
      have hch : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
      calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
            ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖
          ≤ (q.choose i : ℝ) * D * (CS * A * jbracket X ^ (2 * M) * K * Env) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 hch) h4 (norm_nonneg _) (by positivity)
        _ = (q.choose i : ℝ) * (D * (CS * A * jbracket X ^ (2 * M) * K * Env)) := by ring
    refine hlb.trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul]
    have hchoose : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) ≤ 2 ^ k := by
      have : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q := by exact_mod_cast Nat.sum_range_choose q
      rw [this]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hR0 : 0 ≤ D * (CS * A * jbracket X ^ (2 * M) * K * Env) := by positivity
    calc (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)) * (D * (CS * A * jbracket X ^ (2 * M) * K * Env))
        ≤ 2 ^ k * (D * (CS * A * jbracket X ^ (2 * M) * K * Env)) := mul_le_mul_of_nonneg_right hchoose hR0
      _ = 2 ^ k * (D * (CS * A * K * Env)) * jbracket X ^ (2 * M) := by ring
      _ ≤ 2 ^ k * (D * (CS * A * K * Env)) * (3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) :=
          mul_le_mul_of_nonneg_left hjb (by positivity)
      _ = 3 ^ (2 * M) * (2 ^ k * (D * (CS * K))) * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * Env := by
          ring
  · push Not at hz2
    refine hlb.trans (le_trans (le_of_eq ?_) (by positivity))
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [r26t8a_chi_jet_zero hchi i hz2]
    simp

end HRS.MS.R26T8A
