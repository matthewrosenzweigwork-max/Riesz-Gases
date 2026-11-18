import HRS.MS.R26T8AP11a4
import HRS.MS.R26T8AP11h

/-!
# S8.2 T8A packet P11 (helper b1): conormal functions of `y` alone, and monotonicity in the log degree
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conormal_mono_b {k b b' : ℕ} {M σ A : ℝ} (hA : 0 ≤ A) (hb : b ≤ b') {F : Euc d → Euc d → ℝ}
    (hF : Conormal k b M σ A F) : Conormal k b' M σ A F := by
  refine ⟨hF.1, fun p q hpq X z hz => ?_⟩
  refine (hF.2 p q hpq X z hz).trans ?_
  have hW : 0 ≤ HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    simp only [HRS.MS.Phase2S82.pairWeight]
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr0 : 0 < min 1 ‖z‖ := lt_min one_pos hz0
  have h1 : 1 ≤ 1 + |Real.log (min 1 ‖z‖)| := by linarith [abs_nonneg (Real.log (min 1 ‖z‖))]
  have hpow : (1 + |Real.log (min 1 ‖z‖)|) ^ b ≤ (1 + |Real.log (min 1 ‖z‖)|) ^ b' := pow_le_pow_right₀ h1 hb
  have h2 := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hr0.le (-(σ + (q : ℝ))))
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hW)

theorem r26t8a_conormal_of_snd {k b : ℕ} {M σ B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) {r : Euc d → ℝ}
    (hr : ContDiff ℝ (k : WithTop ℕ∞) r) (hj : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j r y‖ ≤ B * jbracket y ^ M) :
    Conormal k b M σ (2 ^ k * B) (fun _ y => r y) := by
  have hu : Function.uncurry (fun (_ : Euc d) (y : Euc d) => r y) = r ∘ (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) := rfl
  refine r26t8a_conormal_of_smooth hB (by rw [hu]; exact hr.comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).contDiff)
    (fun j hjk x y => ?_)
  rw [hu]
  have hcomp := (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).iteratedFDeriv_comp_right (n := (k : WithTop ℕ∞))
    (f := r) hr (x := (x, y)) (i := j) (by exact_mod_cast hjk)
  rw [hcomp]
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j r ((ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) (x, y)))
    (fun _ : Fin j => ContinuousLinearMap.snd ℝ (Euc d) (Euc d))
  have hs : ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ (Euc d) (Euc d)
  have hs' : ∏ _i : Fin j, ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 := by
    simpa using pow_le_one₀ (norm_nonneg _) hs (n := j)
  refine h1.trans ?_
  have h2 := hj j hjk y
  have hjx : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
  have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  have h3 : ‖iteratedFDeriv ℝ j r ((ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) (x, y))‖ ≤ B * jbracket y ^ M := h2
  calc _ ≤ (B * jbracket y ^ M) * 1 :=
        mul_le_mul h3 hs' (by positivity) (by positivity)
    _ = B * jbracket y ^ M := mul_one _
    _ ≤ B * HRS.MS.Phase2S82.pairWeight M x y := by
        simp only [HRS.MS.Phase2S82.pairWeight]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hB

end HRS.MS.R26T8A
