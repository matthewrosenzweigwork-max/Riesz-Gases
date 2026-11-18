import HRS.MS.R26T8AR4a
import HRS.MS.R26T8AR3a
import HRS.MS.R26T8AP17
import HRS.MS.R26T8AP21

/-!
# S8.2 T8A R4b: conormal classes of the source `F_0 = HSource`, its leading part `Lead = src f` and the remainder `E' = F_0 - Lead`
`F_0, Lead ∈ Conormal 8 0 0 s`, `E' ∈ Conormal 8 0 0 (s-2)` (`s = criticalS d`), constants uniform in the thermal density.
`HSource = (1/2) center(hSource f)`, `(1/2) hSource f = P21lead + src f`; the centring correction is smooth (R4a).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

theorem r26t8a_R4_src_eq (f : Euc d → ℝ) (x y : Euc d) :
    r26t8a_R3_src f x y = (1 / 2 : ℝ) * hSource f x y - r26t8a_lead f x y := by
  unfold r26t8a_R3_src r26t8a_lead s82n_critS criticalS
  ring

set_option maxHeartbeats 3200000 in
theorem r26t8a_R4_lead_classes (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      Conormal 8 0 0 (criticalS d) (C * A) (HSource (HRS.Whole.withDensityReal rho) f) ∧
      Conormal 8 0 0 (criticalS d - 2) (C * A)
        (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y) ∧
      Conormal 8 0 0 (criticalS d) (C * A) (r26t8a_R3_src f) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨C17, hC170, h17⟩ := r26t8a_source_conormal d hd a beta ha hbeta
  obtain ⟨C21, hC210, h21⟩ := r26t8a_leading_source d hd 8
  obtain ⟨Ch, hCh0, hCh⟩ := r26t8a_p17_h_conormal hd 8
  obtain ⟨CC, hCC0, hCC⟩ := r26t8a_R4_center_smooth hchi hd a beta ha hbeta 8 0 (σ := criticalS d) (M := 0) le_rfl hsd
  set KE : ℝ := 2 ^ 8 * (((8 : ℕ) + 1 : ℝ) ^ 2 * |(1 / 2 : ℝ)| * (CC * Ch)) + C21 with hKE
  have hKE0 : 0 ≤ KE := by rw [hKE]; positivity
  refine ⟨C17 + KE + (C17 + 2 ^ 8 * ((((8 : ℕ) : ℝ) + 1) ^ 2 * KE)), by positivity, fun rho hrho f A hA hf => ?_⟩
  obtain ⟨-, -, hF0⟩ := h17 rho hrho f A hA hf
  have hF0' : Conormal 8 0 0 (criticalS d) (C17 * A) (HSource (HRS.Whole.withDensityReal rho) f) :=
    r26t8a_conormal_mono (by unfold iterationCount; omega) hF0
  have hf' : TestBound (8 + 4) A f := ⟨hf.1, fun j hj hjk x => hf.2 j hj (by unfold testOrder; omega) x⟩
  have hf2 : TestBound (8 + 2) A f := ⟨hf.1, fun j hj hjk x => hf.2 j hj (by unfold testOrder; omega) x⟩
  have hL21 := h21 f A hA hf'
  have hh := hCh A hA f hf2
  have hcorr := hCC rho hrho (mul_nonneg hCh0 hA) hh 0 (criticalS d - 2)
  have hcorr' : Conormal 8 0 0 (criticalS d - 2) (CC * Ch * A)
      (fun x y => r2CenterKernel (HRS.Whole.withDensityReal rho) (hSource f) x y - hSource f x y) :=
    r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) le_rfl hcorr
  have hhalf := r26t8a_conormal_const_mul hchi (by positivity : 0 ≤ CC * Ch * A) (1 / 2 : ℝ) hcorr'
  have hE := r26t8a_conormal_add hchi hhalf hL21
  have hE' : Conormal 8 0 0 (criticalS d - 2) (KE * A)
      (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y) := by
    refine r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by rw [hKE]; ring)) le_rfl
      (r26t8a_conormal_congr (fun x y _ => ?_) hE)
    rw [r26t8a_R4_src_eq]
    unfold HSource r26t8a_lead
    ring
  have hE's : Conormal 8 0 0 (criticalS d) (KE * A)
      (fun x y => HSource (HRS.Whole.withDensityReal rho) f x y - r26t8a_R3_src f x y) :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (by linarith) hE'
  have hLead := r26t8a_conormal_sub hchi (by positivity : 0 ≤ C17 * A) (by positivity : 0 ≤ KE * A) hF0' hE's
  refine ⟨?_, ?_, ?_⟩
  · exact r26t8a_conormal_mono_sA (by positivity) (by nlinarith [mul_nonneg hC170 hA, mul_nonneg hKE0 hA]) le_rfl hF0'
  · exact r26t8a_conormal_mono_sA (by positivity) (by nlinarith [mul_nonneg hC170 hA, mul_nonneg hKE0 hA]) le_rfl hE'
  · refine r26t8a_conormal_mono_sA (by positivity) ?_ le_rfl
      (r26t8a_conormal_congr (fun x y _ => ?_) hLead)
    · have : C17 * A + 2 ^ 8 * ((((8 : ℕ) : ℝ) + 1) ^ 2 * (KE * A)) =
          (C17 + 2 ^ 8 * ((((8 : ℕ) : ℝ) + 1) ^ 2 * KE)) * A := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hA
    · ring

end HRS.MS.R26T8A
