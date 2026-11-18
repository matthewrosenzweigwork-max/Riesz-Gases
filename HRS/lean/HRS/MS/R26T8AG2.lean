import HRS.MS.R26T8AG1
import HRS.MS.R26T8AP06tb
import HRS.MS.R26T8AP11eP

/-!
# S8.2 sigma<0 assembly (G), step 2: the local Riesz gain for `sigma < 0` and for both signs
`r26t8a_local_riesz_gain_neg`: `σ < 0`, `m < -σ <= m+1`, `Conormal (k+1+m+1) b M σ A F` ⇒ integrability and
`Conormal k (b+1) M (σ-α) (C*A) (localRiesz α chi F)` (the same-`k` statement of the T8A contract is not reachable, see HANDOFF_S82PB.md).
`r26t8a_local_riesz_gain_full`: both signs with the regularity `r26t8a_gainReg k σ` (`= k` for `σ >= 0`, `= k+1+m+1` for `σ < 0`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_local_riesz_gain_neg (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hσ : sigma < 0)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (m : ℕ) (hm : (m : ℝ) < -sigma) (hm1 : -sigma ≤ (m : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (k + 1 + m + 1) b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun v => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y)) ∧
      Conormal k (b + 1) M (sigma - alpha) (C * A) (r26t8a_localRiesz alpha chi F) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsd : sigma < d := lt_trans hσ hd0
  obtain ⟨Ct, hCt0, hCt⟩ := r26t8a_taylor_split hd hchi k b M sigma hM hσ m hm hm1
  obtain ⟨Cg, hCg0, hCg⟩ := r26t8a_local_riesz_gainP d hd k b alpha M sigma halpha had hM hsd chi hchi
  obtain ⟨Cq, hCq0, hCq⟩ := r26t8a_localRiesz_smooth_jets d hd k alpha M halpha had hM chi hchi
  refine ⟨(Cg + Cq) * Ct, by positivity, ?_⟩
  intro F A hA hF
  obtain ⟨P, hPcd, hFP, hPjet⟩ := hCt A hA F hF
  have hA1 : 0 ≤ Ct * A := mul_nonneg hCt0 hA
  have hpw0 : ∀ X z : Euc d, 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := fun X z =>
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hPcd' : ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry P) := hPcd.of_le (by exact_mod_cast Nat.le_succ k)
  have hPcon : Conormal k 0 M 0 (Ct * A) P := by
    refine And.intro hPcd'.contDiffOn fun p q hpq X z hz => ?_
    refine (hPjet p q hpq X z).trans ?_
    have h0 : 0 ≤ Ct * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := mul_nonneg hA1 (hpw0 X z)
    have h1 : 0 ≤ (min 1 ‖z‖) ^ (-((0 : ℝ) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ 0 := by
      have : 0 ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
      positivity
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + (min 1 ‖z‖) ^ (-((0 : ℝ) + (q : ℝ))) *
      (1 + |Real.log (min 1 ‖z‖)|) ^ 0 by linarith) h0
    simpa [mul_assoc] using this
  obtain ⟨hintFP, hGFP⟩ := hCg (fun x y => F x y - P x y) (Ct * A) hA1 hFP
  have hintP : ∀ x y : Euc d, x ≠ y → Integrable (fun v : Euc d => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * P (y + v) y) :=
    fun x y hxy => r26t8a_loc_integrand_integrable d hd k 0 alpha M 0 halpha had hM hd0 chi hchi (Ct * A) hA1 P hPcon x y hxy
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have := (hintFP x y hxy).add (hintP x y hxy)
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    try simp only [Pi.add_apply]
    ring
  · have hLPsm := r26t8a_localRiesz_contDiffOn d hd k 0 alpha M 0 halpha had hM hd0 chi hchi (Ct * A) hA1 P hPcon
    have hLP : Conormal k (b + 1) M (sigma - alpha) (Cq * (Ct * A)) (r26t8a_localRiesz alpha chi P) := by
      refine And.intro hLPsm fun p q hpq X z hz => ?_
      have h := hCq (Ct * A) hA1 P hPcd' hPjet p q hpq X z
      refine h.trans ?_
      have h0 : 0 ≤ Cq * (Ct * A) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
        have := hpw0 X z; positivity
      have h1 : 0 ≤ (min 1 ‖z‖) ^ (-((sigma - alpha) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) := by
        have : 0 ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
        positivity
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + (min 1 ‖z‖) ^ (-((sigma - alpha) + (q : ℝ))) *
        (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) by linarith) h0
      calc _ = Cq * (Ct * A) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * 1 := by ring
        _ ≤ _ := this
    have hsum := r26t8a_conormal_add hchi hGFP hLP
    have hAeq : Cg * (Ct * A) + Cq * (Ct * A) = (Cg + Cq) * Ct * A := by ring
    rw [hAeq] at hsum
    refine r26t8a_conormal_congr (fun x y hxy => ?_) hsum
    unfold r26t8a_localRiesz
    rw [← mul_add, ← integral_add (hintFP x y hxy) (hintP x y hxy)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    try simp only [Pi.add_apply]
    ring

/-- Regularity needed for the local Riesz gain at order `sigma`. -/
def r26t8a_gainReg (k : ℕ) (σ : ℝ) : ℕ := if 0 ≤ σ then k else k + 1 + (⌈-σ⌉₊ - 1) + 1

theorem r26t8a_local_riesz_gain_full (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (r26t8a_gainReg k sigma) b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun v => ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y)) ∧
      Conormal k (b + 1) M (sigma - alpha) (C * A) (r26t8a_localRiesz alpha chi F) := by
  by_cases hσ : 0 ≤ sigma
  · obtain ⟨C, hC0, hC⟩ := r26t8a_local_riesz_gain_nonneg d hd k b alpha M sigma halpha had hM hσ hsd chi hchi
    refine ⟨C, hC0, fun F A hA hF => hC F A hA ?_⟩
    simpa only [r26t8a_gainReg, if_pos hσ] using hF
  · push Not at hσ
    set s : ℝ := -sigma with hs
    have hs0 : 0 < s := by rw [hs]; linarith
    have hceil : 1 ≤ ⌈s⌉₊ := Nat.one_le_iff_ne_zero.2 (by simpa using hs0)
    have hm : ((⌈s⌉₊ - 1 : ℕ) : ℝ) < -sigma := by
      rw [Nat.cast_sub hceil]
      have := Nat.ceil_lt_add_one hs0.le
      push_cast
      linarith
    have hm1 : -sigma ≤ ((⌈s⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hceil]
      have := Nat.le_ceil s
      push_cast
      linarith
    obtain ⟨C, hC0, hC⟩ := r26t8a_local_riesz_gain_neg d hd k b alpha M sigma halpha had hM hσ chi hchi (⌈s⌉₊ - 1) hm hm1
    refine ⟨C, hC0, fun F A hA hF => hC F A hA ?_⟩
    have : r26t8a_gainReg k sigma = k + 1 + (⌈s⌉₊ - 1) + 1 := by
      simp only [r26t8a_gainReg, if_neg (not_le.2 hσ), hs]
    rw [this] at hF
    exact hF

end HRS.MS.R26T8A
