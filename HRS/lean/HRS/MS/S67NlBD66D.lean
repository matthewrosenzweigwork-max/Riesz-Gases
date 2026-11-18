import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63DAux1
import HRS.MS.S67NlBD41
import HRS.MS.S67NlBD54

/-!
# S6.7nl.66D: scalar two-rate convolution retaining the feedback integral
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Exponent-normalised form of the kernel at `a = 1`, with exponent `1/2 - 1`. -/
theorem s67bd_kern66_eq (c t : ℝ) :
    s67bd_kernel 1 c t = (1 + t ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(c * t)) := by
  rw [s67bd_kernel_eq]
  norm_num

/-- The zero extension to `[0, ∞)` of the Beta-type profile with rate `κ`: integrable on `ℝ`. -/
theorem s67bd_ind_int {κ : ℝ} (hκ : 0 < κ) :
    Integrable (Set.indicator (Set.Ici (0 : ℝ))
      (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z)))) volume := by
  rw [integrable_indicator_iff measurableSet_Ici]
  have h := HRS.MS.Mov63.mnd_beta_int (θ := (1:ℝ) / 2) (κ := κ) (by norm_num) hκ
  exact h.congr_set_ae Ioi_ae_eq_Ici.symm

theorem s67bd_ind_nonneg {κ z : ℝ} :
    0 ≤ Set.indicator (Set.Ici (0 : ℝ))
      (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z))) z := by
  unfold Set.indicator
  split_ifs with hz
  · have h0 : (0 : ℝ) ≤ z := hz
    have := Real.rpow_nonneg h0 ((1:ℝ) / 2 - 1)
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · exact le_rfl

/-- Translation-invariant bound: the profile integrated over `[r, T]` after shifting by `r`
is at most the full Beta integral `mndBeta (1/2) κ`. -/
theorem s67bd_trans_le {κ : ℝ} (hκ : 0 < κ) (r T : ℝ) :
    ∫ v in Icc r T, Set.indicator (Set.Ici (0 : ℝ))
      (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z))) (v - r) ≤
      HRS.MS.Mov63.mndBeta ((1:ℝ) / 2) κ := by
  have hint := s67bd_ind_int hκ
  have htr := hint.comp_sub_right r
  calc ∫ v in Icc r T, Set.indicator (Set.Ici (0 : ℝ))
        (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z))) (v - r)
      ≤ ∫ v, Set.indicator (Set.Ici (0 : ℝ))
        (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z))) (v - r) :=
        setIntegral_le_integral htr (Filter.Eventually.of_forall fun v => s67bd_ind_nonneg)
    _ = ∫ z, Set.indicator (Set.Ici (0 : ℝ))
        (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z))) z :=
        integral_sub_right_eq_self (fun z => Set.indicator (Set.Ici (0 : ℝ))
          (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(κ * z))) z) r
    _ = HRS.MS.Mov63.mndBeta ((1:ℝ) / 2) κ := by
        rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
        rfl

/-- S6.7nl.66D: a scalar two-rate Volterra-type conversion with the feedback integral retained. -/
theorem s67bd_two_rate_scalar (Craw Cw lam cw : ℝ)
    (hCr : 0 ≤ Craw) (hCw : 0 ≤ Cw) (hlam : 0 < lam) (hcw : 0 < cw) :
    ∃ C c1 : ℝ, 1 ≤ C ∧ 0 < c1 ∧ c1 ≤ lam ∧
      ∀ T R0 N A : ℝ, 0 ≤ T → 0 ≤ R0 → 0 ≤ N → 0 ≤ A →
      ∀ X Y : ℝ → ℝ,
      (∀ v ∈ Icc (0 : ℝ) T, 0 ≤ X v) → (∀ v ∈ Icc (0 : ℝ) T, 0 ≤ Y v) →
      (∀ v ∈ Icc (0 : ℝ) T, X v ≤ Cw * Real.exp (-cw * (T - v)) * A) →
      (∀ r ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun v => s67bd_kernel 1 lam (v - r) * X v) (Icc r T) volume) →
      (∀ r ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun v => s67bd_kernel 1 lam (v - r) * Y v) (Icc r T) volume) →
      (∀ r ∈ Icc (0 : ℝ) T,
        Y r ≤ Craw * Real.exp (-lam * (T - r)) * N +
          Craw * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * X v) +
          Craw * R0 * ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * Y v) →
      ∀ r ∈ Icc (0 : ℝ) T,
        Y r ≤ C * Real.exp (-c1 * (T - r)) * (N + A) +
          C * R0 * ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * Y v := by
  obtain ⟨c1, hc1, hc1lam, hc1cw⟩ : ∃ c1 : ℝ, 0 < c1 ∧ c1 < lam ∧ c1 < cw :=
    ⟨min lam cw / 2, half_pos (lt_min hlam hcw), by linarith [min_le_left lam cw, min_le_right lam cw],
      by linarith [min_le_left lam cw, min_le_right lam cw]⟩
  have hκ : 0 < lam - c1 := by linarith
  have hK0 : 0 ≤ HRS.MS.Mov63.mndBeta ((1:ℝ) / 2) (lam - c1) :=
    HRS.MS.Mov63.mnd_beta_nonneg _ _
  refine ⟨max 1 (max Craw (Craw * Cw * HRS.MS.Mov63.mndBeta ((1:ℝ) / 2) (lam - c1))), c1,
    le_max_left _ _, hc1, hc1lam.le, ?_⟩
  intro T R0 N A hT hR0 hN hA X Y hX hY hXub hXint hYint hYineq r hr
  obtain ⟨hr0, hrT⟩ := hr
  set K := HRS.MS.Mov63.mndBeta ((1:ℝ) / 2) (lam - c1) with hKdef
  set E := Real.exp (-c1 * (T - r)) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hC1 : Craw ≤ max 1 (max Craw (Craw * Cw * K)) :=
    le_trans (le_max_left Craw (Craw * Cw * K)) (le_max_right 1 _)
  have hC2 : Craw * Cw * K ≤ max 1 (max Craw (Craw * Cw * K)) :=
    le_trans (le_max_right Craw (Craw * Cw * K)) (le_max_right 1 _)
  set C := max 1 (max Craw (Craw * Cw * K)) with hCdef
  -- pointwise comparison of the feedback-free part on `[r, T]`
  have hpt : ∀ v ∈ Icc r T, s67bd_kernel 1 lam (v - r) * X v ≤
      Cw * A * E * Set.indicator (Set.Ici (0 : ℝ))
        (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-((lam - c1) * z))) (v - r) := by
    intro v hv
    have hz : (0 : ℝ) ≤ v - r := by linarith [hv.1]
    have hv0 : v ∈ Icc (0 : ℝ) T := ⟨by linarith [hv.1], hv.2⟩
    have hXv := hXub v hv0
    have hG : Set.indicator (Set.Ici (0 : ℝ))
        (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-((lam - c1) * z))) (v - r) =
        (1 + (v - r) ^ ((1:ℝ) / 2 - 1)) * Real.exp (-((lam - c1) * (v - r))) :=
      Set.indicator_of_mem (show v - r ∈ Set.Ici (0 : ℝ) from hz) _
    rw [s67bd_kern66_eq, hG]
    have hP : 0 ≤ 1 + (v - r) ^ ((1:ℝ) / 2 - 1) := by
      have := Real.rpow_nonneg hz ((1:ℝ) / 2 - 1)
      linarith
    have hexp : Real.exp (-(lam * (v - r))) * Real.exp (-cw * (T - v)) ≤
        E * Real.exp (-((lam - c1) * (v - r))) := by
      rw [← Real.exp_add, hEdef, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg (sub_nonneg.2 hc1cw.le) (show (0 : ℝ) ≤ (T - r) - (v - r) by linarith [hv.2])]
    calc (1 + (v - r) ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(lam * (v - r))) * X v
        ≤ (1 + (v - r) ^ ((1:ℝ) / 2 - 1)) * Real.exp (-(lam * (v - r))) *
          (Cw * Real.exp (-cw * (T - v)) * A) :=
          mul_le_mul_of_nonneg_left hXv (mul_nonneg hP (Real.exp_pos _).le)
      _ = Cw * A * ((1 + (v - r) ^ ((1:ℝ) / 2 - 1)) *
          (Real.exp (-(lam * (v - r))) * Real.exp (-cw * (T - v)))) := by ring
      _ ≤ Cw * A * ((1 + (v - r) ^ ((1:ℝ) / 2 - 1)) *
          (E * Real.exp (-((lam - c1) * (v - r))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hP) (mul_nonneg hCw hA)
      _ = Cw * A * E * ((1 + (v - r) ^ ((1:ℝ) / 2 - 1)) *
          Real.exp (-((lam - c1) * (v - r)))) := by ring
  -- integrated bound for the feedback-free integral
  have hIX : ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * X v ≤ Cw * A * E * K := by
    have hRint : IntegrableOn (fun v => Cw * A * E * Set.indicator (Set.Ici (0 : ℝ))
        (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-((lam - c1) * z))) (v - r))
        (Icc r T) volume :=
      (((s67bd_ind_int hκ).comp_sub_right r).const_mul (Cw * A * E)).integrableOn
    calc ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * X v
        ≤ ∫ v in Icc r T, Cw * A * E * Set.indicator (Set.Ici (0 : ℝ))
          (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-((lam - c1) * z))) (v - r) :=
          setIntegral_mono_on (hXint r ⟨hr0, hrT⟩) hRint measurableSet_Icc hpt
      _ = Cw * A * E * ∫ v in Icc r T, Set.indicator (Set.Ici (0 : ℝ))
          (fun z : ℝ => (1 + z ^ ((1:ℝ) / 2 - 1)) * Real.exp (-((lam - c1) * z))) (v - r) :=
          integral_const_mul _ _
      _ ≤ Cw * A * E * K :=
          mul_le_mul_of_nonneg_left (s67bd_trans_le hκ r T)
            (mul_nonneg (mul_nonneg hCw hA) hE0)
  -- the feedback integral is nonnegative
  have hIY : 0 ≤ ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * Y v :=
    setIntegral_nonneg measurableSet_Icc fun v hv =>
      mul_nonneg (s67bd_kernel_nonneg 1 lam (by linarith [hv.1])) (hY v ⟨by linarith [hv.1], hv.2⟩)
  -- the homogeneous term
  have hexpL : Real.exp (-lam * (T - r)) ≤ E :=
    Real.exp_le_exp.2 (by nlinarith)
  have hY' := hYineq r ⟨hr0, hrT⟩
  have t1 : Craw * Real.exp (-lam * (T - r)) * N ≤ C * E * N := by
    have h1 : Craw * Real.exp (-lam * (T - r)) ≤ C * E :=
      mul_le_mul hC1 hexpL (Real.exp_pos _).le (le_trans hCr hC1)
    exact mul_le_mul_of_nonneg_right h1 hN
  have t2 : Craw * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * X v) ≤ C * E * A := by
    have hXbd : Craw * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * X v) ≤
        Craw * (Cw * A * E * K) := mul_le_mul_of_nonneg_left hIX hCr
    have h2 : Craw * (Cw * A * E * K) = (Craw * Cw * K) * A * E := by ring
    have h3 : (Craw * Cw * K) * A * E ≤ C * A * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hA) hE0
    have h4 : C * A * E = C * E * A := by ring
    linarith
  have t3 : Craw * R0 * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * Y v) ≤
      C * R0 * (∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * Y v) := by
    have h1 : Craw * R0 ≤ C * R0 := mul_le_mul_of_nonneg_right hC1 hR0
    exact mul_le_mul_of_nonneg_right h1 hIY
  have hsplit : C * E * (N + A) = C * E * N + C * E * A := by ring
  linarith [hY', t1, t2, t3, hsplit]

end HRS.MS.BreakdownS67
