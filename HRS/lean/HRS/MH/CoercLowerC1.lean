import HRS.Whole.Basic
import HRS.Energy.Coercivity
import HRS.MH.CoercLowerDefs

/-!
# CoercLower, Group C (`s > 0`): packets P13, P14, P15, P19.

Statements copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- Integrability of `t ^ (s/2-1) * exp(-t r)` on `Ioi 0` for `r > 0`. -/
private lemma clc1_integrableOn_kernel_Ioi {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * r)) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s / 2 - 1) (b := r)
    (by linarith) one_pos hr
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

/-- Integrability of `t ^ (s/2-1) * exp(-t r)` on `Ioc 0 T` for `r ≥ 0`, `T > 0`. -/
private lemma clc1_integrableOn_kernel_Ioc {s T r : ℝ} (hs : 0 < s) (hT : 0 < T) (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * r)) (Set.Ioc 0 T) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1)) (Set.Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine h1.mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * r))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht0.le _)
      (Real.exp_le_one_iff.mpr (by nlinarith))

/-- [P13] Gamma representation. -/
theorem gamma_rep (d : ℕ) {s : ℝ} (hs : 0 < s) {x : Euc d} (hx : x ≠ 0) :
    HRS.Whole.rieszKernel d s x =
      (1 / Real.Gamma (s / 2)) * ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) := by
  have hr : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s / 2) (r := ‖x‖ ^ 2) (half_pos hs) hr
  have hcongr : ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) =
      ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * t)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring_nf)
  rw [hcongr, key]
  have hG : Real.Gamma (s / 2) ≠ 0 := (Real.Gamma_pos_of_pos (half_pos hs)).ne'
  have hpow : (1 / ‖x‖ ^ 2) ^ (s / 2) = ‖x‖ ^ (-s) := by
    rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (norm_nonneg x)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1
    push_cast
    ring
  unfold HRS.Whole.rieszKernel
  rw [if_neg hs.ne', hpow]
  field_simp

/-- [P14] The truncation `gTpos`. -/
theorem gTpos_props {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    Measurable (gTpos s T : Euc d → ℝ) ∧
      (∀ x : Euc d, 0 ≤ gTpos s T x ∧ gTpos s T x ≤ gTpos s T (0 : Euc d)) ∧
      gTpos s T (0 : Euc d) = 2 / (s * Real.Gamma (s / 2)) * T ^ (s / 2) := by
  have hG : 0 < 1 / Real.Gamma (s / 2) := by
    have := Real.Gamma_pos_of_pos (half_pos hs)
    positivity
  have hmeas : Measurable (gTpos s T : Euc d → ℝ) := by
    unfold gTpos
    apply Measurable.const_mul
    have hF : Measurable (fun p : Euc d × ℝ => p.2 ^ (s / 2 - 1) * Real.exp (-p.2 * ‖p.1‖ ^ 2)) := by
      fun_prop
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 T))).measurable
  have hnonneg : ∀ x : Euc d, 0 ≤ gTpos s T x := by
    intro x
    unfold gTpos
    refine mul_nonneg hG.le (setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_))
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.exp_pos _).le
  have hle : ∀ x : Euc d, gTpos s T x ≤ gTpos s T (0 : Euc d) := by
    intro x
    unfold gTpos
    refine mul_le_mul_of_nonneg_left ?_ hG.le
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun t ht => ?_)
    · exact clc1_integrableOn_kernel_Ioc hs hT (by positivity)
    · exact clc1_integrableOn_kernel_Ioc hs hT (by positivity)
    · have ht0 : 0 < t := ht.1
      have hpt : 0 ≤ t ^ (s / 2 - 1) := Real.rpow_nonneg ht0.le _
      refine mul_le_mul_of_nonneg_left ?_ hpt
      rw [Real.exp_le_exp]
      have h0sq : ‖(0 : Euc d)‖ ^ 2 = 0 := by simp
      rw [h0sq, mul_zero]
      nlinarith [mul_nonneg ht0.le (sq_nonneg ‖x‖)]
  refine ⟨hmeas, fun x => ⟨hnonneg x, hle x⟩, ?_⟩
  have h0 : ∀ t : ℝ, Real.exp (-t * ‖(0 : Euc d)‖ ^ 2) = 1 := by
    intro t
    simp
  unfold gTpos
  simp only [h0, mul_one]
  rw [← intervalIntegral.integral_of_le hT.le, integral_rpow (Or.inl (by linarith))]
  have hs2 : s / 2 - 1 + 1 = s / 2 := by ring
  rw [hs2, Real.zero_rpow (half_pos hs).ne']
  field_simp
  ring

/-- [P15] The tail `fTpos` (pointwise facts). -/
theorem fTpos_props (d : ℕ) {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    Measurable (fTpos d s T) ∧
      ∀ x : Euc d, x ≠ 0 →
        fTpos d s T x =
          (1 / Real.Gamma (s / 2)) * ∫ t in Set.Ioi T, t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) ∧
        0 ≤ fTpos d s T x ∧ fTpos d s T x ≤ HRS.Whole.rieszKernel d s x := by
  have hgam : 0 < 1 / Real.Gamma (s / 2) := by
    have := Real.Gamma_pos_of_pos (half_pos hs)
    positivity
  have hRmeas : Measurable (HRS.Whole.rieszKernel d s) := by
    have hfun : HRS.Whole.rieszKernel d s = fun x : Euc d => ‖x‖ ^ (-s) :=
      funext fun x => by simp [HRS.Whole.rieszKernel, hs.ne']
    rw [hfun]
    exact measurable_norm.pow_const _
  have hmeasT := (gTpos_props (d := d) hs hT).1
  refine ⟨hRmeas.sub hmeasT, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) =
      (∫ t in Set.Ioc 0 T, t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) +
        ∫ t in Set.Ioi T, t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (clc1_integrableOn_kernel_Ioc hs hT (sq_nonneg _))
      ((clc1_integrableOn_kernel_Ioi hs hr).mono_set (Set.Ioi_subset_Ioi hT.le)),
      Set.Ioc_union_Ioi_eq_Ioi hT.le]
  have hval : fTpos d s T x =
      (1 / Real.Gamma (s / 2)) * ∫ t in Set.Ioi T, t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) := by
    unfold fTpos gTpos
    rw [gamma_rep d hs hx, hsplit]
    ring
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]
    refine mul_nonneg hgam.le (setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_))
    have ht0 : 0 < t := hT.trans ht
    exact mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le
  · unfold fTpos
    exact sub_le_self _ ((gTpos_props (d := d) hs hT).2.1 x).1

/-- [P19] Choice of `T = (NΛ)^{2/d}`. -/
theorem param_pos (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {Λ : ℝ} (hΛ : 0 < Λ)
    (hN : 1 ≤ N) :
    (1 / 2) *
        (2 / (s * Real.Gamma (s / 2)) * (((N : ℝ) * Λ) ^ (2 / (d : ℝ))) ^ (s / 2) / N +
          2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) *
            (((N : ℝ) * Λ) ^ (2 / (d : ℝ))) ^ ((s - d) / 2))) =
      Cpos d s * HRS.aNΛ d s Λ N := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdne : (d : ℝ) ≠ 0 := hd0.ne'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNne : (N : ℝ) ≠ 0 := hN0.ne'
  have hΛne : Λ ≠ 0 := hΛ.ne'
  have hsne : s ≠ 0 := hs.ne'
  have hdsne : (d : ℝ) - s ≠ 0 := by
    intro h
    have : (d : ℝ) = s := by linarith
    linarith
  have hGne : Real.Gamma (s / 2) ≠ 0 := (Real.Gamma_pos_of_pos (half_pos hs)).ne'
  have hTpow : ∀ c : ℝ, (((N : ℝ) * Λ) ^ (2 / (d : ℝ))) ^ c =
      (N : ℝ) ^ (2 / (d : ℝ) * c) * Λ ^ (2 / (d : ℝ) * c) := fun c => by
    rw [← Real.rpow_mul (by positivity), Real.mul_rpow hN0.le hΛ.le]
  have e1 : 2 / (d : ℝ) * (s / 2) = s / d := by
    field_simp
  have e2 : 2 / (d : ℝ) * ((s - d) / 2) = s / d - 1 := by
    field_simp
  unfold Cpos HRS.aNΛ
  rw [hTpow, hTpow, e1, e2]
  simp only [Real.rpow_sub hN0, Real.rpow_sub hΛ, Real.rpow_one]
  field_simp
