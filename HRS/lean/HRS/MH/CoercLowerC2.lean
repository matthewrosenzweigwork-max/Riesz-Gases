import HRS.Whole.Basic
import HRS.Energy.Coercivity
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerC1
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# CoercLower, Group C (`s > 0`): packet P16 (`fTpos_integral`).

Statement copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- `{0}` is Lebesgue-null in `ℝ^d` for `d ≥ 1`. -/
private lemma clc2_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z : Euc d ∂volume, z ≠ 0 := by
  have hnt : Nontrivial (Euc d) := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    infer_instance
  have h0 : volume ({0} : Set (Euc d)) = 0 := measure_singleton 0
  rw [ae_iff]
  simp [h0]

/-- Integrability of the Gaussian `exp(-t‖x‖²)` on `ℝ^d` for `t > 0`. -/
private lemma clc2_integrable_gauss (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Euc d => Real.exp (-t * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (t : ℂ))
    (by simpa using ht) 0 0).re
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [zero_mul, add_zero, RCLike.re_to_complex, neg_mul]
  rw [show -((t : ℂ) * (‖x‖ : ℂ) ^ 2) = ((-(t * ‖x‖ ^ 2) : ℝ) : ℂ) by push_cast; ring,
    Complex.exp_ofReal_re]

/-- Integrability of `(1/Γ(s/2)) t^{s/2-1} exp(-t r)` on `Ioi T` for `r > 0`, `T > 0`. -/
private lemma clc2_integrableOn_Ioi {s T r : ℝ} (hs : 0 < s) (hT : 0 < T) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => 1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * r)) (Set.Ioi T) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * r)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s / 2 - 1) (b := r)
      (by linarith) one_pos hr
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    ring_nf
  have h2 : IntegrableOn (fun t : ℝ => 1 / Real.Gamma (s / 2) * (t ^ (s / 2 - 1) * Real.exp (-t * r)))
      (Set.Ioi T) :=
    (h1.mono_set (Set.Ioi_subset_Ioi hT.le)).const_mul (1 / Real.Gamma (s / 2))
  refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
  ring

/-- Pointwise identity for the Gaussian value `(π/t)^{d/2}`. -/
private lemma clc2_pointwise (d : ℕ) {s t : ℝ} (ht : 0 < t) :
    1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * (Real.pi / t) ^ ((d : ℝ) / 2) =
      Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * t ^ ((s - (d : ℝ)) / 2 - 1) := by
  rw [Real.div_rpow Real.pi_pos.le ht.le]
  rw [show (s - (d : ℝ)) / 2 - 1 = (s / 2 - 1) - (d : ℝ) / 2 by ring,
    Real.rpow_sub ht (s / 2 - 1) ((d : ℝ) / 2)]
  ring

/-- [P16] Tonelli: `fTpos` is integrable and its integral is the closed form. -/
theorem fTpos_integral (d : ℕ) {s T : ℝ} (hs : 0 < s) (hsd : s < d) (hT : 0 < T) :
    Integrable (fTpos d s T) ∧
      ∫ x, fTpos d s T x =
        Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) * T ^ ((s - d) / 2) := by
  have hd : 1 ≤ d := by
    have h0 : (0 : ℝ) < d := by linarith
    have h1 : 0 < d := by exact_mod_cast h0
    omega
  have hG : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (half_pos hs)
  have hds : 0 < (d : ℝ) - s := by linarith
  have hmeas : Measurable (fTpos d s T) := (fTpos_props d hs hT).1
  -- pointwise representation off the null set `{0}`
  have hstep1 : ∀ x : Euc d, x ≠ 0 →
      ENNReal.ofReal (fTpos d s T x) =
        ∫⁻ t in Set.Ioi T,
          ENNReal.ofReal (1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) := by
    intro x hx
    obtain ⟨hrep, -, -⟩ := (fTpos_props d hs hT).2 x hx
    have hr : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    have hint : ∫ t in Set.Ioi T, 1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) =
        1 / Real.Gamma (s / 2) * ∫ t in Set.Ioi T, t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) := by
      rw [← integral_const_mul]
      simp only [mul_assoc]
    rw [hrep, ← hint]
    refine ofReal_integral_eq_lintegral_ofReal (clc2_integrableOn_Ioi hs hT hr) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := hT.trans ht
    exact mul_nonneg (mul_nonneg (one_div_nonneg.mpr hG.le) (Real.rpow_nonneg ht0.le _))
      (Real.exp_pos _).le
  -- the lintegral over `x` of each slice
  have hinner : ∀ t ∈ Set.Ioi T,
      ∫⁻ x : Euc d, ENNReal.ofReal (1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) ∂volume =
        ENNReal.ofReal (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * t ^ ((s - (d : ℝ)) / 2 - 1)) := by
    intro t ht
    have ht0 : 0 < t := hT.trans ht
    have hint : Integrable (fun x : Euc d => 1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) :=
      (clc2_integrable_gauss d ht0).const_mul _
    have hnn : ∀ x : Euc d, 0 ≤ 1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2) :=
      fun x => mul_nonneg (mul_nonneg (one_div_nonneg.mpr hG.le) (Real.rpow_nonneg ht0.le _))
        (Real.exp_pos _).le
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
    congr 1
    rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht0]
    simp only [finrank_euclideanSpace_fin]
    exact clc2_pointwise d ht0
  -- Tonelli
  have hmeasG : Measurable (fun p : Euc d × ℝ =>
      ENNReal.ofReal (1 / Real.Gamma (s / 2) * p.2 ^ (s / 2 - 1) * Real.exp (-p.2 * ‖p.1‖ ^ 2))) := by
    fun_prop
  have hswap : ∫⁻ x : Euc d, ∫⁻ t in Set.Ioi T,
      ENNReal.ofReal (1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) ∂volume =
        ∫⁻ t in Set.Ioi T, ∫⁻ x : Euc d,
          ENNReal.ofReal (1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) ∂volume :=
    lintegral_lintegral_swap hmeasG.aemeasurable
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (fTpos d s T x) =
      ∫⁻ t in Set.Ioi T,
        ENNReal.ofReal (1 / Real.Gamma (s / 2) * t ^ (s / 2 - 1) * Real.exp (-t * ‖x‖ ^ 2)) := by
    filter_upwards [clc2_ae_ne_zero hd] with x hx
    exact hstep1 x hx
  have hL : ∫⁻ x, ENNReal.ofReal (fTpos d s T x) ∂volume =
      ENNReal.ofReal (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) * T ^ ((s - d) / 2)) := by
    rw [lintegral_congr_ae hae, hswap, setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hinner t ht)]
    have ha : (s - (d : ℝ)) / 2 - 1 < -1 := by linarith
    have hIK : IntegrableOn (fun t : ℝ => Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) *
        t ^ ((s - (d : ℝ)) / 2 - 1)) (Set.Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt ha hT).const_mul _
    have hnnK : 0 ≤ᵐ[volume.restrict (Set.Ioi T)] (fun t : ℝ => Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) *
        t ^ ((s - (d : ℝ)) / 2 - 1)) :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht =>
        mul_nonneg (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) hG.le)
          (Real.rpow_nonneg (hT.trans ht).le _))
    rw [← ofReal_integral_eq_lintegral_ofReal hIK hnnK]
    congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hT]
    rw [show (s - (d : ℝ)) / 2 - 1 + 1 = (s - (d : ℝ)) / 2 by ring]
    have hne2 : s - (d : ℝ) ≠ 0 := (by linarith : s - (d : ℝ) < 0).ne
    have hne1 : (d : ℝ) - s ≠ 0 := hds.ne'
    field_simp
    ring
  have hVnn : 0 ≤ Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) * T ^ ((s - d) / 2) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) hG.le)
      (div_nonneg zero_le_two hds.le)) (Real.rpow_nonneg hT.le _)
  have hnnf : 0 ≤ᵐ[volume] fTpos d s T := by
    filter_upwards [clc2_ae_ne_zero hd] with x hx
    exact ((fTpos_props d hs hT).2 x hx).2.1
  have hfin : ∫⁻ x, ENNReal.ofReal (fTpos d s T x) ∂volume < ⊤ := by
    rw [hL]
    exact ENNReal.ofReal_lt_top
  have hInt : Integrable (fTpos d s T) :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnnf).mpr hfin⟩
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnnf hmeas.aestronglyMeasurable, hL, ENNReal.toReal_ofReal hVnn]

end HRS.MH.CoercLower
