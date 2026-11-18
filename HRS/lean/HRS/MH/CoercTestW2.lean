import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs

/-!
# CoercTest W2: `qform_gauss_spectral`, `qform_gTs_mixture`

Statements copied verbatim from `HRS/MH/CoercTestSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- Integrability in `t` of `Qform (H t)` (the companion of `Qform_mix`). -/
theorem p_wt2_Qform_mix_integrable {ν : Measure ℝ} [SFinite ν] (H : ℝ → Euc d → ℝ) (K ρ : Euc d → ℝ)
    (hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2)) (hint : ∀ z, Integrable (fun t => H t z) ν)
    (hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ K z) (hρ : HRS.Whole.IsProbDensity ρ) (hK : DomK K ρ)
    (X : HRS.Whole.EucConfig d N) :
    Integrable (fun t => Qform (H t) X ρ) ν := by
  have hE := energyDens_mix H K ρ hH hint hdom hρ hK
  have hC := fun x => convFun_mix H K ρ hH hint hdom hρ hK x
  have i1 : ∀ i j, Integrable (fun t => H t (X i - X j)) ν := fun i j => hint _
  have i2 : ∀ i, Integrable (fun t => HRS.Whole.convFun (H t) ρ (X i)) ν := fun i => (hC _).2
  have s1 : Integrable (fun t => (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j, H t (X i - X j)) ν :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => i1 i j).const_mul _
  have s2 : Integrable (fun t => (2 / (N : ℝ)) * ∑ i, HRS.Whole.convFun (H t) ρ (X i)) ν :=
    (integrable_finsetSum _ fun i _ => i2 i).const_mul _
  exact (s1.sub s2).add hE.2

/-- The case `s > 0`. -/
theorem p_wt2_mixture_pos (hd : 1 ≤ d) {s T : ℝ} (hs : 0 < s) (hT : 0 < T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) :
    MeasureTheory.IntegrableOn (fun t : ℝ => wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ)
        (Set.Ioc (0 : ℝ) T) ∧
      Qform (gTpos s T : Euc d → ℝ) X ρ =
        ∫ t in Set.Ioc (0 : ℝ) T, wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
  have hc : 0 < 1 / Real.Gamma (s / 2) := by
    have := Real.Gamma_pos_of_pos (half_pos hs)
    positivity
  set c : ℝ := 1 / Real.Gamma (s / 2) with hcdef
  let H : ℝ → Euc d → ℝ := fun t z => (c * t ^ (s / 2 - 1)) * gaussK t z
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have hgT : ∀ z : Euc d, gTpos s T z = ∫ t, H t z ∂ν := by
    intro z
    unfold gTpos
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [H, gaussK]
    ring
  have hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2) := by
    simp only [H, gaussK]
    fun_prop
  have hint : ∀ z, Integrable (fun t => H t z) ν := by
    intro z
    have h0 : Integrable (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * ‖z‖ ^ 2)) ν := by
      have h1 : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1)) (Set.Ioc 0 T) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
          (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      refine h1.mono' ?_ ?_
      · exact (by fun_prop : Measurable (fun t : ℝ => t ^ (s / 2 - 1) *
          Real.exp (-t * ‖z‖ ^ 2))).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
        have ht0 : 0 < t := ht.1
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
        exact mul_le_of_le_one_right (Real.rpow_nonneg ht0.le _)
          (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z‖]))
    refine (Integrable.const_mul h0 c).congr (ae_of_all _ fun t => ?_)
    simp only [H, gaussK]
    ring
  have hnn : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ z : Euc d, 0 ≤ H t z := by
    intro t ht z
    exact mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ht.1.le _)) (Real.exp_pos _).le
  have hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ (fun _ : Euc d => gTpos s T (0 : Euc d)) z := by
    intro z
    have h1 : ∫ t, ‖H t z‖ ∂ν = ∫ t, H t z ∂ν := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      exact Real.norm_of_nonneg (hnn t ht z)
    rw [h1, ← hgT]
    exact ((gTpos_props hs hT).2.1 z).2
  have hK := domK_const (gTpos s T (0 : Euc d)) hρ
  have hmix := Qform_mix (ν := ν) H (fun _ : Euc d => gTpos s T (0 : Euc d)) ρ hH hint hdom hρ hK X
  have hmixi := p_wt2_Qform_mix_integrable (ν := ν) H (fun _ : Euc d => gTpos s T (0 : Euc d)) ρ hH
    hint hdom hρ hK X
  have hfun : (gTpos s T : Euc d → ℝ) = fun z => ∫ t, H t z ∂ν := funext hgT
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      Qform (H t) X ρ = wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
    intro t ht
    have h1 : Qform (H t) X ρ = (c * t ^ (s / 2 - 1)) * Qform (gaussK t) X ρ :=
      Qform_smul (c * t ^ (s / 2 - 1)) (gaussK t) X ρ
    rw [h1]
    have : wS s t = c * t ^ (s / 2 - 1) := by
      simp only [wS, if_neg hs.ne', hcdef]
      ring
    rw [this]
  refine ⟨?_, ?_⟩
  · exact hmixi.congr ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hpt))
  · rw [hfun, hmix]
    exact setIntegral_congr_fun measurableSet_Ioc hpt

/-- The case `s = 0`. -/
theorem p_wt2_mixture_log {T : ℝ} (hT : 1 ≤ T) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : Integrable (fun y : Euc d => Real.log (2 + ‖y‖) * ρ y)) (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) :
    MeasureTheory.IntegrableOn (fun t : ℝ => wS 0 t * Qform (HRS.MH.CoercLower.gaussK t) X ρ)
        (Set.Ioc (0 : ℝ) T) ∧
      Qform (gTlog T : Euc d → ℝ) X ρ =
        ∫ t in Set.Ioc (0 : ℝ) T, wS 0 t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  set H : ℝ → Euc d → ℝ := fun t z => (1 / 2) * ((Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t)
    with hH_def
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T) with hν
  have hgT : (gTlog T : Euc d → ℝ) = fun z => ∫ t, H t z ∂ν := by
    funext z
    simp only [gTlog, hH_def, hν]
    rw [integral_const_mul]
  have hmeas : Measurable (fun p : ℝ × Euc d => H p.1 p.2) := by
    simp only [hH_def]
    fun_prop
  have hint : ∀ z, Integrable (fun t => H t z) ν := fun z =>
    ((frullani_core (d := d) hT z).1).const_mul (1 / 2)
  have hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ (1 + Real.log T) + Real.log (2 + ‖z‖) := by
    intro z
    have h1 := (frullani_core (d := d) hT z).2
    have hn : ∀ t, ‖H t z‖ = (1 / 2) * ‖(Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t‖ := by
      intro t
      simp only [hH_def, norm_mul]
      norm_num
    simp only [hn, hν]
    rw [integral_const_mul]
    have : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    linarith
  have hK := domK_log (d := d) (c := 1 + Real.log T) (by linarith) hρ hlog
  have hmix := Qform_mix (ν := ν) H _ ρ hmeas hint hdom hρ hK X
  have hmixi := p_wt2_Qform_mix_integrable (ν := ν) H _ ρ hmeas hint hdom hρ hK X
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      Qform (H t) X ρ = wS 0 t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
    intro t ht
    have htpos : 0 < t := ht.1
    have hHt : H t = fun z => (1 / (2 * t)) * (gaussK t z - Real.exp (-t)) := by
      funext z
      simp only [hH_def, gaussK]
      field_simp
    have hb : ∀ z : Euc d, |gaussK t z| ≤ 1 := by
      intro z
      have : 0 ≤ gaussK t z := (Real.exp_pos _).le
      rw [abs_of_nonneg this]
      unfold gaussK
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg ‖z‖]
    have hdomK : DomK (fun _ : Euc d => (1 : ℝ)) ρ := domK_const 1 hρ
    have hI := integrable_of_domK (h := gaussK t) (K := fun _ => (1 : ℝ)) (ρ := ρ)
      (by unfold gaussK; fun_prop) hρ hb hdomK
    rw [hHt, Qform_smul, Qform_sub_const (gaussK t) (Real.exp (-t)) hρ hN X hI.1 hI.2]
    simp [wS]
  refine ⟨?_, ?_⟩
  · exact hmixi.congr ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ hpt))
  · rw [hgT, hmix]
    exact setIntegral_congr_fun measurableSet_Ioc hpt

/-- [W2b] The truncated kernel as a mixture of Gaussian forms. -/
theorem qform_gTs_mixture (hd : 1 ≤ d) {s T : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hT : 1 ≤ T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ))
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) :
    MeasureTheory.IntegrableOn (fun t : ℝ => wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ)
        (Set.Ioc (0 : ℝ) T) ∧
      Qform (gTs d s T) X ρ = ∫ t in Set.Ioc (0 : ℝ) T, wS s t * Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
  by_cases h0 : s = 0
  · subst h0
    have hlog' := (integrable_log_moment_iff hρ).mp (hlog rfl)
    have := p_wt2_mixture_log (N := N) hT hρ hlog' hN X
    simpa [gTs] using this
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
    have := p_wt2_mixture_pos (N := N) hd hs (by linarith) hρ hN X
    simpa [gTs, h0] using this

/-- [W2a], conditional on the statement of `fourierL2_gaussU` (W1b), which is passed as the hypothesis
`hW1` (verbatim its conclusion).  Then `qform_gauss_spectral = p_wt2_gauss_spectral_of_W1 ... (fourierL2_gaussU ...)`. -/
theorem p_wt2_gauss_spectral_of_W1 (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N)
    (hW1 : (Integrable (gaussU t X ρ) ∧ MemLp (gaussU t X ρ) 2 volume) ∧
      ∀ᵐ ξ : Euc d ∂volume, HRS.PDE.ToolboxRd.fourierL2 (gaussU t X ρ) ξ =
        (((Real.pi / (2 * t)) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t)) : ℝ) : ℂ) *
          nuHat X ρ ξ) :
    Integrable (fun ξ : Euc d => Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) * ‖nuHat X ρ ξ‖ ^ 2) ∧
      Qform (HRS.MH.CoercLower.gaussK t) X ρ =
        (Real.pi / t) ^ ((d : ℝ) / 2) * ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) * ‖nuHat X ρ ξ‖ ^ 2 := by
  obtain ⟨⟨_, hmem⟩, hF⟩ := hW1
  set a : ℝ := Real.pi / (2 * t) with ha
  have ha0 : 0 < a := by positivity
  set c : ℝ := a ^ ((d : ℝ) / 2) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos ha0 _
  have hnorm : ∀ᵐ ξ : Euc d ∂volume, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) * ‖nuHat X ρ ξ‖ ^ 2 =
      (c ^ 2)⁻¹ * ‖HRS.PDE.ToolboxRd.fourierL2 (gaussU t X ρ) ξ‖ ^ 2 := by
    filter_upwards [hF] with ξ hξ
    rw [hξ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, mul_pow,
      ← Real.exp_nat_mul]
    have he : Real.exp (((2 : ℕ) : ℝ) * (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t))) =
        Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) := by
      congr 1
      push_cast
      field_simp
    rw [he]
    field_simp
  have hI := HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hmem
  refine ⟨?_, ?_⟩
  · exact (hI.const_mul (c ^ 2)⁻¹).congr (hnorm.mono fun ξ h => h.symm)
  · rw [integral_congr_ae hnorm, integral_const_mul,
      HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hmem,
      ← gauss_Qform_eq ht hρ hN X]
    have h1 : (Real.pi / t) ^ ((d : ℝ) / 2) * (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) = c ^ 2 := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have h2 : Real.pi / t * (Real.pi / (4 * t)) = a * a := by
        rw [ha]
        field_simp
        ring
      rw [h2, Real.mul_rpow ha0.le ha0.le, hc, sq]
    have h3 : (Real.pi / t) ^ ((d : ℝ) / 2) * ((c ^ 2)⁻¹ * ((Real.pi / (4 * t)) ^ ((d : ℝ) / 2) *
        Qform (HRS.MH.CoercLower.gaussK t) X ρ)) =
        ((Real.pi / t) ^ ((d : ℝ) / 2) * (Real.pi / (4 * t)) ^ ((d : ℝ) / 2) / c ^ 2) *
          Qform (HRS.MH.CoercLower.gaussK t) X ρ := by
      ring
    rw [h3, h1, div_self (by positivity), one_mul]

end HRS.MH.CoercTest
