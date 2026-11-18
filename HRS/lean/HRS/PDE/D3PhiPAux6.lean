import HRS.PDE.D3PhiPAux5

/-!
# D3PHIP, helper 6: regularity in time of `Z̃`, `ℓ = log h`, `m`, and the pointwise derivative of `A`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

section time

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ}

theorem d3pp_exp_cont (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => Real.exp (ψ q.1 q.2) :=
  Real.continuous_exp.comp hψ.continuous_f

theorem d3pp_Z_contOn (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) :
    ContinuousOn (d3phi_Z κ U ψ) (Set.Icc 0 T) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  exact d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U) (H := fun r x => Real.exp (ψ r x))
    (d3pp_exp_cont hψ)

theorem d3pp_Z_hasDeriv (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) :
    ∀ r ∈ Set.Ioo 0 T, HasDerivAt (d3phi_Z κ U ψ)
      (∫ x, ψt r x * Real.exp (ψ r x) ∂(d1_gibbsMeasure κ U)) r := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  have hD : Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => ψt q.1 q.2 * Real.exp (ψ q.1 q.2) :=
    hψ.cont_time_deriv.mul (d3pp_exp_cont hψ)
  exact d3b_hasDerivAt_param (ν := d1_gibbsMeasure κ U) (τ := T) (F := fun r x => Real.exp (ψ r x))
    (D := fun r x => ψt r x * Real.exp (ψ r x)) (d3pp_exp_cont hψ) hD (fun x r hr =>
      (hψ.time_deriv x r hr).exp.congr_deriv (mul_comm _ _))

theorem d3pp_c_contOn (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hψ : IsC12Test T ψ ψt) :
    ContinuousOn (d3pp_c κ U ψ ψt) (Set.Icc 0 T) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  exact (d3b_logZ hT (P := d1_gibbsMeasure κ U) hψ).1

theorem d3pp_logZ_hasDeriv (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) :
    ∀ r ∈ Set.Ioo 0 T, HasDerivAt (fun r => Real.log (d3phi_Z κ U ψ r)) (d3pp_c κ U ψ ψt r) r := by
  intro r hr
  exact (d3pp_Z_hasDeriv hκ hU hψ r hr).log (d3phi_Z_pos hκ hU hψ (Set.Ioo_subset_Icc_self hr)).ne'

/-- Joint continuity (subtype form) of the objects built from `Z̃`. -/
theorem d3pp_Z_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3phi_Z κ U ψ q.1.1 :=
  (d3pp_Z_contOn hκ hU hψ).comp_continuous (continuous_subtype_val.comp continuous_fst)
    (fun q => q.1.2)

theorem d3pp_c_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3pp_c κ U ψ ψt q.1.1 :=
  (d3pp_c_contOn hκ hU hT hψ).comp_continuous (continuous_subtype_val.comp continuous_fst)
    (fun q => q.1.2)

theorem d3pp_h_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3phi_h κ U ψ w q.1.1 q.2 :=
  ((hw.c12.continuous_f.mul (d3pp_Z_cont_sub hκ hU hψ)).mul
    (Real.continuous_exp.comp hψ.continuous_f.neg))

theorem d3pp_h_pos (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (q : Set.Icc (0 : ℝ) T × Torus n) :
    0 < d3phi_h κ U ψ w q.1.1 q.2 :=
  d3pp_u_pos (w := w q.1.1) (ψ := ψ q.1.1) (hw.pos q.1.1 q.1.2) (d3phi_Z_pos hκ hU hψ q.1.2) q.2

theorem d3pp_ell_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3pp_ell κ U ψ w q.1.1 q.2 :=
  (d3pp_h_cont_sub hκ hU hw hψ).log fun q => (d3pp_h_pos hκ hU hw hψ q).ne'

theorem d3pp_m_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3pp_m κ U ψ q.1.1 q.2 :=
  hψ.continuous_f.sub ((d3pp_Z_cont_sub hκ hU hψ).log fun q => (d3phi_Z_pos hκ hU hψ q.1.2).ne')

theorem d3pp_ellr_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3pp_ellr κ U ψ ψt w q.1.1 q.2 :=
  ((hw.c12.cont_time_deriv.div hw.c12.continuous_f fun q => (hw.pos q.1.1 q.1.2 q.2).ne').sub
    hψ.cont_time_deriv).add (d3pp_c_cont_sub hκ hU hT hψ)

theorem d3pp_mr_cont_sub (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hψ : IsC12Test T ψ ψt) :
    Continuous fun q : Set.Icc (0 : ℝ) T × Torus n => d3pp_mr κ U ψ ψt q.1.1 q.2 :=
  hψ.cont_time_deriv.sub (d3pp_c_cont_sub hκ hU hT hψ)

/-- Pointwise (in `x`) time derivative of `ℓ = log h`. -/
theorem d3pp_ell_hasDeriv (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (x : Torus n) :
    ∀ r ∈ Set.Ioo 0 T, HasDerivAt (fun r => d3pp_ell κ U ψ w r x) (d3pp_ellr κ U ψ ψt w r x) r := by
  intro r hr
  have hrI := Set.Ioo_subset_Icc_self hr
  have hw' := hw.c12.time_deriv x r hr
  have hψ' := hψ.time_deriv x r hr
  have hZ' := d3pp_logZ_hasDeriv hκ hU hψ r hr
  have hwpos := hw.pos r hrI x
  have h1 := (hw'.log hwpos.ne').add (hZ'.sub hψ')
  have heq : (fun r' => d3pp_ell κ U ψ w r' x) =ᶠ[𝓝 r]
      fun r' => Real.log (w r' x) + (Real.log (d3phi_Z κ U ψ r') - ψ r' x) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
    have hr'I := Set.Ioo_subset_Icc_self hr'
    unfold d3pp_ell d3phi_h
    have hp := hw.pos r' hr'I x
    have hZ := d3phi_Z_pos hκ hU hψ hr'I
    rw [Real.log_mul (mul_pos hp hZ).ne' (Real.exp_pos _).ne', Real.log_mul hp.ne' hZ.ne',
      Real.log_exp]
    ring
  refine (h1.congr_of_eventuallyEq heq).congr_deriv ?_
  unfold d3pp_ellr
  ring

theorem d3pp_m_hasDeriv (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) (x : Torus n) :
    ∀ r ∈ Set.Ioo 0 T, HasDerivAt (fun r => d3pp_m κ U ψ r x) (d3pp_mr κ U ψ ψt r x) r := by
  intro r hr
  exact (hψ.time_deriv x r hr).sub (d3pp_logZ_hasDeriv hκ hU hψ r hr)

end time

end HRS
