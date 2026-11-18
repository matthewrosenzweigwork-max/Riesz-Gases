import HRS.PDE.D3PhiPAux3

/-!
# D3PHIP, helper 4: dictionary `q^r`-integrals = `P`-integrals, and the fixed-time identity for `D`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

section fixed

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ} {r : ℝ}

theorem d3pp_c_eq (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) (hr : r ∈ Set.Icc 0 T) :
    ∫ y, ψt r y ∂(d3phi_q κ U ψ r) = d3pp_c κ U ψ ψt r := by
  rw [d3phi_integral_q hκ hU hψ hr]
  unfold d3pp_c
  rw [← integral_div]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

theorem d3pp_Y_eq (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) (hr : r ∈ Set.Icc 0 T)
    (p : ℝ → ℝ) :
    d3phi_Y κ U ψ w p r = ∫ x, d3pp_A κ U ψ w p r x ∂(d1_gibbsMeasure κ U) := by
  have hZ := d3phi_Z_pos hκ hU hψ hr
  unfold d3phi_Y
  rw [d3phi_integral_q hκ hU hψ hr]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  unfold d3pp_A
  rw [d3pp_exp_m κ U ψ hZ]
  ring

theorem d3pp_Ylog_eq (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) (hr : r ∈ Set.Icc 0 T)
    (p : ℝ → ℝ) :
    d3phi_Ylog κ U ψ w p r =
      ∫ x, d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x ∂(d1_gibbsMeasure κ U) := by
  have hZ := d3phi_Z_pos hκ hU hψ hr
  unfold d3phi_Ylog
  rw [d3phi_integral_q hκ hU hψ hr]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  unfold d3pp_A d3pp_ell
  beta_reduce
  rw [d3pp_exp_m κ U ψ hZ]
  ring

theorem d3pp_Sh_eq (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hψ : IsC12Test T ψ ψt) (hr : r ∈ Set.Icc 0 T)
    (p : ℝ → ℝ) :
    d3phi_Sh κ U ψ ψt w p r =
      ∫ x, d3pp_A κ U ψ w p r x *
        (d1_gen κ (d1_gradDrift U) (ψ r) x + κ * ‖Torus.grad (ψ r) x‖ ^ 2 - ψt r x
          + d3pp_c κ U ψ ψt r) ∂(d1_gibbsMeasure κ U) := by
  have hZ := d3phi_Z_pos hκ hU hψ hr
  unfold d3phi_Sh
  rw [d3phi_integral_q hκ hU hψ hr]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  unfold d3pp_A d3phi_src d3_source
  beta_reduce
  rw [d3pp_exp_m κ U ψ hZ, d3pp_c_eq hκ hU hψ hr]
  ring

theorem d3pp_dir_eq (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hr : r ∈ Set.Icc 0 T) (p : ℝ → ℝ) (hp : 0 < p r) :
    d3phi_dir κ U ψ w p r =
      p r * (p r - 1) * κ * ∫ x, d3phi_h κ U ψ w r x ^ (p r - 1) * w r x *
        ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2
        ∂(d1_gibbsMeasure κ U) := by
  have hZ := d3phi_Z_pos hκ hU hψ hr
  have hw1 : Torus.IsCk 1 (w r) := d3a_ck2_ck1 (hw.c12.c2 r hr)
  have hψ1 : Torus.IsCk 1 (ψ r) := d3a_ck2_ck1 (hψ.c2 r hr)
  have hwpos := hw.pos r hr
  have hu1 : Torus.IsCk 1 (d3phi_h κ U ψ w r) := d3pp_u_ck hw1 hψ1 _
  have hupos : ∀ x, 0 < d3phi_h κ U ψ w r x := fun x => d3pp_u_pos hwpos hZ x
  unfold d3phi_dir
  rw [d3phi_integral_q hκ hU hψ hr]
  have hpt : ∀ x, (Real.exp (ψ r x) / d3phi_Z κ U ψ r) *
      ‖Torus.grad (fun y => d3phi_h κ U ψ w r y ^ (p r / 2)) x‖ ^ 2 =
      (p r) ^ 2 / 4 * (d3phi_h κ U ψ w r x ^ (p r - 1) * w r x *
        ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2) := by
    intro x
    rw [d3pp_grad_rpow hu1 hupos (p r / 2) x]
    have hg : Torus.grad (fun y => Real.log (d3phi_h κ U ψ w r y)) x =
        Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x :=
      d3pp_grad_log_u hw1 hwpos hψ1 hZ x
    rw [hg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow]
    have hh := hupos x
    have e1 : (d3phi_h κ U ψ w r x ^ (p r / 2)) ^ 2 = d3phi_h κ U ψ w r x ^ p r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
      norm_num
    have e2 := d3pp_A_eq (κ := κ) (U := U) (ψ := ψ) (w := w) (x := x) hZ (hwpos x) p
    have e3 := d3pp_exp_m κ U ψ hZ (r := r) x
    unfold d3pp_A at e2
    rw [e3] at e2
    rw [e1]
    have e4 : Real.exp (ψ r x) / d3phi_Z κ U ψ r * d3phi_h κ U ψ w r x ^ p r =
        d3phi_h κ U ψ w r x ^ (p r - 1) * w r x := by
      rw [← e2]; ring
    calc _ = (Real.exp (ψ r x) / d3phi_Z κ U ψ r * d3phi_h κ U ψ w r x ^ p r) *
          (p r / 2) ^ 2 * ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2 := by ring
      _ = _ := by rw [e4]; ring
  simp_rw [hpt]
  rw [integral_const_mul]
  have := hp.ne'
  field_simp

end fixed

end HRS
