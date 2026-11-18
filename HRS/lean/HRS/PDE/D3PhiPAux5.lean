import HRS.PDE.D3PhiPAux4

/-!
# D3PHIP, helper 5: the fixed-time identity `∫ D_r dP = -Dir + (p-1) Sh + p' Ylog`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

section fixed

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ} {r : ℝ}

theorem d3pp_inner (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (hr : r ∈ Set.Icc 0 T) (p pd : ℝ → ℝ) (hp : 0 < p r) :
    ∫ x, d3pp_D κ U ψ ψt w p pd r x ∂(d1_gibbsMeasure κ U) =
      -d3phi_dir κ U ψ w p r + (p r - 1) * d3phi_Sh κ U ψ ψt w p r +
        pd r * d3phi_Ylog κ U ψ w p r := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hZ := d3phi_Z_pos hκ hU hψ hr
  have hw2 : Torus.IsCk 2 (w r) := hw.c12.c2 r hr
  have hψ2 : Torus.IsCk 2 (ψ r) := hψ.c2 r hr
  have hw1 := d3a_ck2_ck1 hw2
  have hψ1 := d3a_ck2_ck1 hψ2
  have hwpos := hw.pos r hr
  obtain ⟨-, hhc, hhpos, -⟩ := d3phi_slice_facts hκ hU hw hψ hr
  have cψ : Continuous (ψ r) := d3a_continuous_of_ck1 hψ1
  have cψt : Continuous (ψt r) := d3a_contOn_space hψ.cont_time_deriv hr
  have cLw : Continuous (d1_gen κ (d1_gradDrift U) (w r)) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hw2
  have cLψ : Continuous (d1_gen κ (d1_gradDrift U) (ψ r)) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hψ2
  have cg := d3a_continuous_grad_ck1 hψ1
  have cm : Continuous (d3pp_m κ U ψ r) := cψ.sub continuous_const
  have cA : Continuous (d3pp_A κ U ψ w p r) :=
    (hhc.rpow_const fun x => Or.inl (hhpos x).ne').mul (Real.continuous_exp.comp cm)
  have cell : Continuous (d3pp_ell κ U ψ w r) :=
    Real.continuousOn_log.comp_continuous hhc fun x => (hhpos x).ne'
  have cf : Continuous fun x => d3phi_h κ U ψ w r x ^ (p r - 1) :=
    hhc.rpow_const fun x => Or.inl (hhpos x).ne'
  set s := p r with hs
  set c0 := d3pp_c κ U ψ ψt r with hc0
  have hA : ∀ x, d3pp_A κ U ψ w p r x = d3phi_h κ U ψ w r x ^ (s - 1) * w r x := fun x =>
    d3pp_A_eq hZ (hwpos x) p
  -- pointwise decomposition of D
  have hD : ∀ x, d3pp_D κ U ψ ψt w p pd r x =
      pd r * (d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x) +
      s * (d1_gen κ (d1_gradDrift U) (w r) x * d3phi_h κ U ψ w r x ^ (s - 1)) +
      (s - 1) * (d3pp_A κ U ψ w p r x * (c0 - ψt r x)) := by
    intro x
    unfold d3pp_D d3pp_ellr d3pp_mr
    rw [hA x]
    have := (hwpos x).ne'
    field_simp
    ring
  have i1 : Integrable (fun x => d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x) (d1_gibbsMeasure κ U) :=
    d3a_hint _ (cA.mul cell)
  have i2 : Integrable (fun x => d1_gen κ (d1_gradDrift U) (w r) x * d3phi_h κ U ψ w r x ^ (s - 1))
      (d1_gibbsMeasure κ U) := d3a_hint _ (cLw.mul cf)
  have i3 : Integrable (fun x => d3pp_A κ U ψ w p r x * (c0 - ψt r x)) (d1_gibbsMeasure κ U) :=
    d3a_hint _ (cA.mul (continuous_const.sub cψt))
  have hint : ∫ x, d3pp_D κ U ψ ψt w p pd r x ∂(d1_gibbsMeasure κ U) =
      pd r * (∫ x, d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x ∂(d1_gibbsMeasure κ U)) +
      s * (∫ x, d1_gen κ (d1_gradDrift U) (w r) x * d3phi_h κ U ψ w r x ^ (s - 1) ∂(d1_gibbsMeasure κ U)) +
      (s - 1) * ∫ x, d3pp_A κ U ψ w p r x * (c0 - ψt r x) ∂(d1_gibbsMeasure κ U) := by
    simp_rw [hD]
    have j12 : Integrable (fun x => pd r * (d3pp_A κ U ψ w p r x * d3pp_ell κ U ψ w r x) +
        s * (d1_gen κ (d1_gradDrift U) (w r) x * d3phi_h κ U ψ w r x ^ (s - 1)))
        (d1_gibbsMeasure κ U) := (i1.const_mul _).add (i2.const_mul _)
    rw [integral_add j12 (i3.const_mul _), integral_add (i1.const_mul _) (i2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  -- Green
  have hG := d3pp_green_fixed hκ hU hw2 hwpos hψ2 hZ s
  have hu : d3phi_h κ U ψ w r = d3pp_u (w r) (ψ r) (d3phi_Z κ U ψ r) := rfl
  rw [← hu] at hG
  -- the source part
  have hSh := d3pp_Sh_eq (w := w) hκ hU hψ hr p
  have hAL : ∫ x, d3pp_A κ U ψ w p r x * (d1_gen κ (d1_gradDrift U) (ψ r) x +
      κ * ‖Torus.grad (ψ r) x‖ ^ 2 - ψt r x + c0) ∂(d1_gibbsMeasure κ U) =
      (∫ x, d3phi_h κ U ψ w r x ^ (s - 1) * w r x * (d1_gen κ (d1_gradDrift U) (ψ r) x +
        κ * ‖Torus.grad (ψ r) x‖ ^ 2) ∂(d1_gibbsMeasure κ U)) +
      ∫ x, d3pp_A κ U ψ w p r x * (c0 - ψt r x) ∂(d1_gibbsMeasure κ U) := by
    have j1 : Integrable (fun x => d3phi_h κ U ψ w r x ^ (s - 1) * w r x *
        (d1_gen κ (d1_gradDrift U) (ψ r) x + κ * ‖Torus.grad (ψ r) x‖ ^ 2)) (d1_gibbsMeasure κ U) :=
      d3a_hint _ ((cf.mul (d3a_continuous_of_ck1 hw1)).mul (cLψ.add (continuous_const.mul (cg.norm.pow 2))))
    rw [← integral_add j1 i3]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [hA x]
    ring
  have hdir := d3pp_dir_eq hκ hU hw hψ hr p hp
  have hYl := d3pp_Ylog_eq (w := w) hκ hU hψ hr p
  rw [hint, hdir, hSh, hAL, hYl]
  have hG' : s * ∫ x, d1_gen κ (d1_gradDrift U) (w r) x * d3phi_h κ U ψ w r x ^ (s - 1)
        ∂(d1_gibbsMeasure κ U) =
      -(s * (s - 1) * κ) * ∫ x, d3phi_h κ U ψ w r x ^ (s - 1) * w r x *
          ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2 ∂(d1_gibbsMeasure κ U)
        + (s - 1) * ∫ x, d3phi_h κ U ψ w r x ^ (s - 1) * w r x *
          (d1_gen κ (d1_gradDrift U) (ψ r) x + κ * ‖Torus.grad (ψ r) x‖ ^ 2) ∂(d1_gibbsMeasure κ U) := hG
  linear_combination hG'

end fixed

end HRS
