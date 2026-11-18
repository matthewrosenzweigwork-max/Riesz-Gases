import HRS.PDE.D3PhiPAux1

/-!
# D3PHIP, helper 2: the fixed-time Green identity
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- `u = w · Zc · e^{-ψ}` (the density `h_r` of packet A at a fixed time). -/
def d3pp_u (w ψ : Torus n → ℝ) (Zc : ℝ) (y : Torus n) : ℝ := w y * Zc * Real.exp (-ψ y)

theorem d3pp_u_pos {w ψ : Torus n → ℝ} (hwpos : ∀ x, 0 < w x) {Zc : ℝ} (hZ : 0 < Zc) (x : Torus n) :
    0 < d3pp_u w ψ Zc x := mul_pos (mul_pos (hwpos x) hZ) (Real.exp_pos _)

theorem d3pp_u_ck {k : WithTop ℕ∞} {w ψ : Torus n → ℝ} (hw : Torus.IsCk k w) (hψ : Torus.IsCk k ψ)
    (Zc : ℝ) : Torus.IsCk k (d3pp_u w ψ Zc) := d3pp_isCk_u hw hψ Zc

theorem d3pp_green_fixed {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hwpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ)
    {Zc : ℝ} (hZ : 0 < Zc) (s : ℝ) :
    s * ∫ x, d1_gen κ (d1_gradDrift U) w x * d3pp_u w ψ Zc x ^ (s - 1) ∂(d1_gibbsMeasure κ U) =
      -(s * (s - 1) * κ) * ∫ x, d3pp_u w ψ Zc x ^ (s - 1) * w x *
          ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2 ∂(d1_gibbsMeasure κ U)
        + (s - 1) * ∫ x, d3pp_u w ψ Zc x ^ (s - 1) * w x *
          (d1_gen κ (d1_gradDrift U) ψ x + κ * ‖Torus.grad ψ x‖ ^ 2) ∂(d1_gibbsMeasure κ U) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hw1 := d3a_ck2_ck1 hw
  have hψ1 := d3a_ck2_ck1 hψ
  have hu2 := d3pp_u_ck hw hψ Zc
  have hupos := d3pp_u_pos (ψ := ψ) hwpos hZ
  have hu1 := d3a_ck2_ck1 hu2
  have hf2 : Torus.IsCk 2 (fun y => d3pp_u w ψ Zc y ^ (s - 1)) := d3pp_isCk_rpow hu2 hupos _
  have hAi2 : Torus.IsCk 2 (fun y => d3pp_u w ψ Zc y ^ (s - 1) * w y) := d3pp_isCk_mul hf2 hw
  have hf1 := d3a_ck2_ck1 hf2
  have hlogw : Torus.IsCk 1 (fun y => Real.log (w y)) := d3a_isCk_log hw1 hwpos
  -- abbreviations
  set f1 : Torus n → ℝ := fun y => d3pp_u w ψ Zc y ^ (s - 1) with hf1def
  set Ai : Torus n → ℝ := fun y => f1 y * w y with hAidef
  set a : Torus n → Euc n := fun x => Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x with hadef
  set g : Torus n → Euc n := Torus.grad ψ with hgdef
  set B : Torus n → Euc n := Torus.grad (fun y => Real.log (w y)) with hBdef
  have hBa : ∀ x, B x = a x + g x := fun x => by simp [hadef]
  -- continuity
  have cw := d3a_continuous_of_ck1 hw1
  have cf1 := d3a_continuous_of_ck1 hf1
  have cAi := d3a_continuous_of_ck1 (d3a_ck2_ck1 hAi2)
  have cB := d3a_continuous_grad_ck1 hlogw
  have cg := d3a_continuous_grad_ck1 hψ1
  have ca : Continuous a := cB.sub cg
  have cLw : Continuous (d1_gen κ (d1_gradDrift U) w) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hw
  have cLψ : Continuous (d1_gen κ (d1_gradDrift U) ψ) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hψ
  -- gradients
  have gu : ∀ x, Torus.grad (fun y => Real.log (d3pp_u w ψ Zc y)) x = a x := fun x =>
    d3pp_grad_log_u hw1 hwpos hψ1 hZ x
  have gf1 : ∀ x, Torus.grad f1 x = ((s - 1) * f1 x) • a x := fun x => by
    have := d3pp_grad_rpow hu1 hupos (s - 1) x
    rw [gu x] at this
    exact this
  have gw : ∀ x, Torus.grad w x = w x • B x := fun x => d3a_grad_eq_smul_log hw1 hwpos x
  have gAi : ∀ x, Torus.grad Ai x = Ai x • (B x + (s - 1) • a x) := fun x => by
    have := d3pp_grad_mul hf1 hw1 x
    rw [gf1 x, gw x] at this
    simp only [hAidef]
    rw [this]
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  -- the three quadratic integrals
  have c1 : Continuous fun x => Ai x * ‖a x‖ ^ 2 := cAi.mul (ca.norm.pow 2)
  have c2 : Continuous fun x => Ai x * inner ℝ (a x) (g x) := cAi.mul (ca.inner cg)
  have c3 : Continuous fun x => Ai x * ‖g x‖ ^ 2 := cAi.mul (cg.norm.pow 2)
  set I1 := ∫ x, Ai x * ‖a x‖ ^ 2 ∂(d1_gibbsMeasure κ U) with hI1
  set I2 := ∫ x, Ai x * inner ℝ (a x) (g x) ∂(d1_gibbsMeasure κ U) with hI2
  set I3 := ∫ x, Ai x * ‖g x‖ ^ 2 ∂(d1_gibbsMeasure κ U) with hI3
  -- Green 1
  have G1 := d3a_green_P hκ hU hf2 hw
  have e1 : ∫ x, inner ℝ (Torus.grad f1 x) (Torus.grad w x) ∂(d1_gibbsMeasure κ U) =
      (s - 1) * (I1 + I2) := by
    have hpt : ∀ x, inner ℝ (Torus.grad f1 x) (Torus.grad w x) =
        (s - 1) * (Ai x * ‖a x‖ ^ 2 + Ai x * inner ℝ (a x) (g x)) := by
      intro x
      rw [gf1 x, gw x, real_inner_smul_left, real_inner_smul_right, hBa x, inner_add_right,
        real_inner_self_eq_norm_sq]
      simp only [hAidef]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_add (d3a_hint _ c1) (d3a_hint _ c2)]
  -- Green 2
  have G2 := d3a_green_P hκ hU hAi2 hψ
  have e2 : ∫ x, inner ℝ (Torus.grad Ai x) (Torus.grad ψ x) ∂(d1_gibbsMeasure κ U) =
      s * I2 + I3 := by
    have hpt : ∀ x, inner ℝ (Torus.grad Ai x) (Torus.grad ψ x) =
        s * (Ai x * inner ℝ (a x) (g x)) + Ai x * ‖g x‖ ^ 2 := by
      intro x
      rw [gAi x, real_inner_smul_left, inner_add_left, real_inner_smul_left, hBa x, inner_add_left,
        real_inner_self_eq_norm_sq]
      show Ai x * (_ + _ + _) = _
      ring
    simp_rw [hpt]
    rw [integral_add ((d3a_hint _ c2).const_mul s) (d3a_hint _ c3), integral_const_mul]
  -- assemble
  have hJ1 : ∫ x, d1_gen κ (d1_gradDrift U) w x * d3pp_u w ψ Zc x ^ (s - 1) ∂(d1_gibbsMeasure κ U) =
      -(κ * ((s - 1) * (I1 + I2))) := by
    have := G1
    rw [e1] at this
    simpa [hf1def, mul_assoc] using this
  have hJ2 : ∫ x, d1_gen κ (d1_gradDrift U) ψ x * Ai x ∂(d1_gibbsMeasure κ U) =
      -(κ * (s * I2 + I3)) := by
    have := G2
    rw [e2] at this
    simpa [mul_assoc] using this
  have hmix : ∫ x, d3pp_u w ψ Zc x ^ (s - 1) * w x *
      (d1_gen κ (d1_gradDrift U) ψ x + κ * ‖Torus.grad ψ x‖ ^ 2) ∂(d1_gibbsMeasure κ U) =
      (∫ x, d1_gen κ (d1_gradDrift U) ψ x * Ai x ∂(d1_gibbsMeasure κ U)) + κ * I3 := by
    have i1 : Integrable (fun x => d1_gen κ (d1_gradDrift U) ψ x * Ai x) (d1_gibbsMeasure κ U) :=
      d3a_hint _ (cLψ.mul cAi)
    have i2 : Integrable (fun x => κ * (Ai x * ‖g x‖ ^ 2)) (d1_gibbsMeasure κ U) :=
      (d3a_hint _ c3).const_mul κ
    rw [← integral_const_mul, ← integral_add i1 i2]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hAidef, hf1def, hgdef]
    ring
  have hI1' : ∫ x, d3pp_u w ψ Zc x ^ (s - 1) * w x * ‖Torus.grad (fun y => Real.log (w y)) x -
      Torus.grad ψ x‖ ^ 2 ∂(d1_gibbsMeasure κ U) = I1 := rfl
  rw [hJ1, hmix, hJ2]
  ring

end HRS
