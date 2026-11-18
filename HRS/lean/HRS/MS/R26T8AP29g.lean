import HRS.MS.R26T8AP29f

/-!
# S8.2 T8A P29 (part g): gradient and Hessian bounds of the sum `Q0 + Ψ`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_pw_nonneg (M : ℝ) (x y : Euc d) : 0 ≤ Phase2S82.pairWeight M x y := by
  unfold Phase2S82.pairWeight
  exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)

theorem r26t8a_p29_gradient (Q0 Psi : Euc d → Euc d → ℝ) {A1 B M1 MU Mf : ℝ} (hA1 : 0 ≤ A1) (hB : 0 ≤ B)
    (h1 : M1 ≤ Mf) (h2 : MU ≤ Mf)
    (hQd : ∀ x y : Euc d, x ≠ y → DifferentiableAt ℝ (Function.uncurry Q0) (x, y))
    (hQ : ∀ x y : Euc d, x ≠ y → ‖pairGradX Q0 x y‖ + ‖pairGradY Q0 x y‖ ≤
      A1 * Phase2S82.pairWeight M1 x y * (1 + smallRadius x y ^ (1 - criticalS d)))
    (hPd : ContDiff ℝ 8 (Function.uncurry Psi))
    (hP : ∀ x y : Euc d, ‖iteratedFDeriv ℝ 1 (Function.uncurry Psi) (x, y)‖ ≤ B * Phase2S82.pairWeight MU x y)
    {Afin : ℝ} (hA : A1 + 2 * B ≤ Afin) (x y : Euc d) (hxy : x ≠ y) :
    ‖pairGradX (fun x y => Q0 x y + Psi x y) x y‖ + ‖pairGradY (fun x y => Q0 x y + Psi x y) x y‖ ≤
      Afin * Phase2S82.pairWeight Mf x y * (1 + smallRadius x y ^ (1 - criticalS d)) := by
  set br : ℝ := 1 + smallRadius x y ^ (1 - criticalS d) with hbr
  have hbr1 : 1 ≤ br := by
    have : 0 ≤ smallRadius x y ^ (1 - criticalS d) := Real.rpow_nonneg (r26t8a_p29_smallRadius_nonneg x y) _
    rw [hbr]; linarith
  have hPdiff : DifferentiableAt ℝ (Function.uncurry Psi) (x, y) :=
    (hPd.differentiable (by norm_num)) (x, y)
  have hQdiff := hQd x y hxy
  have hfx : DifferentiableAt ℝ (fun x' : Euc d => (x', y)) x :=
    differentiableAt_id.prodMk (differentiableAt_const y)
  have hfy : DifferentiableAt ℝ (fun y' : Euc d => (x, y')) y :=
    (differentiableAt_const x).prodMk differentiableAt_id
  have dx1 : DifferentiableAt ℝ (fun x' => Q0 x' y) x :=
    DifferentiableAt.comp (g := Function.uncurry Q0) (f := fun x' : Euc d => (x', y)) x hQdiff hfx
  have dx2 : DifferentiableAt ℝ (fun x' => Psi x' y) x :=
    DifferentiableAt.comp (g := Function.uncurry Psi) (f := fun x' : Euc d => (x', y)) x hPdiff hfx
  have dy1 : DifferentiableAt ℝ (Q0 x) y :=
    DifferentiableAt.comp (g := Function.uncurry Q0) (f := fun y' : Euc d => (x, y')) y hQdiff hfy
  have dy2 : DifferentiableAt ℝ (Psi x) y :=
    DifferentiableAt.comp (g := Function.uncurry Psi) (f := fun y' : Euc d => (x, y')) y hPdiff hfy
  have ex : pairGradX (fun x y => Q0 x y + Psi x y) x y = pairGradX Q0 x y + pairGradX Psi x y :=
    r26t8a_V1_gradient_add dx1 dx2
  have ey : pairGradY (fun x y => Q0 x y + Psi x y) x y = pairGradY Q0 x y + pairGradY Psi x y :=
    r26t8a_V1_gradient_add dy1 dy2
  have gP := r26t8a_p29_pairGrad_norm_le hPdiff
  have w1 := r26t8a_p29_pairWeight_mono h1 x y
  have w2 := r26t8a_p29_pairWeight_mono h2 x y
  have w0 := r26t8a_p29_pw_nonneg (d := d) Mf x y
  have q1 := hQ x y hxy
  have p1 := hP x y
  rw [ex, ey]
  have t1 := norm_add_le (pairGradX Q0 x y) (pairGradX Psi x y)
  have t2 := norm_add_le (pairGradY Q0 x y) (pairGradY Psi x y)
  have b1 : A1 * Phase2S82.pairWeight M1 x y * br ≤ A1 * Phase2S82.pairWeight Mf x y * br :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left w1 hA1) (by linarith)
  have b2 : 2 * (B * Phase2S82.pairWeight MU x y) ≤ 2 * B * Phase2S82.pairWeight Mf x y * br := by
    calc 2 * (B * Phase2S82.pairWeight MU x y) ≤ 2 * (B * Phase2S82.pairWeight Mf x y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left w2 hB) (by norm_num)
      _ ≤ 2 * B * Phase2S82.pairWeight Mf x y * br := by nlinarith [mul_nonneg hB w0]
  have hfin : (A1 + 2 * B) * Phase2S82.pairWeight Mf x y * br ≤ Afin * Phase2S82.pairWeight Mf x y * br := by
    have : 0 ≤ Phase2S82.pairWeight Mf x y * br := mul_nonneg w0 (by linarith)
    nlinarith
  nlinarith [t1, t2, q1, p1, gP, b1, b2, hfin]

theorem r26t8a_p29_hessian (Q0 Psi : Euc d → Euc d → ℝ) {A1 B M1 MU Mf : ℝ} (hA1 : 0 ≤ A1) (hB : 0 ≤ B)
    (h1 : M1 ≤ Mf) (h2 : MU ≤ Mf)
    (hQd : ∀ x y : Euc d, x ≠ y → ContDiffAt ℝ 2 (Function.uncurry Q0) (x, y))
    (hQ : ∀ x y : Euc d, x ≠ y → ‖iteratedFDeriv ℝ 2 (Function.uncurry Q0) (x, y)‖ ≤
      A1 * Phase2S82.pairWeight M1 x y * (1 + smallRadius x y ^ (-criticalS d)))
    (hPd : ContDiff ℝ 8 (Function.uncurry Psi))
    (hP : ∀ x y : Euc d, ‖iteratedFDeriv ℝ 2 (Function.uncurry Psi) (x, y)‖ ≤ B * Phase2S82.pairWeight MU x y)
    {Afin : ℝ} (hA : A1 + B ≤ Afin) (x y : Euc d) (hxy : x ≠ y) :
    ‖iteratedFDeriv ℝ 2 (Function.uncurry (fun x y => Q0 x y + Psi x y)) (x, y)‖ ≤
      Afin * Phase2S82.pairWeight Mf x y * (1 + smallRadius x y ^ (-criticalS d)) := by
  set br : ℝ := 1 + smallRadius x y ^ (-criticalS d) with hbr
  have hbr1 : 1 ≤ br := by
    have : 0 ≤ smallRadius x y ^ (-criticalS d) := Real.rpow_nonneg (r26t8a_p29_smallRadius_nonneg x y) _
    rw [hbr]; linarith
  have hPc : ContDiffAt ℝ 2 (Function.uncurry Psi) (x, y) := (hPd.of_le (by norm_num)).contDiffAt
  have e : iteratedFDeriv ℝ 2 (Function.uncurry (fun x y => Q0 x y + Psi x y)) (x, y) =
      iteratedFDeriv ℝ 2 (Function.uncurry Q0) (x, y) + iteratedFDeriv ℝ 2 (Function.uncurry Psi) (x, y) := by
    have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := 2) (hQd x y hxy) hPc
    exact this
  have w1 := r26t8a_p29_pairWeight_mono h1 x y
  have w2 := r26t8a_p29_pairWeight_mono h2 x y
  have w0 := r26t8a_p29_pw_nonneg (d := d) Mf x y
  have q1 := hQ x y hxy
  have p1 := hP x y
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have b1 : A1 * Phase2S82.pairWeight M1 x y * br ≤ A1 * Phase2S82.pairWeight Mf x y * br :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left w1 hA1) (by linarith)
  have b2 : B * Phase2S82.pairWeight MU x y ≤ B * Phase2S82.pairWeight Mf x y * br := by
    calc B * Phase2S82.pairWeight MU x y ≤ B * Phase2S82.pairWeight Mf x y := mul_le_mul_of_nonneg_left w2 hB
      _ ≤ B * Phase2S82.pairWeight Mf x y * br := by nlinarith [mul_nonneg hB w0]
  have hfin : (A1 + B) * Phase2S82.pairWeight Mf x y * br ≤ Afin * Phase2S82.pairWeight Mf x y * br := by
    have : 0 ≤ Phase2S82.pairWeight Mf x y * br := mul_nonneg w0 (by linarith)
    nlinarith
  nlinarith [q1, p1, b1, b2, hfin]

end HRS.MS.R26T8A

end
