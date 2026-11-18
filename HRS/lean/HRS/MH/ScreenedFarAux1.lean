import HRS.MH.ScreenedA2
import HRS.MH.ScreenedA3a
import HRS.MH.ScreenedA6
import HRS.MH.ScreenedA7
import HRS.MH.ScreenedF3
import HRS.MH.ScreenedF4
import HRS.MH.ScreenedF5
import HRS.MH.ScreenedF6
import HRS.Whole.MovtrAux4

/-! Helper lemmas for `far_core` of `B:lem:screened` (S.B.4): kernel bound on the far region, cell comparison,
pointwise estimate and the squared cell estimate. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma far_kernel_const {s : ℝ} (hs0 : 0 ≤ s) (L : ℝ) (hL : 1 ≤ L) (u : Euc d) (hu : 4 / L ≤ ‖u‖) :
    ‖rieszKernelGrad d s u‖ ≤ max 1 s * (4 / L) ^ (-s - 1) := by
  have hL0 : 0 < L := by linarith
  have hpos : 0 < 4 / L := by positivity
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; linarith
  refine (kernel_bound_proof hs0 u hu0).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos hu (by linarith))
    (le_trans zero_le_one (le_max_left _ _))

lemma far_jb_cell (Kw : ℝ) (hKw : 0 < Kw) {y c : Euc d} (h : jbracket c ≤ Kw * jbracket y) :
    jbracket y ^ (-((d : ℝ) + 3)) ≤ Kw ^ ((d : ℝ) + 3) * jbracket c ^ (-((d : ℝ) + 3)) := by
  have hy : 0 < jbracket y := by unfold jbracket; positivity
  have hc : 0 < jbracket c := by unfold jbracket; positivity
  have hp : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
  have h1 : jbracket c ^ ((d : ℝ) + 3) ≤ Kw ^ ((d : ℝ) + 3) * jbracket y ^ ((d : ℝ) + 3) := by
    rw [← Real.mul_rpow hKw.le hy.le]
    exact Real.rpow_le_rpow hc.le h hp
  have hA : 0 < jbracket y ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos hy _
  have hC : 0 < jbracket c ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos hc _
  rw [Real.rpow_neg hy.le, Real.rpow_neg hc.le]
  simp only [inv_eq_one_div]
  rw [mul_one_div, div_le_div_iff₀ hA hC]
  linarith

lemma far_ptwise {s : ℝ} (hs0 : 0 ≤ s) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (L : ℝ) (hL : 1 ≤ L)
    (hsep : ∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
        y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 / L ≤ ‖x - y‖)
    (z : Euc d) (Λ' : ℝ) (hΛ' : 0 ≤ Λ') (a ψ : Euc d → ℝ)
    (ha : ∀ y, jbracket y ^ ((d : ℝ) + 3) * |a y| ≤ Λ')
    (x : Euc d) (hx : x ∈ tsupport (advCutoff χ Ψ τ z)) (y : Euc d) :
    ‖(1 - advCutoff χh Ψ τ z y) * (a y * ψ y)‖ₑ * ‖rieszKernelGrad d s (x - y)‖ₑ ≤
      ENNReal.ofReal (max 1 s * (4 / L) ^ (-s - 1) * Λ' * jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ := by
  by_cases h0 : 1 - advCutoff χh Ψ τ z y = 0
  · simp [h0]
  have hL0 : 0 < L := by linarith
  have hy : y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) := subset_tsupport _ h0
  have hxy := hsep z x y hx hy
  have hK := far_kernel_const (d := d) hs0 L hL (x - y) hxy
  have hrange : advCutoff χh Ψ τ z y ∈ Icc (0 : ℝ) 1 :=
    hχ.2.2.2.2.1 (Function.invFun (Ψ τ) y - z)
  have hc : |1 - advCutoff χh Ψ τ z y| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hrange.1, hrange.2]
  have hjbp : 0 < jbracket y := by unfold jbracket; positivity
  have hjb : 0 < jbracket y ^ (-((d : ℝ) + 3)) := Real.rpow_pos_of_pos hjbp _
  have ha' : |a y| ≤ Λ' * jbracket y ^ (-((d : ℝ) + 3)) := by
    have h1 : jbracket y ^ (-((d : ℝ) + 3)) * jbracket y ^ ((d : ℝ) + 3) = 1 := by
      rw [← Real.rpow_add hjbp]; simp
    calc |a y| = jbracket y ^ (-((d : ℝ) + 3)) * (jbracket y ^ ((d : ℝ) + 3) * |a y|) := by
          rw [← mul_assoc, h1, one_mul]
      _ ≤ jbracket y ^ (-((d : ℝ) + 3)) * Λ' := mul_le_mul_of_nonneg_left (ha y) hjb.le
      _ = _ := mul_comm _ _
  have hκ : 0 ≤ max 1 s * (4 / L) ^ (-s - 1) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (Real.rpow_nonneg (by positivity) _)
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Real.norm_eq_abs, abs_mul]
  calc |1 - advCutoff χh Ψ τ z y| * (|a y| * |ψ y|) * ‖rieszKernelGrad d s (x - y)‖
      ≤ 1 * ((Λ' * jbracket y ^ (-((d : ℝ) + 3))) * |ψ y|) * (max 1 s * (4 / L) ^ (-s - 1)) := by
        gcongr
    _ = _ := by ring

lemma far_eLpNorm_sq (f : Euc d → ℝ) (hf : AEStronglyMeasurable f volume) :
    (eLpNorm f 2 volume) ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact a2_sq_sqrt _

lemma far_I_sq (hd : 1 ≤ d) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hbij : Function.Bijective (Ψ τ))
    (hlip : ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ L * ‖x - y‖)
    (hlipi : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ L * ‖x - y‖)
    (horig : ‖Ψ τ 0‖ ≤ B) (c1 : ℝ) (hc1 : 0 ≤ c1) (ψ : Euc d → ℝ) (hψ : Measurable ψ) :
    (∫⁻ y, ENNReal.ofReal (c1 * jbracket y ^ (-((d : ℝ) + 3))) * ‖ψ y‖ₑ) ^ 2 ≤
      (ENNReal.ofReal (c1 * (L + L * B + Real.sqrt d + 1) ^ ((d : ℝ) + 3)) *
          (∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z)) *
          volume (Metric.closedBall (0 : Euc d) (L * Real.sqrt d))) *
        (ENNReal.ofReal (c1 * (L + L * B + Real.sqrt d + 1) ^ ((d : ℝ) + 3)) *
          ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') *
            (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hgeo := flowCell_geometry_proof Ψ τ L hL0.le hbij hlip
  have hw := flowCell_weight_proof Ψ τ L B hL0.le hB hbij hlipi horig
  have hKw : 0 < L + L * B + Real.sqrt d + 1 := by positivity
  set Kw := L + L * B + Real.sqrt d + 1 with hKwdef
  set E := ENNReal.ofReal (c1 * Kw ^ ((d : ℝ) + 3)) with hE
  have h := cell_cs_proof (flowCell Ψ τ) hgeo.1 hgeo.2.1
    (volume (Metric.closedBall (0 : Euc d) (L * Real.sqrt d)))
    (fun z => by
      rw [← Measure.addHaar_closedBall_center volume (Ψ τ (latticePt z))]
      exact measure_mono (hgeo.2.2.1 z))
    (fun z => E * ENNReal.ofReal (cellWeight d z))
    (fun y => ENNReal.ofReal (c1 * jbracket y ^ (-((d : ℝ) + 3))))
    (fun i y hy => by
      have h1 := far_jb_cell (d := d) Kw hKw (hw i y hy)
      calc ENNReal.ofReal (c1 * jbracket y ^ (-((d : ℝ) + 3)))
          ≤ ENNReal.ofReal (c1 * (Kw ^ ((d : ℝ) + 3) * cellWeight d i)) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1 hc1)
        _ = E * ENNReal.ofReal (cellWeight d i) := by
            rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)])
    ψ hψ
  have h1 : ∑' i : Fin d → ℤ, E * ENNReal.ofReal (cellWeight d i) =
      E * ∑' i : Fin d → ℤ, ENNReal.ofReal (cellWeight d i) := ENNReal.tsum_mul_left
  have h2 : ∑' i : Fin d → ℤ, E * ENNReal.ofReal (cellWeight d i) *
      (eLpNorm ((flowCell Ψ τ i).indicator ψ) 2 volume) ^ 2 =
      E * ∑' z' : Fin d → ℤ, ENNReal.ofReal (cellWeight d z') *
        (eLpNorm ((flowCell Ψ τ z').indicator ψ) 2 volume) ^ 2 := by
    simp_rw [mul_assoc]; exact ENNReal.tsum_mul_left
  rw [h1, h2] at h
  exact h

lemma far_meas_grad {s : ℝ} (G : Euc d → ℝ) (hG : Measurable G) (i : Fin d) :
    StronglyMeasurable (fun x => gradGConvPlain d s G x i) := by
  have hf : Measurable (fun p : Euc d × Euc d => G p.2 • rieszKernelGrad d s (p.1 - p.2)) :=
    (hG.comp measurable_snd).smul
      ((movtr_rieszKernelGrad_measurable s).comp (measurable_fst.sub measurable_snd))
  have h := StronglyMeasurable.integral_prod_right (ν := (volume : Measure (Euc d)))
    (f := fun x y => G y • rieszKernelGrad d s (x - y)) hf.stronglyMeasurable
  exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_stronglyMeasurable h

end HRS.MH.Screened
