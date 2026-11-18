import HRS.MS.MovOpAux6
import HRS.MS.MovLinAux9

/-!
# S6.3 packet N2a (1): `movB` is bilinear on Schwartz functions

Namespace `HRS.MS.Mov63`, helper prefix `mnb_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.

For the thermal data (`MovRhoData d ρ`, `0 ≤ s < d`, `1 ≤ d`) and Schwartz `v, v₁, v₂, w, w₁, w₂`:

* `mnb_B_lin_left`: `B(a v₁ + b v₂, w) = a B(v₁, w) + b B(v₂, w)` (pointwise, everywhere);
* `mnb_B_lin_right`: `B(v, a w₁ + b w₂) = a B(v, w₁) + b B(v, w₂)` (pointwise, everywhere).

Both are proved from the explicit formula `mv1_B_formula` (the junk traps -- Bochner integrals in `movForce`, `fderiv` of
non-differentiable maps -- are excluded there: the integrands are continuous with Gaussian bounds, `mnb_conv_int`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS.Whole HRS.MS.MovForce

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- Continuous with a Gaussian bound. -/
def mnb_Gb (f : Euc d → ℝ) : Prop :=
  Continuous f ∧ ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ y, |f y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)

section Conv

variable {s : ℝ}

lemma mnb_conv_int (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : mnb_Gb f) (x : Euc d) :
    Integrable (fun z => rieszKernel d s z * f (x - z)) := by
  obtain ⟨hcont, C, c, hC, hc, hb⟩ := hf
  obtain ⟨hk, hB, hBint⟩ := mv1_g_data (d := d) hd hs0 hsd hc
  exact movtr_integrable_of_gauss_bound hc hk hB hBint hC hcont (x' := x) (R := ‖x‖) le_rfl hb

/-- Linearity of `g * ·` on Gaussian-bounded continuous functions. -/
lemma mnb_convFun_lin (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f1 f2 : Euc d → ℝ} (h1 : mnb_Gb f1)
    (h2 : mnb_Gb f2) (a b : ℝ) (x : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (fun y => a * f1 y + b * f2 y) x =
      a * HRS.Whole.convFun (rieszKernel d s) f1 x + b * HRS.Whole.convFun (rieszKernel d s) f2 x := by
  simp only [mv1_convFun_eq]
  have e : ∀ z, rieszKernel d s z * (a * f1 (x - z) + b * f2 (x - z)) =
      a * (rieszKernel d s z * f1 (x - z)) + b * (rieszKernel d s z * f2 (x - z)) := fun z => by ring
  simp_rw [e]
  rw [integral_add ((mnb_conv_int hd hs0 hsd h1 x).const_mul a) ((mnb_conv_int hd hs0 hsd h2 x).const_mul b),
    integral_const_mul, integral_const_mul]

end Conv

section Gauss

variable {ρ : Euc d → ℝ}

lemma mnb_Gb_partial (hρ : MovRhoData d ρ) (w : 𝓢R) (i : Fin d) :
    mnb_Gb (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) := by
  have hh := (mv1_h_gauss hρ w).1
  have hh' : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) (fun z => Real.sqrt (ρ z) * w z) := by
    have h2 : ContDiff ℝ 2 (fun z => Real.sqrt (ρ z) * w z) := hh.of_le (by norm_num)
    simpa using h2
  have hg : MovGauss (1 + 1) (fun z => Real.sqrt (ρ z) * w z) := mv1_h_movGauss hρ w _
  have hp := mv1_partial_contDiff (k := 1) hh' i
  obtain ⟨C, c, hC, hc, h0, -⟩ := mv1_gauss01 (mv1_gauss_partial (k := 1) hh' hg i)
  refine ⟨?_, C, c, hC, hc, fun y => ?_⟩
  · simp_rw [movtr_gradient_apply]
    exact hp.continuous
  · show |gradient (fun z => Real.sqrt (ρ z) * w z) y i| ≤ _
    rw [movtr_gradient_apply]; exact h0 y

lemma mnb_lap_formula (u : Euc d → ℝ) (y : Euc d) :
    Laplacian.laplacian u y = ∑ i, iteratedFDeriv ℝ 2 u y ![EuclideanSpace.single i (1 : ℝ),
      EuclideanSpace.single i (1 : ℝ)] := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin d) ℝ)) y
  simpa using this

lemma mnb_Gb_lap (hρ : MovRhoData d ρ) (w : 𝓢R) :
    mnb_Gb (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y) := by
  have hh := (mv1_h_gauss hρ w).1
  obtain ⟨C, c, hc, hb⟩ := (mv1_h_gauss hρ w).2 2
  have hcont : Continuous (iteratedFDeriv ℝ 2 (fun z => Real.sqrt (ρ z) * w z)) :=
    hh.continuous_iteratedFDeriv (m := 2) (by norm_num)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  refine ⟨?_, d * C, c, by positivity, hc, fun y => ?_⟩
  · simp_rw [mnb_lap_formula]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]).continuous.comp hcont
  · show |Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y| ≤ _
    rw [mnb_lap_formula]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i : Fin d, |iteratedFDeriv ℝ 2 (fun z => Real.sqrt (ρ z) * w z) y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]| ≤
        C * Real.exp (-c * ‖y‖ ^ 2) := fun i => by
      have h1 := (iteratedFDeriv ℝ 2 (fun z => Real.sqrt (ρ z) * w z) y).le_opNorm
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]
      have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hn, mul_one] at h1
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (hb y)
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)]

end Gauss

section Bilin

variable {s : ℝ} {ρ : Euc d → ℝ}

lemma mnb_h_diff (hρ : MovRhoData d ρ) (w : 𝓢R) : Differentiable ℝ (fun z => Real.sqrt (ρ z) * w z) :=
  ((mv1_h_gauss hρ w).1).differentiable (by simp)

lemma mnb_h_lin (a b : ℝ) (w1 w2 : 𝓢R) :
    (fun z => Real.sqrt (ρ z) * (a • w1 + b • w2) z) =
      fun z => a * (Real.sqrt (ρ z) * w1 z) + b * (Real.sqrt (ρ z) * w2 z) := by
  funext z; simp; ring

lemma mnb_grad_lin (hρ : MovRhoData d ρ) (a b : ℝ) (w1 w2 : 𝓢R) (y : Euc d) (i : Fin d) :
    gradient (fun z => Real.sqrt (ρ z) * (a • w1 + b • w2) z) y i =
      a * gradient (fun z => Real.sqrt (ρ z) * w1 z) y i + b * gradient (fun z => Real.sqrt (ρ z) * w2 z) y i := by
  rw [movtr_gradient_apply, mnb_h_lin, movtr_gradient_apply, movtr_gradient_apply]
  have := ((mnb_h_diff hρ w1 y).hasFDerivAt.const_mul a).add ((mnb_h_diff hρ w2 y).hasFDerivAt.const_mul b)
  have h : HasFDerivAt (fun z => a * (Real.sqrt (ρ z) * w1 z) + b * (Real.sqrt (ρ z) * w2 z))
      (a • fderiv ℝ (fun z => Real.sqrt (ρ z) * w1 z) y + b • fderiv ℝ (fun z => Real.sqrt (ρ z) * w2 z) y) y := this
  rw [h.fderiv]; simp

lemma mnb_lap_lin (hρ : MovRhoData d ρ) (a b : ℝ) (w1 w2 : 𝓢R) (y : Euc d) :
    Laplacian.laplacian (fun z => Real.sqrt (ρ z) * (a • w1 + b • w2) z) y =
      a * Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w1 z) y +
        b * Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w2 z) y := by
  have hc1 : ContDiffAt ℝ 2 (fun z => Real.sqrt (ρ z) * w1 z) y :=
    ((mv1_h_gauss hρ w1).1.of_le (by norm_num)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun z => Real.sqrt (ρ z) * w2 z) y :=
    ((mv1_h_gauss hρ w2).1.of_le (by norm_num)).contDiffAt
  have e : (fun z => Real.sqrt (ρ z) * (a • w1 + b • w2) z) =
      a • (fun z => Real.sqrt (ρ z) * w1 z) + b • (fun z => Real.sqrt (ρ z) * w2 z) := by
    funext z; simp; ring
  have hs1 : ContDiffAt ℝ 2 (a • fun z => Real.sqrt (ρ z) * w1 z) y := hc1.const_smul a
  have hs2 : ContDiffAt ℝ 2 (b • fun z => Real.sqrt (ρ z) * w2 z) y := hc2.const_smul b
  rw [e, ContDiffAt.laplacian_add hs1 hs2, InnerProductSpace.laplacian_smul a hc1,
    InnerProductSpace.laplacian_smul b hc2]
  simp

/-- `B(v, a w₁ + b w₂) = a B(v, w₁) + b B(v, w₂)`, pointwise. -/
theorem mnb_B_lin_right (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : MovRhoData d ρ) (v w1 w2 : 𝓢R)
    (a b : ℝ) (x : Euc d) :
    movB d s ρ (⇑v) (fun z => a * w1 z + b * w2 z) x =
      a * movB d s ρ (⇑v) (⇑w1) x + b * movB d s ρ (⇑v) (⇑w2) x := by
  set W : 𝓢R := a • w1 + b • w2 with hWdef
  have hW : (fun z => a * w1 z + b * w2 z) = ⇑W := by funext z; simp [hWdef]
  have hvd : Differentiable ℝ (⇑v) := (v.smooth ⊤).differentiable (by simp)
  rw [hW, mv1_B_formula hd hs0 hsd hρ hvd W x, mv1_B_formula hd hs0 hsd hρ hvd w1 x,
    mv1_B_formula hd hs0 hsd hρ hvd w2 x]
  have hg : ∀ i : Fin d, HRS.Whole.convFun (rieszKernel d s)
      (fun y => gradient (fun z => Real.sqrt (ρ z) * W z) y i) x =
      a * HRS.Whole.convFun (rieszKernel d s) (fun y => gradient (fun z => Real.sqrt (ρ z) * w1 z) y i) x +
      b * HRS.Whole.convFun (rieszKernel d s) (fun y => gradient (fun z => Real.sqrt (ρ z) * w2 z) y i) x :=
    fun i => by
      have : (fun y => gradient (fun z => Real.sqrt (ρ z) * W z) y i) =
          fun y => a * gradient (fun z => Real.sqrt (ρ z) * w1 z) y i +
            b * gradient (fun z => Real.sqrt (ρ z) * w2 z) y i :=
        funext fun y => mnb_grad_lin hρ a b w1 w2 y i
      rw [this]
      exact mnb_convFun_lin hd hs0 hsd (mnb_Gb_partial hρ w1 i) (mnb_Gb_partial hρ w2 i) a b x
  have hl : HRS.Whole.convFun (rieszKernel d s)
      (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * W z) y) x =
      a * HRS.Whole.convFun (rieszKernel d s) (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w1 z) y) x +
      b * HRS.Whole.convFun (rieszKernel d s) (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w2 z) y) x := by
    have : (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * W z) y) =
        fun y => a * Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w1 z) y +
          b * Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w2 z) y :=
      funext fun y => mnb_lap_lin hρ a b w1 w2 y
    rw [this]
    exact mnb_convFun_lin hd hs0 hsd (mnb_Gb_lap hρ w1) (mnb_Gb_lap hρ w2) a b x
  simp only [hg, hl]
  set C1 : Fin d → ℝ := fun i => HRS.Whole.convFun (rieszKernel d s)
    (fun y => gradient (fun z => Real.sqrt (ρ z) * w1 z) y i) x with hC1
  set C2 : Fin d → ℝ := fun i => HRS.Whole.convFun (rieszKernel d s)
    (fun y => gradient (fun z => Real.sqrt (ρ z) * w2 z) y i) x with hC2
  have s1 : ∑ i, gradient (⇑v) x i * (a * C1 i + b * C2 i) =
      a * ∑ i, gradient (⇑v) x i * C1 i + b * ∑ i, gradient (⇑v) x i * C2 i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have s2 : ∑ i, gradient (fun y => Real.log (ρ y)) x i * (a * C1 i + b * C2 i) =
      a * ∑ i, gradient (fun y => Real.log (ρ y)) x i * C1 i +
        b * ∑ i, gradient (fun y => Real.log (ρ y)) x i * C2 i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [s1, s2]
  ring

/-- `B(a v₁ + b v₂, w) = a B(v₁, w) + b B(v₂, w)`, pointwise. -/
theorem mnb_B_lin_left (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : MovRhoData d ρ) (v1 v2 w : 𝓢R)
    (a b : ℝ) (x : Euc d) :
    movB d s ρ (fun z => a * v1 z + b * v2 z) (⇑w) x =
      a * movB d s ρ (⇑v1) (⇑w) x + b * movB d s ρ (⇑v2) (⇑w) x := by
  have hv1 : Differentiable ℝ (⇑v1) := (v1.smooth ⊤).differentiable (by simp)
  have hv2 : Differentiable ℝ (⇑v2) := (v2.smooth ⊤).differentiable (by simp)
  have hV : Differentiable ℝ (fun z => a * v1 z + b * v2 z) :=
    (hv1.const_mul a).add (hv2.const_mul b)
  rw [mv1_B_formula hd hs0 hsd hρ hV w x, mv1_B_formula hd hs0 hsd hρ hv1 w x,
    mv1_B_formula hd hs0 hsd hρ hv2 w x]
  have hgr : ∀ i : Fin d, gradient (fun z => a * v1 z + b * v2 z) x i =
      a * gradient (⇑v1) x i + b * gradient (⇑v2) x i := fun i => by
    rw [movtr_gradient_apply, movtr_gradient_apply, movtr_gradient_apply]
    have := ((hv1 x).hasFDerivAt.const_mul a).add ((hv2 x).hasFDerivAt.const_mul b)
    have h : HasFDerivAt (fun z => a * v1 z + b * v2 z) (a • fderiv ℝ (⇑v1) x + b • fderiv ℝ (⇑v2) x) x := this
    rw [h.fderiv]; simp
  simp only [hgr]
  set C : Fin d → ℝ := fun i => HRS.Whole.convFun (rieszKernel d s)
    (fun y => gradient (fun z => Real.sqrt (ρ z) * w z) y i) x with hC
  set K : ℝ := HRS.Whole.convFun (rieszKernel d s)
    (fun y => Laplacian.laplacian (fun z => Real.sqrt (ρ z) * w z) y) x +
      (1 / 2) * ∑ i, gradient (fun y => Real.log (ρ y)) x i * C i with hK
  have s1 : ∑ i, (a * gradient (⇑v1) x i + b * gradient (⇑v2) x i) * C i =
      a * ∑ i, gradient (⇑v1) x i * C i + b * ∑ i, gradient (⇑v2) x i * C i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [s1]
  ring

end Bilin

end HRS.MS.Mov63

end
