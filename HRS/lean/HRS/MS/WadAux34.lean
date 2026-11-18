import HRS.MS.WadAux33

/-!
# S8.3, packet D7c (Route A): `s84_Bop` is linear on `C²_b`

`s84_C2b h B`: `h ∈ C²` with `‖Dh‖, ‖D²h‖ ≤ B`.  For such `h` the components `u_j = ρ (Mᵀ∇h)_j` are
bounded by a multiple of `(1+‖y‖)^{-(d+1)}` and locally Hölder-1/2 (`s84_u_facts`), hence the conv integrals
converge absolutely and `s84_Bop` is additive (`s84_Bop_sub`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

def s84_C2b (h : Euc d → ℝ) (B : ℝ) : Prop :=
  ContDiff ℝ 2 h ∧ ∀ y, ‖fderiv ℝ h y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B

theorem s84_gradient_sub {h₁ h₂ : Euc d → ℝ} (d1 : Differentiable ℝ h₁) (d2 : Differentiable ℝ h₂)
    (y : Euc d) : gradient (fun y => h₁ y - h₂ y) y = gradient h₁ y - gradient h₂ y := by
  unfold gradient
  have : fderiv ℝ (fun y => h₁ y - h₂ y) y = fderiv ℝ h₁ y - fderiv ℝ h₂ y :=
    fderiv_sub (d1 y) (d2 y)
  rw [this, map_sub]

theorem s84_u_facts (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) :
    ∃ Lu : ℝ, 0 ≤ Lu ∧ ∀ {h : Euc d → ℝ} {B : ℝ}, s84_C2b h B → ∀ j : Fin d,
      Measurable (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) ∧
      (∀ y, |ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
        (Lu * B) * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x,
        |ρ (x - z) * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h (x - z))) j -
          ρ x * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h x)) j| ≤
        (Lu * B) * ‖z‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨hρd, C, c, hC0, hc, hρb⟩ := hρ
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := (d : ℝ) + 1) (c := c) (by positivity) hc
  refine ⟨C * KB + C, by positivity, ?_⟩
  intro h B ⟨hc2, hB⟩ j
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0).1
  have hexp1 : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) ≤ KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro y
    have h1 := hKB y
    have hp : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hp.le]
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hp _
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    nlinarith [h1]
  have hcomp : ∀ y : Euc d, |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
      ‖fderiv ℝ h y‖ := fun y => by
    rw [s84_matVec_neg_T]
    simp only [PiLp.neg_apply, abs_neg]
    rw [← Real.norm_eq_abs, ← s84_grad_norm]
    exact PiLp.norm_apply_le (gradient h y) j
  have hcompd : ∀ y y' : Euc d, |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y')) j -
      (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
      ‖fderiv ℝ h y' - fderiv ℝ h y‖ := fun y y' => by
    rw [s84_matVec_neg_T, s84_matVec_neg_T]
    simp only [PiLp.neg_apply]
    rw [show -(gradient h y') j - -(gradient h y) j = -((gradient h y' - gradient h y) j) by simp; ring,
      abs_neg, ← Real.norm_eq_abs, ← s84_grad_sub]
    exact PiLp.norm_apply_le (gradient h y' - gradient h y) j
  have hgc : Continuous (gradient h) := by
    have : gradient h = fun y => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ h y) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hc2.continuous_fderiv (by norm_num))
  refine ⟨?_, fun y => ?_, fun z hz x => ?_⟩
  · refine (hρd.continuous.measurable).mul ?_
    simp only [s84_matVec_neg_T]
    exact ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hgc.neg).measurable
  · rw [abs_mul]
    calc |ρ y| * |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j|
        ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * B := mul_le_mul (hρb y).1 ((hcomp y).trans (hB y).1)
            (abs_nonneg _) (by positivity)
      _ ≤ (C * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))) * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp1 y) hC0) hB0
      _ = (C * KB * B) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by ring
      _ ≤ ((C * KB + C) * B) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          nlinarith [mul_nonneg hC0 hB0]
  · set vv : Euc d → ℝ := fun y => (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j
      with hvv
    have hd1 : Differentiable ℝ (fderiv ℝ h) :=
      (hc2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have hLipD : ‖fderiv ℝ h (x - z) - fderiv ℝ h x‖ ≤ B * ‖z‖ := by
      have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
        (f := fderiv ℝ h) (C := B) (fun y _ => hd1 y) (fun y _ => (hB y).2)
        (Set.mem_univ x) (Set.mem_univ (x - z))
      rwa [sub_sub_cancel_left, norm_neg] at this
    have hLipρ : |ρ (x - z) - ρ x| ≤ C * ‖z‖ := by
      have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le (f := ρ) (C := C)
        (fun y _ => hρd y) (fun y _ => ((hρb y).2).trans (by
          have : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖y‖]
          nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)])) (Set.mem_univ x) (Set.mem_univ (x - z))
      rw [Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] at this
      exact this
    have hρ1 : |ρ (x - z)| ≤ C := (hρb _).1.trans (by
      have : Real.exp (-c * ‖x - z‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x - z‖]
      nlinarith [Real.exp_pos (-c * ‖x - z‖ ^ 2)])
    have e : ρ (x - z) * vv (x - z) - ρ x * vv x =
        ρ (x - z) * (vv (x - z) - vv x) + (ρ (x - z) - ρ x) * vv x := by ring
    show |ρ (x - z) * vv (x - z) - ρ x * vv x| ≤ _
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 : |ρ (x - z)| * |vv (x - z) - vv x| ≤ C * (B * ‖z‖) :=
      mul_le_mul hρ1 ((hcompd x (x - z)).trans hLipD) (abs_nonneg _) hC0
    have t2 : |ρ (x - z) - ρ x| * |vv x| ≤ (C * ‖z‖) * B :=
      mul_le_mul hLipρ ((hcomp x).trans (hB x).1) (abs_nonneg _) (by positivity)
    have hh := s84_norm_le_sqrt hz
    have hS0 : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have hCB0 : 0 ≤ C * B := mul_nonneg hC0 hB0
    calc _ ≤ C * (B * ‖z‖) + (C * ‖z‖) * B := add_le_add t1 t2
      _ = (C * B) * (2 * ‖z‖) := by ring
      _ ≤ (C * B) * ‖z‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hCB0
      _ ≤ ((C * KB + C) * B) * ‖z‖ ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hS0
          nlinarith [mul_nonneg (mul_nonneg hC0 hKB0) hB0]

/-- **Additivity of the first-order remainder on `C²_b`.** -/
theorem s84_Bop_sub (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {h₁ h₂ : Euc d → ℝ} {B₁ B₂ : ℝ}
    (h1 : s84_C2b h₁ B₁) (h2 : s84_C2b h₂ B₂) (x : Euc d) :
    s84_Bop ρ (fun y => h₁ y - h₂ y) x = s84_Bop ρ h₁ x - s84_Bop ρ h₂ x := by
  obtain ⟨Lu, hLu0, hLu⟩ := s84_u_facts hd hρ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hs1 : (d : ℝ) / 2 + 1 / 2 < (d : ℝ) := by linarith
  have dd1 : Differentiable ℝ h₁ := h1.1.differentiable (by norm_num)
  have dd2 : Differentiable ℝ h₂ := h2.1.differentiable (by norm_num)
  have hB10 : 0 ≤ B₁ := (norm_nonneg _).trans (h1.2 0).1
  have hB20 : 0 ≤ B₂ := (norm_nonneg _).trans (h2.2 0).1
  unfold s84_Bop
  have e1 : inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient (fun y => h₁ y - h₂ y) x) =
      inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
        (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient h₁ x) -
      inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
        (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient h₂ x) := by
    rw [s84_gradient_sub dd1 dd2, inner_sub_right]
  have e2 : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
      (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient (fun y => h₁ y - h₂ y) y)) j) x) j =
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₁ y)) j) x) j -
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₂ y)) j) x) j := by
    intro j
    obtain ⟨m1, a1, hh1⟩ := hLu h1 j
    obtain ⟨m2, a2, hh2⟩ := hLu h2 j
    have hi1 := s84_conv_integrable hd hs0 hs1 (by positivity) (by positivity) m1 a1 hh1 x
    have hi2 := s84_conv_integrable hd hs0 hs1 (by positivity) (by positivity) m2 a2 hh2 x
    have hfun : (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient (fun y => h₁ y - h₂ y) y)) j) =
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₁ y)) j -
          ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₂ y)) j) := by
      funext y
      rw [s84_gradient_sub dd1 dd2, s84_matVec_neg_T, s84_matVec_neg_T, s84_matVec_neg_T]
      simp only [PiLp.neg_apply, PiLp.sub_apply]
      ring
    rw [hfun, s84_conv_sub (u₁ := fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h₁ y)) j) (u₂ := fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h₂ y)) j) x hi1 hi2, PiLp.sub_apply]
  rw [e1, Finset.sum_congr rfl fun j _ => e2 j, Finset.sum_sub_distrib]
  ring

end HRS.MS.Wad
