import HRS.MS.WadAux182

/-!
# S8.3, packet S8H2-9: linearity of the projected generator on the weighted `C^2` class

`s8h2_proj_sub`: for `g₁, g₂ ∈ C^2` with `‖Dg_i‖ ≤ V_i⟨y⟩^M`, `‖D²g_i‖ ≤ W_i⟨y⟩^M`: `𝒜(g₁ - g₂)(x) = 𝒜g₁(x) - 𝒜g₂(x)` (the cancellation
convolutions converge absolutely, `s8h2_u_facts`, and `generatorW g_i` is `μ`-integrable); `s8h2_proj_smul`.  This is the linearity needed
to pass to the limit with the bound `s8g_gen_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Weighted `C^2` class. -/
def S8hCls (M V W : ℝ) (g : Euc d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ (∀ y, ‖fderiv ℝ g y‖ ≤ V * jbracket y ^ M) ∧
    ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ W * jbracket y ^ M

theorem s8h2_u_facts (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ Lu : ℝ, 0 ≤ Lu ∧ ∀ {h : Euc d → ℝ} {V W : ℝ}, 0 ≤ V → 0 ≤ W → S8hCls M V W h → ∀ j : Fin d,
      Measurable (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) ∧
      (∀ y, |ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
        (Lu * (V + W)) * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x,
        |ρ (x - z) * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h (x - z))) j -
          ρ x * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h x)) j| ≤
        (Lu * (V + W)) * ‖z‖ ^ (1 / 2 : ℝ)) := by
  obtain ⟨hρd, C, c, hC0, hc, hρb⟩ := hρ
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := (d : ℝ) + 1 + M) (c := c)
    (by have := Nat.cast_nonneg (α := ℝ) d; linarith) hc
  have hpowgauss : ∀ y : Euc d, (1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2) ≤
      KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro y
    have h1 := hKB y
    have hp : 0 < 1 + ‖y‖ := by positivity
    have e : (1 + ‖y‖) ^ ((d : ℝ) + 1 + M) = (1 + ‖y‖) ^ M * (1 + ‖y‖) ^ ((d : ℝ) + 1) := by
      rw [show ((d : ℝ) + 1 + M) = M + ((d : ℝ) + 1) by ring, Real.rpow_add hp]
    rw [e] at h1
    rw [Real.rpow_neg hp.le]
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hp _
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    have : (1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2) * (1 + ‖y‖) ^ ((d : ℝ) + 1) =
        (1 + ‖y‖) ^ M * (1 + ‖y‖) ^ ((d : ℝ) + 1) * Real.exp (-c * ‖y‖ ^ 2) := by ring
    rw [this]
    exact h1
  have hKB1 : ∀ y : Euc d, (1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2) ≤ KB := fun y =>
    (hpowgauss y).trans (by
      have h1 : (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith)
      nlinarith)
  have h2M : (0 : ℝ) ≤ 2 ^ M := Real.rpow_nonneg (by norm_num) M
  refine ⟨C * KB * (1 + 2 ^ M * 2 ^ M + 2 ^ M), by positivity, ?_⟩
  intro h V W hV hW ⟨hc2, hDh, hD2h⟩ j
  have hjy : ∀ y : Euc d, 0 ≤ jbracket y ^ M := fun y => Real.rpow_nonneg (s83_jb_pos y).le M
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
    have hjle : jbracket y ^ M ≤ (1 + ‖y‖) ^ M :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM
    have hcomp' : |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
        V * (1 + ‖y‖) ^ M :=
      (hcomp y).trans ((hDh y).trans (mul_le_mul_of_nonneg_left hjle hV))
    have hq0 : 0 ≤ (1 + ‖y‖) ^ M := Real.rpow_nonneg (by positivity) _
    calc |ρ y| * |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j|
        ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (V * (1 + ‖y‖) ^ M) :=
          mul_le_mul (hρb y).1 hcomp' (abs_nonneg _) (by positivity)
      _ = (C * V) * ((1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ (C * V) * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (hpowgauss y) (mul_nonneg hC0 hV)
      _ = (C * KB * V) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by ring
      _ ≤ (C * KB * (1 + 2 ^ M * 2 ^ M + 2 ^ M) * (V + W)) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          have hCK : 0 ≤ C * KB := mul_nonneg hC0 hKB0
          nlinarith [mul_nonneg hCK hV, mul_nonneg hCK hW, mul_nonneg (mul_nonneg hCK hV) (mul_nonneg h2M h2M),
            mul_nonneg (mul_nonneg hCK hV) h2M, mul_nonneg (mul_nonneg hCK hW) (mul_nonneg h2M h2M),
            mul_nonneg (mul_nonneg hCK hW) h2M]
  · set vv : Euc d → ℝ := fun y => (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j
      with hvv
    have hd1 : Differentiable ℝ (fderiv ℝ h) :=
      (hc2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have hjx0 := s83_jb_pos x
    have hjxz := s83_jb_pos (x - z)
    have hz0 := norm_nonneg z
    -- comparison of the weights near `x`
    have hjball : ∀ y ∈ Metric.closedBall x ‖z‖, jbracket y ≤ 2 * jbracket x := by
      intro y hy
      have hy' : ‖y - x‖ ≤ ‖z‖ := mem_closedBall_iff_norm.1 hy
      have h1 := s83_jb_lipschitz y x
      have h2 := abs_le.1 h1
      have h3 := s83_one_le_jb x
      linarith [h2.2]
    have hjball' : ∀ y ∈ Metric.closedBall x ‖z‖, jbracket x ≤ 2 * jbracket y := by
      intro y hy
      have hy' : ‖y - x‖ ≤ ‖z‖ := mem_closedBall_iff_norm.1 hy
      have h1 := s83_jb_lipschitz y x
      have h2 := abs_le.1 h1
      have h3 := s83_one_le_jb y
      linarith [h2.1]
    have hLipD : ‖fderiv ℝ h (x - z) - fderiv ℝ h x‖ ≤ W * 2 ^ M * jbracket x ^ M * ‖z‖ := by
      have hb : ∀ y ∈ Metric.closedBall x ‖z‖, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ W * 2 ^ M * jbracket x ^ M := by
        intro y hy
        have h4 : jbracket y ^ M ≤ (2 * jbracket x) ^ M :=
          Real.rpow_le_rpow (s83_jb_pos y).le (hjball y hy) hM
        rw [Real.mul_rpow (by norm_num) hjx0.le] at h4
        calc ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ W * jbracket y ^ M := hD2h y
          _ ≤ W * (2 ^ M * jbracket x ^ M) := mul_le_mul_of_nonneg_left h4 hW
          _ = _ := by ring
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ h)
        (C := W * 2 ^ M * jbracket x ^ M) (s := Metric.closedBall x ‖z‖) (fun y _ => hd1 y) hb
        (convex_closedBall _ _) (mem_closedBall_self hz0) (x := x) (y := x - z)
        (by rw [mem_closedBall_iff_norm, sub_sub_cancel_left, norm_neg])
      rwa [sub_sub_cancel_left, norm_neg] at hmv
    have hLipρ : |ρ (x - z) - ρ x| ≤ (2 ^ M * C * KB / jbracket x ^ M) * ‖z‖ := by
      have hb : ∀ y ∈ Metric.closedBall x ‖z‖, ‖fderiv ℝ ρ y‖ ≤ 2 ^ M * C * KB / jbracket x ^ M := by
        intro y hy
        have hxp := Real.rpow_pos_of_pos hjx0 M
        rw [le_div_iff₀ hxp]
        have h4 : jbracket x ^ M ≤ (2 * jbracket y) ^ M :=
          Real.rpow_le_rpow hjx0.le (hjball' y hy) hM
        rw [Real.mul_rpow (by norm_num) (s83_jb_pos y).le] at h4
        have h5 : jbracket y ^ M ≤ (1 + ‖y‖) ^ M :=
          Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM
        calc ‖fderiv ℝ ρ y‖ * jbracket x ^ M ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (2 ^ M * (1 + ‖y‖) ^ M) :=
              mul_le_mul (hρb y).2 (h4.trans (mul_le_mul_of_nonneg_left h5 h2M)) hxp.le (by positivity)
          _ = 2 ^ M * C * ((1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2)) := by ring
          _ ≤ 2 ^ M * C * KB := mul_le_mul_of_nonneg_left (hKB1 y) (mul_nonneg h2M hC0)
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := ρ)
        (C := 2 ^ M * C * KB / jbracket x ^ M) (s := Metric.closedBall x ‖z‖) (fun y _ => hρd y) hb
        (convex_closedBall _ _) (mem_closedBall_self hz0) (x := x) (y := x - z)
        (by rw [mem_closedBall_iff_norm, sub_sub_cancel_left, norm_neg])
      rw [Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] at hmv
      exact hmv
    have hρ1 : |ρ (x - z)| ≤ C * Real.exp (-c * ‖x - z‖ ^ 2) := (hρb _).1
    have hx2 : jbracket x ^ M ≤ 2 ^ M * (1 + ‖x - z‖) ^ M := by
      have h1 : jbracket x ≤ 2 * jbracket (x - z) := by
        have h2 := abs_le.1 (s83_jb_lipschitz x (x - z))
        have h3 := s83_one_le_jb (x - z)
        have h4 : ‖x - (x - z)‖ = ‖z‖ := by rw [sub_sub_cancel]
        rw [h4] at h2
        linarith [h2.2]
      have h2 : jbracket x ^ M ≤ (2 * jbracket (x - z)) ^ M := Real.rpow_le_rpow hjx0.le h1 hM
      rw [Real.mul_rpow (by norm_num) hjxz.le] at h2
      exact h2.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hjxz.le (s83_jb_le_one_add _) hM) h2M)
    have e : ρ (x - z) * vv (x - z) - ρ x * vv x =
        ρ (x - z) * (vv (x - z) - vv x) + (ρ (x - z) - ρ x) * vv x := by ring
    show |ρ (x - z) * vv (x - z) - ρ x * vv x| ≤ _
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hxp := Real.rpow_pos_of_pos hjx0 M
    have t1 : |ρ (x - z)| * |vv (x - z) - vv x| ≤ (C * (W * 2 ^ M * 2 ^ M * KB)) * ‖z‖ := by
      have h1 : |vv (x - z) - vv x| ≤ W * 2 ^ M * jbracket x ^ M * ‖z‖ :=
        (hcompd x (x - z)).trans hLipD
      have hq0 : 0 ≤ (1 + ‖x - z‖) ^ M := Real.rpow_nonneg (by positivity) _
      calc |ρ (x - z)| * |vv (x - z) - vv x| ≤ (C * Real.exp (-c * ‖x - z‖ ^ 2)) *
            (W * 2 ^ M * (2 ^ M * (1 + ‖x - z‖) ^ M) * ‖z‖) := by
            refine mul_le_mul hρ1 (h1.trans ?_) (abs_nonneg _) (by positivity)
            have : W * 2 ^ M * jbracket x ^ M ≤ W * 2 ^ M * (2 ^ M * (1 + ‖x - z‖) ^ M) :=
              mul_le_mul_of_nonneg_left hx2 (mul_nonneg hW h2M)
            exact mul_le_mul_of_nonneg_right this hz0
        _ = (C * (W * 2 ^ M * 2 ^ M)) * ((1 + ‖x - z‖) ^ M * Real.exp (-c * ‖x - z‖ ^ 2)) * ‖z‖ := by ring
        _ ≤ (C * (W * 2 ^ M * 2 ^ M)) * KB * ‖z‖ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hKB1 _)
              (mul_nonneg hC0 (mul_nonneg (mul_nonneg hW h2M) h2M))) hz0
        _ = _ := by ring
    have t2 : |ρ (x - z) - ρ x| * |vv x| ≤ (2 ^ M * C * KB * V) * ‖z‖ := by
      have h1 : |vv x| ≤ V * jbracket x ^ M := (hcomp x).trans (hDh x)
      calc |ρ (x - z) - ρ x| * |vv x| ≤ ((2 ^ M * C * KB / jbracket x ^ M) * ‖z‖) * (V * jbracket x ^ M) :=
            mul_le_mul hLipρ h1 (abs_nonneg _) (by positivity)
        _ = (2 ^ M * C * KB * V) * ‖z‖ := by field_simp
    have hh := s84_norm_le_sqrt hz
    have hS0 : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg hz0 _
    have hCK : 0 ≤ C * KB := mul_nonneg hC0 hKB0
    calc _ ≤ (C * (W * 2 ^ M * 2 ^ M * KB)) * ‖z‖ + (2 ^ M * C * KB * V) * ‖z‖ := add_le_add t1 t2
      _ ≤ (C * KB * (1 + 2 ^ M * 2 ^ M + 2 ^ M) * (V + W)) * ‖z‖ ^ (1 / 2 : ℝ) := by
          have hcoef : (C * (W * 2 ^ M * 2 ^ M * KB)) + (2 ^ M * C * KB * V) ≤
              C * KB * (1 + 2 ^ M * 2 ^ M + 2 ^ M) * (V + W) := by
            nlinarith [mul_nonneg hCK hV, mul_nonneg hCK hW, mul_nonneg (mul_nonneg hCK hV) (mul_nonneg h2M h2M),
              mul_nonneg (mul_nonneg hCK hV) h2M, mul_nonneg (mul_nonneg hCK hW) (mul_nonneg h2M h2M),
              mul_nonneg (mul_nonneg hCK hW) h2M]
          calc (C * (W * 2 ^ M * 2 ^ M * KB)) * ‖z‖ + (2 ^ M * C * KB * V) * ‖z‖
              = ((C * (W * 2 ^ M * 2 ^ M * KB)) + (2 ^ M * C * KB * V)) * ‖z‖ := by ring
            _ ≤ (C * KB * (1 + 2 ^ M * 2 ^ M + 2 ^ M) * (V + W)) * ‖z‖ :=
                mul_le_mul_of_nonneg_right hcoef hz0
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end HRS.MS.Wad
