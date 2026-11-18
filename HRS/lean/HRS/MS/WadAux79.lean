import HRS.MS.WadAux78

/-!
# S8.3, packet S8E-2, part 3: linearity of `𝓑` in the density, shifts of `s84_GaussReg`

`s8e_gaussReg_shift`: a density with Gaussian bounds shifted by `‖z‖ ≤ 1` has Gaussian bounds.
`s8e_gr_facts`: the size and Hölder bounds feeding `s84_conv_integrable`.
`s8e_Bop_rho_sub`: `𝓑_{σ₁ - σ₂} h = 𝓑_{σ₁} h - 𝓑_{σ₂} h` for `σ₁, σ₂` with Gaussian bounds and `h ∈ C²_b`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s8e_gaussReg_shift {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {z : Euc d} (hz : ‖z‖ ≤ 1) :
    s84_GaussReg (fun y => ρ (y + z)) := by
  obtain ⟨hd, C, c, hC, hc, hb⟩ := hρ
  refine ⟨(hd.comp (differentiable_id.add_const z)), C * Real.exp c, c / 2, by positivity,
    by positivity, fun x => ?_⟩
  have hf : fderiv ℝ (fun y => ρ (y + z)) x = fderiv ℝ ρ (x + z) := by
    rw [fderiv_comp_add_right]
  have he := s8e_exp_shift hc.le hz x
  refine ⟨(hb (x + z)).1.trans ?_, (hf ▸ (hb (x + z)).2).trans ?_⟩ <;>
  · calc C * Real.exp (-c * ‖x + z‖ ^ 2) ≤ C * (Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left he hC
      _ = _ := by ring

theorem s8e_gr_facts {ρ : Euc d → ℝ} (h : s84_GaussReg ρ) :
    ∃ A H : ℝ, 0 ≤ A ∧ 0 ≤ H ∧ (∀ y, |ρ y| ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x, |ρ (x - z) - ρ x| ≤ H * ‖z‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨hρd, C, c, hC0, hc, hρb⟩ := h
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := (d : ℝ) + 1) (c := c) (by positivity) hc
  have hexp1 : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) ≤ KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro y
    have h1 := hKB y
    have hp : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hp.le]
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hp _
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    nlinarith [h1]
  refine ⟨C * KB, C / 2, by positivity, by positivity, fun y => ?_, fun z hz x => ?_⟩
  · calc |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (hρb y).1
      _ ≤ C * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) := mul_le_mul_of_nonneg_left (hexp1 y) hC0
      _ = _ := by ring
  · have hmv := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le (f := ρ) (C := C)
      (fun y _ => hρd y) (fun y _ => ((hρb y).2).trans (by
        have : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖y‖]
        nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)])) (Set.mem_univ x) (Set.mem_univ (x - z))
    rw [Real.norm_eq_abs, sub_sub_cancel_left, norm_neg] at hmv
    have hh := s84_norm_le_sqrt hz
    calc |ρ (x - z) - ρ x| ≤ C * ‖z‖ := hmv
      _ ≤ C * (‖z‖ ^ (1 / 2 : ℝ) / 2) := mul_le_mul_of_nonneg_left hh hC0
      _ = _ := by ring

theorem s8e_Bop_rho_sub (hd : 2 ≤ d) {σ₁ σ₂ : Euc d → ℝ} (g₁ : s84_GaussReg σ₁) (g₂ : s84_GaussReg σ₂)
    {h : Euc d → ℝ} {B : ℝ} (hh : s84_C2b h B) (x : Euc d) :
    s84_Bop (fun y => σ₁ y - σ₂ y) h x = s84_Bop σ₁ h x - s84_Bop σ₂ h x := by
  obtain ⟨Lu1, hLu10, hLu1⟩ := s84_u_facts hd g₁
  obtain ⟨Lu2, hLu20, hLu2⟩ := s84_u_facts hd g₂
  obtain ⟨A1, H1, hA10, hH10, hA1, hH1⟩ := s8e_gr_facts g₁
  obtain ⟨A2, H2, hA20, hH20, hA2, hH2⟩ := s8e_gr_facts g₂
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hs1 : (d : ℝ) / 2 + 1 / 2 < (d : ℝ) := by linarith
  have dd : Differentiable ℝ h := hh.1.differentiable (by norm_num)
  have c1 := s84_conv_integrable hd hs0 hs1 hA10 hH10 g₁.1.continuous.measurable hA1 hH1 x
  have c2 := s84_conv_integrable hd hs0 hs1 hA20 hH20 g₂.1.continuous.measurable hA2 hH2 x
  have e1 : convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) (fun y => σ₁ y - σ₂ y) x =
      convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) σ₁ x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) σ₂ x := s84_conv_sub x c1 c2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hh.2 0).1
  unfold s84_Bop
  rw [e1]
  have e2 : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
      (fun y => (σ₁ y - σ₂ y) * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j =
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => σ₁ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j -
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => σ₂ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j := by
    intro j
    obtain ⟨m1, a1, hh1⟩ := hLu1 hh j
    obtain ⟨m2, a2, hh2⟩ := hLu2 hh j
    have hi1 := s84_conv_integrable hd hs0 hs1 (by positivity) (by positivity) m1 a1 hh1 x
    have hi2 := s84_conv_integrable hd hs0 hs1 (by positivity) (by positivity) m2 a2 hh2 x
    have hfun : (fun y => (σ₁ y - σ₂ y) * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h y)) j) =
        (fun y => σ₁ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j -
          σ₂ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) := by
      funext y; ring
    rw [hfun, s84_conv_sub (u₁ := fun y => σ₁ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h y)) j) (u₂ := fun y => σ₂ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h y)) j) x hi1 hi2, PiLp.sub_apply]
  rw [Finset.sum_congr rfl fun j _ => e2 j, Finset.sum_sub_distrib]
  have e3 : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) σ₁ x -
        convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) σ₂ x) =
      Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) σ₁ x) -
        Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) σ₂ x) := by
    simp only [s84_matVec_neg]; abel
  rw [e3, inner_sub_left]
  ring

end HRS.MS.Wad
