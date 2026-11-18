import HRS.MS.WadAux57

/-!
# S8.3, packet S8D-2, part 4: decay of the first order remainder `𝓑` at infinity

`s8d_force_bound`: the force `D = ∇g*ρ` is bounded.
`s8d_B_decay`: for every `ε > 0` there is `C_ε` such that `|𝓑 h(y)| ≤ (V+H)(ε⟨y⟩^M + C_ε)` for every `h` with the
weighted `C^{1,1/2}` bounds (`‖Dh‖ ≤ V⟨y⟩^M`, Hölder constant `H`), i.e. `𝓑` has a coefficient decaying at infinity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s8d_force_bound (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) :
    ∃ Dρ : ℝ, 0 ≤ Dρ ∧ ∀ x : Euc d, ‖convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x‖ ≤ Dρ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hρd, C, c, hC0, hc, hρb⟩ := hρ
  set s : ℝ := (d : ℝ) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s + 1 / 2 < (d : ℝ) := by rw [hs]; linarith
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := (d : ℝ) + 1) (c := c) (by positivity) hc
  have hρA : ∀ y : Euc d, |ρ y| ≤ (C * KB) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
    refine ((hρb y).1).trans ?_
    have h1 := hKB y
    have hp : 0 < 1 + ‖y‖ := by positivity
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hp _
    have h2 : Real.exp (-c * ‖y‖ ^ 2) ≤ KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
      rw [Real.rpow_neg hp.le, ← div_eq_mul_inv, le_div_iff₀ hq]
      linarith [mul_comm (Real.exp (-c * ‖y‖ ^ 2)) ((1 + ‖y‖) ^ ((d : ℝ) + 1))]
    calc C * Real.exp (-c * ‖y‖ ^ 2) ≤ C * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h2 hC0
      _ = _ := by ring
  have hρLip : ∀ x z : Euc d, |ρ (x - z) - ρ x| ≤ C * ‖z‖ := by
    intro x z
    have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le (f := ρ) (C := C)
      (fun y _ => hρd y) (fun y _ => ((hρb y).2).trans (by
        have : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖y‖]
        nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)])) (Set.mem_univ x) (Set.mem_univ (x - z))
    rw [Real.norm_eq_abs] at this
    rw [sub_sub_cancel_left x z, norm_neg] at this
    exact this
  refine ⟨s84_Cconv d s * (C * KB + C / 2), mul_nonneg (s84_Cconv_nonneg d hs0.le) (by positivity), fun x => ?_⟩
  refine s84_conv_bound hd hs0 hs1 (A := C * KB) (H := C / 2) (by positivity) (by positivity)
    hρA (fun z hz x' => ?_) x
  refine (hρLip x' z).trans ?_
  have := s84_norm_le_sqrt hz
  nlinarith

theorem s8d_B_decay (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {M : ℝ} (hM : 0 ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧ ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ y, |s84_Bop ρ h y| ≤ (V + H) * (ε * jbracket y ^ M + Cε) := by
  obtain ⟨CJ, hCJ0, hCJ⟩ := s8d_J_bound hd hρ hM
  obtain ⟨Dρ, hDρ0, hDρ⟩ := s8d_force_bound hd hρ
  obtain ⟨R, hR⟩ := s8d_force_decay hd hρ hε
  refine ⟨CJ + Dρ * (1 + |R|) ^ M, by positivity, ?_⟩
  intro h V H hV hH hDh hHh y
  have hJ := hCJ hV hH hDh hHh y
  have hjy0 : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
  have hRM : 0 ≤ Dρ * (1 + |R|) ^ M := by positivity
  unfold s84_Bop
  refine (abs_sub _ _).trans ?_
  have t1 : |inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ y)) (gradient h y)| ≤
      ‖convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ y‖ * (V * jbracket y ^ M) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [s84_matVec_neg, norm_neg, s84_grad_norm]
    exact mul_le_mul_of_nonneg_left (hDh y) (norm_nonneg _)
  have hVJ : 0 ≤ V * jbracket y ^ M := mul_nonneg hV hjy0
  have hmain : ‖convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ y‖ * (V * jbracket y ^ M) ≤
      V * (ε * jbracket y ^ M + Dρ * (1 + |R|) ^ M) := by
    by_cases hy : R ≤ ‖y‖
    · have := mul_le_mul_of_nonneg_right (hR y hy) hVJ
      nlinarith [mul_nonneg hV hRM]
    · push Not at hy
      have h1 := hDρ y
      have h2 : jbracket y ^ M ≤ (1 + |R|) ^ M := by
        refine Real.rpow_le_rpow (s83_jb_pos y).le ((s83_jb_le_one_add y).trans ?_) hM
        have := le_abs_self R
        linarith
      have := mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hV) hVJ hDρ0
      nlinarith [mul_nonneg hV (mul_nonneg hε.le hjy0)]
  have hHnn : 0 ≤ H * (ε * jbracket y ^ M + Dρ * (1 + |R|) ^ M) :=
    mul_nonneg hH (by positivity)
  nlinarith [t1, hmain, hJ]

end HRS.MS.Wad
