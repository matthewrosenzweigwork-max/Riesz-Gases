import HRS.MS.WadAux56

/-!
# S8.3, packet S8D-2, part 3: the nonlocal term of `𝓑` is bounded without weight

`s8d_J_bound`: the nonlocal term `Σ_j (∇g * (ρ (M^T ∇h)_j))_j` of `s84_Bop` is bounded by `C_J (V+H)`, without the
factor `⟨x⟩^M` (the density `ρ` is Gaussian, so only the values of `∇h` near the origin matter).  Together with the
decay of the force (`s8d_force_decay`) this gives `|𝓑 h(x)| ≤ ε⟨x⟩^M (V+H) + C_ε (V+H)` (`s8d_B_decay`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s8d_J_bound (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |∑ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j| ≤
        CJ * (V + H) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hρd, C, c, hC0, hc, hρb⟩ := hρ
  set s : ℝ := (d : ℝ) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs1 : s + 1 / 2 < (d : ℝ) := by rw [hs]; linarith
  set Cc : ℝ := s84_Cconv d s with hCc
  have hCc0 : 0 ≤ Cc := s84_Cconv_nonneg d hs0.le
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := M + ((d : ℝ) + 1)) (c := c) (by positivity) hc
  -- weights
  have W1 : ∀ y : Euc d, (1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2) ≤
      KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro y
    have h1 := hKB y
    have hp : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_add hp] at h1
    rw [Real.rpow_neg hp.le]
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hp _
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    nlinarith [h1]
  have W0 : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) ≤ KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
    intro y
    refine le_trans ?_ (W1 y)
    have : 1 ≤ (1 + ‖y‖) ^ M := Real.one_le_rpow (by linarith [norm_nonneg y]) hM
    nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)]
  have W2 : ∀ y : Euc d, (1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2) ≤ KB := by
    intro y
    refine (W1 y).trans ?_
    have : (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)
    nlinarith
  have hjb1 : ∀ y : Euc d, jbracket y ^ M ≤ (1 + ‖y‖) ^ M := fun y =>
    Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_one_add y) hM
  have hjb0 : ∀ y : Euc d, 1 ≤ jbracket y ^ M := fun y => Real.one_le_rpow (s83_one_le_jb y) hM
  -- the density `ρ`: size and Lipschitz bounds
  have hρA : ∀ y, |ρ y| ≤ (C * KB) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y =>
    ((hρb y).1).trans (by
      calc C * Real.exp (-c * ‖y‖ ^ 2) ≤ C * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (W0 y) hC0
        _ = _ := by ring)
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
  have hz12 : ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ‖z‖ ≤ ‖z‖ ^ (1 / 2 : ℝ) / 2 := by
    intro z hz
    have h0 := norm_nonneg z
    have hsq : ‖z‖ ^ (1 / 2 : ℝ) = Real.sqrt ‖z‖ := (Real.sqrt_eq_rpow ‖z‖).symm
    rw [hsq]
    have h1 := Real.sq_sqrt h0
    have h2 : Real.sqrt ‖z‖ ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hz
    nlinarith [Real.sqrt_nonneg ‖z‖]
  -- constants
  set L : ℝ := C * 3 ^ M * KB with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨2 * d * Cc * L, by positivity, ?_⟩
  intro h V H hV hH hDh hHh x
  have hJ : ∀ j : Fin d, ‖convGradConvW (rieszKernelGrad d s)
      (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x‖ ≤
        Cc * (L * V + L * (H + V / 2)) := by
    intro j
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
    have hA : ∀ y, |ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
        (L * V) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
      intro y
      rw [abs_mul]
      have h1 : |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (hρb y).1
      have h2 : |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j| ≤
          V * (1 + ‖y‖) ^ M := (hcomp y).trans ((hDh y).trans
        (mul_le_mul_of_nonneg_left (hjb1 y) hV))
      have h3 := W1 y
      have h33 : (1 : ℝ) ≤ 3 ^ M := Real.one_le_rpow (by norm_num) hM
      calc |ρ y| * |(Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j|
          ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (V * (1 + ‖y‖) ^ M) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = C * V * ((1 + ‖y‖) ^ M * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ ≤ C * V * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (C * KB * V) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by ring
        _ ≤ (L * V) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
            rw [hL]
            have : C * KB * V ≤ C * 3 ^ M * KB * V := by
              have := mul_nonneg hC0 hKB0
              nlinarith [mul_nonneg this hV]
            exact this
    have hHol : ∀ z : Euc d, ‖z‖ ≤ 1 / 4 → ∀ x' : Euc d,
        |ρ (x' - z) * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h (x' - z))) j -
          ρ x' * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h x')) j| ≤
          (L * (H + V / 2)) * ‖z‖ ^ (1 / 2 : ℝ) := by
      intro z hz x'
      have hjx := s83_jb_pos x'
      have hjx3 : ∀ w : Euc d, ‖x' - w‖ < 1 → jbracket x' ^ M ≤ 3 ^ M * (1 + ‖w‖) ^ M := by
        intro w hw
        have h1 : jbracket x' ≤ 3 * jbracket w := by
          have := s83_jb_le_three (x := x') (x₀ := w) hw
          exact this
        calc jbracket x' ^ M ≤ (3 * jbracket w) ^ M := Real.rpow_le_rpow hjx.le h1 hM
          _ = 3 ^ M * jbracket w ^ M := Real.mul_rpow (by norm_num) (s83_jb_pos _).le
          _ ≤ 3 ^ M * (1 + ‖w‖) ^ M := mul_le_mul_of_nonneg_left (hjb1 w) (by positivity)
      set vv : Euc d → ℝ := fun y => (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j
        with hvv
      have e : ρ (x' - z) * vv (x' - z) - ρ x' * vv x' =
          ρ (x' - z) * (vv (x' - z) - vv x') + (ρ (x' - z) - ρ x') * vv x' := by ring
      show |ρ (x' - z) * vv (x' - z) - ρ x' * vv x'| ≤ _
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have hzx : ‖x' - (x' - z)‖ = ‖z‖ := by rw [sub_sub_cancel]
      have hz1 : ‖z‖ < 1 := by linarith
      -- first term
      have t1 : |ρ (x' - z)| * |vv (x' - z) - vv x'| ≤ L * H * ‖z‖ ^ (1 / 2 : ℝ) := by
        have h1 : |vv (x' - z) - vv x'| ≤ H * ‖z‖ ^ (1 / 2 : ℝ) * jbracket x' ^ M := by
          refine (hcompd x' (x' - z)).trans ?_
          have := hHh x' (x' - z) (by rw [sub_sub_cancel_left x' z, norm_neg]; exact hz)
          rwa [sub_sub_cancel_left x' z, norm_neg] at this
        have h2 : |ρ (x' - z)| * jbracket x' ^ M ≤ L := by
          have := hjx3 (x' - z) (by rw [hzx]; exact hz1)
          calc |ρ (x' - z)| * jbracket x' ^ M ≤ (C * Real.exp (-c * ‖x' - z‖ ^ 2)) * (3 ^ M * (1 + ‖x' - z‖) ^ M) :=
                mul_le_mul (hρb _).1 this (by positivity) (by positivity)
            _ = C * 3 ^ M * ((1 + ‖x' - z‖) ^ M * Real.exp (-c * ‖x' - z‖ ^ 2)) := by ring
            _ ≤ C * 3 ^ M * KB := mul_le_mul_of_nonneg_left (W2 _) (by positivity)
            _ = L := by rw [hL]
        calc |ρ (x' - z)| * |vv (x' - z) - vv x'| ≤ |ρ (x' - z)| * (H * ‖z‖ ^ (1 / 2 : ℝ) * jbracket x' ^ M) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = (|ρ (x' - z)| * jbracket x' ^ M) * (H * ‖z‖ ^ (1 / 2 : ℝ)) := by ring
          _ ≤ L * (H * ‖z‖ ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = L * H * ‖z‖ ^ (1 / 2 : ℝ) := by ring
      -- second term
      have t2 : |ρ (x' - z) - ρ x'| * |vv x'| ≤ L * V / 2 * ‖z‖ ^ (1 / 2 : ℝ) := by
        have hjM : 0 < jbracket x' ^ M := Real.rpow_pos_of_pos hjx _
        have hbd : ∀ w ∈ closedBall x' (1 / 4), ‖fderiv ℝ ρ w‖ ≤ L / jbracket x' ^ M := by
          intro w hw
          rw [mem_closedBall_iff_norm'] at hw
          have hlt : ‖x' - w‖ < 1 := by linarith
          have h1 := hjx3 w hlt
          rw [le_div_iff₀ hjM]
          calc ‖fderiv ℝ ρ w‖ * jbracket x' ^ M ≤ (C * Real.exp (-c * ‖w‖ ^ 2)) * (3 ^ M * (1 + ‖w‖) ^ M) :=
                mul_le_mul (hρb w).2 h1 (by positivity) (by positivity)
            _ = C * 3 ^ M * ((1 + ‖w‖) ^ M * Real.exp (-c * ‖w‖ ^ 2)) := by ring
            _ ≤ C * 3 ^ M * KB := mul_le_mul_of_nonneg_left (W2 _) (by positivity)
            _ = L := by rw [hL]
        have hmv := (convex_closedBall x' (1 / 4)).norm_image_sub_le_of_norm_fderiv_le
          (f := ρ) (C := L / jbracket x' ^ M) (fun w _ => hρd w) hbd
          (mem_closedBall_self (by norm_num)) (show x' - z ∈ closedBall x' (1 / 4) by
            rw [mem_closedBall_iff_norm]; rw [sub_sub_cancel_left x' z, norm_neg]; exact hz)
        rw [Real.norm_eq_abs, sub_sub_cancel_left x' z, norm_neg] at hmv
        have hv : |vv x'| ≤ V * jbracket x' ^ M := (hcomp x').trans (hDh x')
        calc |ρ (x' - z) - ρ x'| * |vv x'| ≤ (L / jbracket x' ^ M * ‖z‖) * (V * jbracket x' ^ M) :=
              mul_le_mul hmv hv (abs_nonneg _) (by positivity)
          _ = L * V * ‖z‖ := by field_simp
          _ ≤ L * V * (‖z‖ ^ (1 / 2 : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left (hz12 z hz) (by positivity)
          _ = L * V / 2 * ‖z‖ ^ (1 / 2 : ℝ) := by ring
      calc _ ≤ L * H * ‖z‖ ^ (1 / 2 : ℝ) + L * V / 2 * ‖z‖ ^ (1 / 2 : ℝ) := add_le_add t1 t2
        _ = (L * (H + V / 2)) * ‖z‖ ^ (1 / 2 : ℝ) := by ring
    exact s84_conv_bound hd hs0 hs1 (by positivity) (by positivity) hA hHol x
  have t2 : |∑ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
      (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j| ≤
      d * (Cc * (L * V + L * (H + V / 2))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin d, |(convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x) j|
        ≤ ∑ _j : Fin d, Cc * (L * V + L * (H + V / 2)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Real.norm_eq_abs]
          exact (PiLp.norm_apply_le _ j).trans (hJ j)
      _ = d * (Cc * (L * V + L * (H + V / 2))) := by simp
  refine t2.trans ?_
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have e1 : 0 ≤ d * Cc * L := by positivity
  nlinarith [mul_nonneg e1 hV, mul_nonneg e1 hH]

end HRS.MS.Wad
