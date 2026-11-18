import HRS.MS.WadAux159

/-!
# S8.3, packet S8G-11: the projected generator is a bounded functional on weighted `C^2`

`s8g_gen_bound` (the pointwise functional bound (J12) of the Pro plan, one-body version): for `g ∈ C^2` with `‖Dg(y)‖ ≤ V⟨y⟩^M` and
`‖D²g(y)‖ ≤ W⟨y⟩^M`, `|𝒜 g(x)| ≤ C_𝒜 (V+W) ⟨x⟩^M (1 + ‖x‖)` where `𝒜 = projGeneratorW (critCoeff …) (withDensityReal ρβ) 0`.
(`generatorW = L₀ + 𝓑` with `L₀ g = νΔg - a⟨x,∇g⟩`, `s84_B_bound` for the nonlocal part, Gaussian moments for the mean.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8g_lap_pt (g : Euc d → ℝ) (y : Euc d) : |s83_lap g y| ≤ d * ‖fderiv ℝ (fderiv ℝ g) y‖ := by
  unfold s83_lap
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin d, |fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤
      ‖fderiv ℝ (fderiv ℝ g) y‖ := by
    intro i
    rw [← Real.norm_eq_abs]
    have h1 := (fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single i 1)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    have h2 := (fderiv ℝ (fderiv ℝ g) y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at h1 h2
    exact h1.trans h2
  calc ∑ i : Fin d, |fderiv ℝ (fderiv ℝ g) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin d, ‖fderiv ℝ (fderiv ℝ g) y‖ := Finset.sum_le_sum fun i _ => this i
    _ = d * ‖fderiv ℝ (fderiv ℝ g) y‖ := by simp

theorem s8g_gen_bound (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 ≤ M) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {g : Euc d → ℝ} {V W : ℝ}, 0 ≤ V → 0 ≤ W → ContDiff ℝ 2 g →
      (∀ y, ‖fderiv ℝ g y‖ ≤ V * jbracket y ^ M) → (∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ W * jbracket y ^ M) →
      ∀ x, |projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 g x| ≤
        Cg * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hgr : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨CB, hCB0, hCB⟩ := s84_B_bound hd hgr hM
  have hi1 : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hgr hM
  have hi2 : Integrable (fun y : Euc d => jbracket y ^ (M + 1)) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hgr (by linarith)
  set m1 : ℝ := ∫ y, jbracket y ^ M ∂(HRS.Whole.withDensityReal ρβ) with hm1
  set m2 : ℝ := ∫ y, jbracket y ^ (M + 1) ∂(HRS.Whole.withDensityReal ρβ) with hm2
  have hm10 : 0 ≤ m1 := integral_nonneg fun y => Real.rpow_nonneg (s83_jb_pos y).le _
  have hm20 : 0 ≤ m2 := integral_nonneg fun y => Real.rpow_nonneg (s83_jb_pos y).le _
  set C1 : ℝ := β⁻¹ * d + |a| + CB * (1 + 2 ^ M) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  refine ⟨C1 * (1 + (m1 + m2)), by positivity, fun {g} {V W} hV hW hg hDg hD2g x => ?_⟩
  have h2M : 0 ≤ (2 : ℝ) ^ M := Real.rpow_nonneg (by norm_num) M
  -- pointwise bound of the generator
  have hpt : ∀ x : Euc d, |generatorW (critCoeff d a β ρβ) 0 g x| ≤
      C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
    intro x
    rw [s84_generator_decomp]
    have hjx := Real.rpow_nonneg (s83_jb_pos x).le M
    have hn1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hHolder : ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ g x' - fderiv ℝ g x‖ ≤ (W * 2 ^ M) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
      intro x x' hxx
      have hdiff : Differentiable ℝ (fderiv ℝ g) :=
        (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
      have hjx0 := Real.rpow_nonneg (s83_jb_pos x).le M
      have hb : ∀ z ∈ Metric.closedBall x ‖x' - x‖, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ W * 2 ^ M * jbracket x ^ M := by
        intro z hz
        have hz' : ‖z - x‖ ≤ ‖x' - x‖ := mem_closedBall_iff_norm.1 hz
        have h1 : jbracket z ≤ 2 * jbracket x := by
          have := s83_jb_lipschitz z x
          have h2 := abs_le.1 this
          have h3 := s83_one_le_jb x
          linarith [h2.2]
        have h4 : jbracket z ^ M ≤ (2 * jbracket x) ^ M :=
          Real.rpow_le_rpow (s83_jb_pos z).le h1 hM
        rw [Real.mul_rpow (by norm_num) (s83_jb_pos x).le] at h4
        calc ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ W * jbracket z ^ M := hD2g z
          _ ≤ W * (2 ^ M * jbracket x ^ M) := mul_le_mul_of_nonneg_left h4 hW
          _ = _ := by ring
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ g)
        (C := W * 2 ^ M * jbracket x ^ M) (s := Metric.closedBall x ‖x' - x‖) (fun y _ => hdiff y) hb
        (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg _)) (x := x) (y := x')
        (by rw [mem_closedBall_iff_norm, norm_sub_rev])
      have hr : ‖x' - x‖ ≤ ‖x' - x‖ ^ (1 / 2 : ℝ) := by
        by_cases h0 : ‖x' - x‖ = 0
        · rw [h0]; simp
        · have hpos : 0 < ‖x' - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          have hs : ‖x' - x‖ ^ (1 / 2 : ℝ) * ‖x' - x‖ ^ (1 / 2 : ℝ) = ‖x' - x‖ := by
            rw [← Real.rpow_add hpos]; norm_num
          have hs1 : ‖x' - x‖ ^ (1 / 2 : ℝ) ≤ 1 := by
            have : ‖x' - x‖ ^ (1 / 2 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (norm_nonneg _) (by linarith) (by norm_num)
            simpa using this
          nlinarith [Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)]
      calc ‖fderiv ℝ g x' - fderiv ℝ g x‖ ≤ W * 2 ^ M * jbracket x ^ M * ‖x' - x‖ := hmv
        _ ≤ W * 2 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hr (mul_nonneg (mul_nonneg hW h2M) hjx0)
        _ = _ := by ring
    have hB := hCB hV (mul_nonneg hW h2M) hDg hHolder x
    unfold s83_L0
    have e1 : |β⁻¹ * s83_lap g x| ≤ β⁻¹ * (d * (W * jbracket x ^ M)) := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
      exact mul_le_mul_of_nonneg_left ((s8g_lap_pt g x).trans
        (mul_le_mul_of_nonneg_left (hD2g x) (Nat.cast_nonneg d))) (inv_pos.2 hβ).le
    have e2 : |a * fderiv ℝ g x x| ≤ |a| * (V * jbracket x ^ M * ‖x‖) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ g x).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hDg x) (norm_nonneg _))
    have hxn := norm_nonneg x
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc |β⁻¹ * s83_lap g x - a * fderiv ℝ g x x + s84_Bop ρβ g x|
        ≤ |β⁻¹ * s83_lap g x - a * fderiv ℝ g x x| + |s84_Bop ρβ g x| := abs_add_le _ _
      _ ≤ |β⁻¹ * s83_lap g x| + |a * fderiv ℝ g x x| + |s84_Bop ρβ g x| := by
          have := abs_sub (β⁻¹ * s83_lap g x) (a * fderiv ℝ g x x)
          linarith
      _ ≤ β⁻¹ * (d * (W * jbracket x ^ M)) + |a| * (V * jbracket x ^ M * ‖x‖) +
            CB * (V + W * 2 ^ M) * jbracket x ^ M := by linarith
      _ ≤ C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
          have hVW : W * 2 ^ M ≤ W * 2 ^ M := le_rfl
          have t1 : β⁻¹ * (d * (W * jbracket x ^ M)) ≤ β⁻¹ * d * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
            have : W * jbracket x ^ M ≤ (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
              nlinarith [mul_nonneg hV hjx, mul_nonneg hW hjx, mul_nonneg (mul_nonneg hW hjx) hxn,
                mul_nonneg (mul_nonneg hV hjx) hxn]
            have h5 : 0 ≤ β⁻¹ * d := mul_nonneg (inv_pos.2 hβ).le hd0
            calc β⁻¹ * (d * (W * jbracket x ^ M)) = β⁻¹ * d * (W * jbracket x ^ M) := by ring
              _ ≤ β⁻¹ * d * ((V + W) * (jbracket x ^ M * (1 + ‖x‖))) := mul_le_mul_of_nonneg_left this h5
              _ = _ := by ring
          have t2 : |a| * (V * jbracket x ^ M * ‖x‖) ≤ |a| * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
            have : V * jbracket x ^ M * ‖x‖ ≤ (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
              nlinarith [mul_nonneg hV hjx, mul_nonneg hW hjx, mul_nonneg (mul_nonneg hW hjx) hxn,
                mul_nonneg (mul_nonneg hV hjx) hxn]
            calc |a| * (V * jbracket x ^ M * ‖x‖) ≤ |a| * ((V + W) * (jbracket x ^ M * (1 + ‖x‖))) :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = _ := by ring
          have t3 : CB * (V + W * 2 ^ M) * jbracket x ^ M ≤ CB * (1 + 2 ^ M) * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
            have h6 : V + W * 2 ^ M ≤ (1 + 2 ^ M) * (V + W) := by
              nlinarith [mul_nonneg hV h2M, mul_nonneg hW h2M]
            have h7 : jbracket x ^ M ≤ jbracket x ^ M * (1 + ‖x‖) := by nlinarith
            calc CB * (V + W * 2 ^ M) * jbracket x ^ M ≤ CB * ((1 + 2 ^ M) * (V + W)) * (jbracket x ^ M * (1 + ‖x‖)) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left h6 hCB0) h7 hjx
                    (mul_nonneg hCB0 (mul_nonneg (by positivity) (add_nonneg hV hW)))
              _ = _ := by ring
          calc _ ≤ β⁻¹ * d * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) + |a| * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) +
                CB * (1 + 2 ^ M) * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by linarith
            _ = _ := by rw [hC1]; ring
  -- the mean
  have hpt2 : ∀ y : Euc d, jbracket y ^ M * (1 + ‖y‖) ≤ jbracket y ^ M + jbracket y ^ (M + 1) := by
    intro y
    have hjy := Real.rpow_nonneg (s83_jb_pos y).le M
    have e : jbracket y ^ (M + 1) = jbracket y ^ M * jbracket y := by
      rw [Real.rpow_add (s83_jb_pos y), Real.rpow_one]
    rw [e]
    have := s83_norm_le_jb y
    nlinarith
  have hVW : 0 ≤ C1 * (V + W) := by positivity
  have hmean : |∫ y, generatorW (critCoeff d a β ρβ) 0 g y ∂(HRS.Whole.withDensityReal ρβ)| ≤
      C1 * (V + W) * (m1 + m2) := by
    rw [← Real.norm_eq_abs]
    have hbd : Integrable (fun y : Euc d => C1 * (V + W) * (jbracket y ^ M + jbracket y ^ (M + 1)))
        (HRS.Whole.withDensityReal ρβ) := (hi1.add hi2).const_mul _
    have := norm_integral_le_of_norm_le hbd (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact (hpt y).trans (mul_le_mul_of_nonneg_left (hpt2 y) hVW))
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add hi1 hi2]
  have hjx := Real.rpow_nonneg (s83_jb_pos x).le M
  have hone : 1 ≤ jbracket x ^ M * (1 + ‖x‖) := by
    have h1 : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
    have h2 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    nlinarith
  unfold projGeneratorW
  refine (abs_sub _ _).trans ?_
  calc |generatorW (critCoeff d a β ρβ) 0 g x| +
        |∫ y, generatorW (critCoeff d a β ρβ) 0 g y ∂(HRS.Whole.withDensityReal ρβ)|
      ≤ C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) + C1 * (V + W) * (m1 + m2) := add_le_add (hpt x) hmean
    _ ≤ C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) + C1 * (V + W) * ((m1 + m2) * (jbracket x ^ M * (1 + ‖x‖))) := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hVW)
        have hm12 : 0 ≤ m1 + m2 := by linarith
        nlinarith
    _ = _ := by ring

end HRS.MS.Wad
