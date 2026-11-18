import HRS.MS.R26T8AP22g
import HRS.MD.DOMCalc

/-!
# S8.2 local Newton layer, packet T8A.P22 (part h): `|Δ phi_eps| <= C ‖B‖ |w|^(-s')`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N HRS.MD.DOMProof

namespace HRS.MS.R26T8A

variable {d : ℕ}

/-- The cut-off leading inverse. -/
def r26t8a_p22_phi (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (chi : Euc d → ℝ) (ε : ℝ) (x : Euc d) : ℝ :=
  r26t8a_p22_theta chi ε x * (chi x * s82n_leadingInverse nu B x)

theorem r26t8a_p22_lap_phi_zero {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (nu : ℝ)
    (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (ε : ℝ) {w : Euc d} (hw : 2 < ‖w‖) :
    Laplacian.laplacian (r26t8a_p22_phi nu B chi ε) w = 0 := by
  have hev : r26t8a_p22_phi nu B chi ε =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with y hy
    simp [r26t8a_p22_phi, hchi.2.2.2.2 y (le_of_lt hy)]
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  simp

set_option maxHeartbeats 6400000 in
theorem r26t8a_p22_lap_phi_bound (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), (∀ x y, B x y = B y x) → ∀ ε : ℝ, 0 < ε →
      ∀ w : Euc d, w ≠ 0 → ‖w‖ ≤ 2 →
        |Laplacian.laplacian (r26t8a_p22_phi nu B chi ε) w| ≤ Cd * ‖B‖ * ‖w‖ ^ (-r26t8a_p22_sp d) := by
  obtain ⟨CL, hCL0, hCL⟩ := r26t8a_p22_L_dom hd nu hnu
  obtain ⟨D1, D2, hD10, hD20, hD1, hD2⟩ := r26t8a_p22_chi_bounds hchi
  refine ⟨CL * (1 + 16 * D1 + 8 * D2 + 8 * D1 ^ 2), by positivity, fun B hB ε hε w hw hw2 => ?_⟩
  obtain ⟨hN, hG, hD⟩ := hCL B hB w hw hw2
  have hr : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hnB : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  set r : ℝ := ‖w‖ with hrdef
  set s' : ℝ := r26t8a_p22_sp d with hs'
  set a : ℝ := r ^ (-s') with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hr _
  have e2 : r ^ (2 - s') = r ^ 2 * a := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_add hr]; congr 1
  have e1 : r ^ (1 - s') = r * a := by
    rw [ha, show (1 - s') = 1 + (-s') by ring, Real.rpow_add hr, Real.rpow_one]
  rw [e2] at hN
  rw [e1] at hG
  set u : ℝ := CL * ‖B‖ * a with hu
  have hu0 : 0 ≤ u := by positivity
  have hN' : |s82n_leadingInverse nu B w| ≤ r ^ 2 * u := by rw [hu]; nlinarith [hN]
  have hG' : ‖fderiv ℝ (s82n_leadingInverse nu B) w‖ ≤ r * u := by rw [hu]; nlinarith [hG]
  have hD' : |Laplacian.laplacian (s82n_leadingInverse nu B) w| ≤ u := by rw [hu]; exact hD
  -- smoothness at w
  have hc2 := r26t8a_p22_chi_c2 hchi
  have hL2 : ContDiffAt ℝ 2 (s82n_leadingInverse nu B) w := by
    have h : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (s82n_leadingInverse nu B) w :=
      contDiffAt_infty.1 (r26t8a_p22_L_contDiffAt nu B hw) 2
    exact_mod_cast h
  have hchi2 : ContDiffAt ℝ 2 chi w := hc2.contDiffAt
  have hθ2 : ContDiffAt ℝ 2 (r26t8a_p22_theta chi ε) w := (r26t8a_p22_theta_contDiff hchi ε).contDiffAt
  have hM2 : ContDiffAt ℝ 2 (fun x => chi x * s82n_leadingInverse nu B x) w := hchi2.mul hL2
  have hlapM := domp_lap_mul hchi2 hL2
  have hlapφ : Laplacian.laplacian (r26t8a_p22_phi nu B chi ε) w =
      r26t8a_p22_theta chi ε w * Laplacian.laplacian (fun x => chi x * s82n_leadingInverse nu B x) w +
        2 * inner ℝ (gradient (r26t8a_p22_theta chi ε) w) (gradient (fun x => chi x * s82n_leadingInverse nu B x) w) +
        (chi w * s82n_leadingInverse nu B w) * Laplacian.laplacian (r26t8a_p22_theta chi ε) w :=
    domp_lap_mul hθ2 hM2
  -- elementary bounds
  have hchi01 := hchi.2.2.1 w
  have hθ01 : 0 ≤ r26t8a_p22_theta chi ε w ∧ r26t8a_p22_theta chi ε w ≤ 1 := by
    have := hchi.2.2.1 (ε⁻¹ • w)
    unfold r26t8a_p22_theta; constructor <;> linarith [this.1, this.2]
  have hLabs := hN'
  have hM_abs : |chi w * s82n_leadingInverse nu B w| ≤ r ^ 2 * u := by
    rw [abs_mul, abs_of_nonneg hchi01.1]
    calc chi w * |s82n_leadingInverse nu B w| ≤ 1 * |s82n_leadingInverse nu B w| :=
          mul_le_mul_of_nonneg_right hchi01.2 (abs_nonneg _)
      _ ≤ r ^ 2 * u := by linarith
  -- bound for ΔM
  have hΔM : |Laplacian.laplacian (fun x => chi x * s82n_leadingInverse nu B x) w| ≤
      u + 2 * D1 * (r * u) + D2 * (r ^ 2 * u) := by
    rw [hlapM]
    have i1 : |chi w * Laplacian.laplacian (s82n_leadingInverse nu B) w| ≤ u := by
      rw [abs_mul, abs_of_nonneg hchi01.1]
      calc chi w * |Laplacian.laplacian (s82n_leadingInverse nu B) w| ≤ 1 * u :=
            mul_le_mul hchi01.2 hD' (abs_nonneg _) zero_le_one
        _ = u := one_mul _
    have i2 : |2 * inner ℝ (gradient chi w) (gradient (s82n_leadingInverse nu B) w)| ≤ 2 * D1 * (r * u) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := r26t8a_p22_inner_le chi (s82n_leadingInverse nu B) w
      calc 2 * |inner ℝ (gradient chi w) (gradient (s82n_leadingInverse nu B) w)|
          ≤ 2 * (‖fderiv ℝ chi w‖ * ‖fderiv ℝ (s82n_leadingInverse nu B) w‖) := by gcongr
        _ ≤ 2 * (D1 * (r * u)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (hD1 w) hG' (norm_nonneg _) hD10) (by norm_num)
        _ = _ := by ring
    have i3 : |s82n_leadingInverse nu B w * Laplacian.laplacian chi w| ≤ D2 * (r ^ 2 * u) := by
      rw [abs_mul]
      calc |s82n_leadingInverse nu B w| * |Laplacian.laplacian chi w| ≤ (r ^ 2 * u) * D2 :=
            mul_le_mul hN' (hD2 w) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    calc _ ≤ |chi w * Laplacian.laplacian (s82n_leadingInverse nu B) w| +
          |2 * inner ℝ (gradient chi w) (gradient (s82n_leadingInverse nu B) w)| +
          |s82n_leadingInverse nu B w * Laplacian.laplacian chi w| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  -- bound for the gradient of M
  have hGM : ‖fderiv ℝ (fun x => chi x * s82n_leadingInverse nu B x) w‖ ≤ r * u + D1 * (r ^ 2 * u) := by
    have hdc : DifferentiableAt ℝ chi w := hchi2.differentiableAt (by norm_num)
    have hdL : DifferentiableAt ℝ (s82n_leadingInverse nu B) w := hL2.differentiableAt (by norm_num)
    rw [fderiv_fun_mul hdc hdL]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hchi01.1]
    have j1 : chi w * ‖fderiv ℝ (s82n_leadingInverse nu B) w‖ ≤ r * u :=
      (mul_le_mul hchi01.2 hG' (norm_nonneg _) zero_le_one).trans (by linarith)
    have j2 : |s82n_leadingInverse nu B w| * ‖fderiv ℝ chi w‖ ≤ D1 * (r ^ 2 * u) := by
      calc |s82n_leadingInverse nu B w| * ‖fderiv ℝ chi w‖ ≤ (r ^ 2 * u) * D1 :=
            mul_le_mul hN' (hD1 w) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    linarith
  -- bounds on the cut-off
  have hθg : ‖fderiv ℝ (r26t8a_p22_theta chi ε) w‖ ≤ 2 * D1 / r := by
    by_cases hann : ε < r ∧ r < 2 * ε
    · have h := r26t8a_p22_theta_fderiv hchi hε w
      have hεr : ε⁻¹ ≤ 2 / r := by
        rw [inv_eq_one_div, div_le_div_iff₀ hε hr]; linarith [hann.2]
      calc ‖fderiv ℝ (r26t8a_p22_theta chi ε) w‖ ≤ ε⁻¹ * ‖fderiv ℝ chi (ε⁻¹ • w)‖ := h
        _ ≤ (2 / r) * D1 := mul_le_mul hεr (hD1 _) (norm_nonneg _) (by positivity)
        _ = 2 * D1 / r := by ring
    · have hflat : ‖ε⁻¹ • w‖ ≤ 1 ∨ 2 ≤ ‖ε⁻¹ • w‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le]
        by_cases h1 : r ≤ ε
        · left; rw [inv_mul_le_iff₀ hε]; linarith
        · right
          have h2 : 2 * ε ≤ r := by
            by_contra h3
            exact hann ⟨lt_of_not_ge h1, not_le.1 h3⟩
          rw [le_inv_mul_iff₀ hε]; linarith
      have h := r26t8a_p22_theta_fderiv hchi hε w
      have hz := (r26t8a_p22_chi_flat hchi hflat).1
      rw [hz, norm_zero, mul_zero] at h
      calc ‖fderiv ℝ (r26t8a_p22_theta chi ε) w‖ ≤ 0 := h
        _ ≤ 2 * D1 / r := by positivity
  have hθl : |Laplacian.laplacian (r26t8a_p22_theta chi ε) w| ≤ 4 * D2 / r ^ 2 := by
    rw [r26t8a_p22_theta_lap hchi hε, abs_neg, abs_mul]
    by_cases hann : ε < r ∧ r < 2 * ε
    · have hεr : ε⁻¹ ≤ 2 / r := by
        rw [inv_eq_one_div, div_le_div_iff₀ hε hr]; linarith [hann.2]
      have h1 : |(ε⁻¹) ^ 2| ≤ 4 / r ^ 2 := by
        rw [abs_of_nonneg (by positivity)]
        calc (ε⁻¹) ^ 2 ≤ (2 / r) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hε.le) hεr 2
          _ = 4 / r ^ 2 := by ring
      calc |(ε⁻¹) ^ 2| * |Laplacian.laplacian chi (ε⁻¹ • w)| ≤ (4 / r ^ 2) * D2 :=
            mul_le_mul h1 (hD2 _) (abs_nonneg _) (by positivity)
        _ = 4 * D2 / r ^ 2 := by ring
    · have hflat : ‖ε⁻¹ • w‖ ≤ 1 ∨ 2 ≤ ‖ε⁻¹ • w‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le]
        by_cases h1 : r ≤ ε
        · left; rw [inv_mul_le_iff₀ hε]; linarith
        · right
          have h2 : 2 * ε ≤ r := by
            by_contra h3
            exact hann ⟨lt_of_not_ge h1, not_le.1 h3⟩
          rw [le_inv_mul_iff₀ hε]; linarith
      rw [(r26t8a_p22_chi_flat hchi hflat).2, abs_zero, mul_zero]
      positivity
  -- assemble
  rw [hlapφ]
  have k1 : |r26t8a_p22_theta chi ε w * Laplacian.laplacian (fun x => chi x * s82n_leadingInverse nu B x) w| ≤
      u + 2 * D1 * (r * u) + D2 * (r ^ 2 * u) := by
    rw [abs_mul, abs_of_nonneg hθ01.1]
    exact (mul_le_mul hθ01.2 hΔM (abs_nonneg _) zero_le_one).trans (by linarith)
  have k2 : |2 * inner ℝ (gradient (r26t8a_p22_theta chi ε) w) (gradient (fun x => chi x * s82n_leadingInverse nu B x) w)| ≤
      2 * (2 * D1 / r) * (r * u + D1 * (r ^ 2 * u)) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := r26t8a_p22_inner_le (r26t8a_p22_theta chi ε) (fun x => chi x * s82n_leadingInverse nu B x) w
    have hh : 0 ≤ 2 * D1 / r := by positivity
    calc 2 * |inner ℝ (gradient (r26t8a_p22_theta chi ε) w) (gradient (fun x => chi x * s82n_leadingInverse nu B x) w)|
        ≤ 2 * (‖fderiv ℝ (r26t8a_p22_theta chi ε) w‖ * ‖fderiv ℝ (fun x => chi x * s82n_leadingInverse nu B x) w‖) := by gcongr
      _ ≤ 2 * ((2 * D1 / r) * (r * u + D1 * (r ^ 2 * u))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hθg hGM (norm_nonneg _) hh) (by norm_num)
      _ = _ := by ring
  have k3 : |(chi w * s82n_leadingInverse nu B w) * Laplacian.laplacian (r26t8a_p22_theta chi ε) w| ≤
      (r ^ 2 * u) * (4 * D2 / r ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hM_abs hθl (abs_nonneg _) (by positivity)
  have hsimp2 : 2 * (2 * D1 / r) * (r * u + D1 * (r ^ 2 * u)) = 4 * D1 * u + 4 * D1 ^ 2 * (r * u) := by
    field_simp
    ring
  have hsimp3 : (r ^ 2 * u) * (4 * D2 / r ^ 2) = 4 * D2 * u := by field_simp
  have hr2 : r ≤ 2 := hw2
  have hfin : u + 2 * D1 * (r * u) + D2 * (r ^ 2 * u) + (4 * D1 * u + 4 * D1 ^ 2 * (r * u)) + 4 * D2 * u ≤
      (1 + 16 * D1 + 8 * D2 + 8 * D1 ^ 2) * u := by
    have hr2' : r ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hr.le hr2 2
    have a1 : 2 * D1 * (r * u) ≤ 4 * D1 * u := by
      have : 2 * D1 * (r * u) = (2 * D1 * u) * r := by ring
      rw [this]
      nlinarith [mul_nonneg hD10 hu0]
    have a2 : D2 * (r ^ 2 * u) ≤ 4 * D2 * u := by
      have : D2 * (r ^ 2 * u) = (D2 * u) * r ^ 2 := by ring
      rw [this]
      nlinarith [mul_nonneg hD20 hu0]
    have a3 : 4 * D1 ^ 2 * (r * u) ≤ 8 * D1 ^ 2 * u := by
      have : 4 * D1 ^ 2 * (r * u) = (4 * D1 ^ 2 * u) * r := by ring
      rw [this]
      nlinarith [mul_nonneg (sq_nonneg D1) hu0]
    have b1 := mul_nonneg hD10 hu0
    linarith
  calc _ ≤ |r26t8a_p22_theta chi ε w * Laplacian.laplacian (fun x => chi x * s82n_leadingInverse nu B x) w| +
        |2 * inner ℝ (gradient (r26t8a_p22_theta chi ε) w) (gradient (fun x => chi x * s82n_leadingInverse nu B x) w)| +
        |(chi w * s82n_leadingInverse nu B w) * Laplacian.laplacian (r26t8a_p22_theta chi ε) w| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (1 + 16 * D1 + 8 * D2 + 8 * D1 ^ 2) * u := by
        have := add_le_add (add_le_add k1 k2) k3
        rw [hsimp2, hsimp3] at this
        linarith
    _ = CL * (1 + 16 * D1 + 8 * D2 + 8 * D1 ^ 2) * ‖B‖ * ‖w‖ ^ (-r26t8a_p22_sp d) := by
        rw [hu, ha]; ring

end HRS.MS.R26T8A
