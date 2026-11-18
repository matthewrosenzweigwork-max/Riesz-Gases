import HRS.MC.D1F

/-!
# Packet D1F0: Fourier-side normalisation of the Fefferman-de la Llave constant, `s = 0`
(namespace `HRS.MC.D1F0`, helpers prefixed `d1z_`)

Parallel to `HRS.MC.D1F.d1f_pos` (`0 < s < d`).  For `s = 0` the constant `b` with `b φ(0) = 1`
satisfies `b ∫_0^∞ t^{d} ψ̂(te)² dt/t = rieszConst d 0 (2π)^{-d}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.MC.D1F0

open HRS HRS.MC.D1E HRS.MC.D1F

variable {d : ℕ}

/-- Real exponent `d - 1` versus natural exponent `d - 1`, for `1 ≤ d`. -/
theorem d1z_rpow_nat (hd : 1 ≤ d) {y : ℝ} : y ^ ((d : ℝ) - 1) = y ^ (d - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one]

/-- Radiality of `ψ̂` written along the ray through the unit vector `e`. -/
theorem d1z_hat_ray {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {e : Euc d} (he : ‖e‖ = 1) (ξ : Euc d) :
    fdlPsiHat ψ ξ = fdlPsiHat ψ (‖ξ‖ • e) := by
  refine d1f_hat_radial hψ ?_
  rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg ξ)]

/-- `ψ̂²` is integrable on `ℝ^d` (decay of `ψ̂` and polar coordinates). -/
theorem d1z_hat_sq_int (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {e : Euc d}
    (he : ‖e‖ = 1) : Integrable (fun ξ : Euc d => fdlPsiHat ψ ξ ^ 2) := by
  set H : ℝ → ℝ := fun r => fdlPsiHat ψ (r • e) with hH
  have hHc : Continuous H :=
    (d1f_hat_cont hψ).comp (continuous_id.smul continuous_const)
  obtain ⟨C0, hC0, h0⟩ := d1f_hat_decay hψ 0
  obtain ⟨C1, hC1, h1⟩ := d1f_hat_decay hψ d
  have hQc : Continuous fun r => H r ^ 2 := hHc.pow 2
  have hint : IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - 1) * H r ^ 2) (Ioi 0) := by
    refine d1f_oneD_int hQc (by linarith [(by exact_mod_cast hd : (1 : ℝ) ≤ d)]) (M := C0 ^ 2)
      (fun r => ?_) (n := 2 * d) (C := C1 ^ 2) (fun r hr => ?_) (by
        push_cast; linarith [(by exact_mod_cast hd : (1 : ℝ) ≤ d)])
    · have := h0 (r • e)
      simp only [pow_zero, one_mul] at this
      show |H r ^ 2| ≤ _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    · have := h1 (r • e)
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)] at this
      show |H r ^ 2| * r ^ (2 * d) ≤ _
      calc |H r ^ 2| * r ^ (2 * d) = (r ^ d * |fdlPsiHat ψ (r • e)|) ^ 2 := by
            rw [abs_pow, pow_mul']
            show |fdlPsiHat ψ (r • e)| ^ 2 * (r ^ d) ^ 2 = _
            ring
        _ ≤ C1 ^ 2 := pow_le_pow_left₀ (by positivity) this 2
  have hnat : IntegrableOn (fun y : ℝ => y ^ (d - 1) * (fun r : ℝ => H r ^ 2) y) (Ioi 0) := by
    refine hint.congr_fun (fun y hy => ?_) measurableSet_Ioi
    show y ^ ((d : ℝ) - 1) * H y ^ 2 = y ^ (d - 1) * H y ^ 2
    rw [d1z_rpow_nat hd]
  have hsq2 : Integrable (fun ξ : Euc d => (fun r : ℝ => H r ^ 2) ‖ξ‖) :=
    (d1f_polar_integrable hd (fun r : ℝ => H r ^ 2)).2 hnat
  have hA' : (fun ξ : Euc d => (fun r : ℝ => H r ^ 2) ‖ξ‖) = fun ξ => fdlPsiHat ψ ξ ^ 2 := by
    funext ξ
    show fdlPsiHat ψ (‖ξ‖ • e) ^ 2 = fdlPsiHat ψ ξ ^ 2
    rw [d1z_hat_ray hψ he ξ]
  rw [hA'] at hsq2
  exact hsq2

/-- Fourier inversion at the origin: `φ(0) = ∫ ψ̂²`. -/
theorem d1z_phi_zero_eq_int {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    (hsq : Integrable (fun ξ : Euc d => fdlPsiHat ψ ξ ^ 2)) :
    fdlPhi ψ 0 = ∫ ξ : Euc d, fdlPsiHat ψ ξ ^ 2 := by
  have hC : Continuous (fun x : Euc d => (fdlPhi ψ x : ℂ)) :=
    Complex.continuous_ofReal.comp (d1e_phi_cont hψ)
  have hI : Integrable (fun x : Euc d => (fdlPhi ψ x : ℂ)) := (d1f_phi_int hψ).ofReal
  have hFeq : 𝓕 (fun x : Euc d => (fdlPhi ψ x : ℂ)) =
      fun ξ => ((fdlPsiHat ψ ξ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    exact d1f_fourier_phi hψ ξ
  have hFI : Integrable (𝓕 (fun x : Euc d => (fdlPhi ψ x : ℂ))) := by
    rw [hFeq]
    exact hsq.ofReal
  have hinv := hI.fourierInv_fourier_eq hFI (v := 0) hC.continuousAt
  rw [Real.fourierInv_eq', hFeq] at hinv
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at hinv
  rw [integral_complex_ofReal] at hinv
  exact (Complex.ofReal_injective hinv).symm

/-- Pointwise identity `y^{d-1} ψ̂(ye)² = y^{d-0} ψ̂(ye)² / y` on `(0,∞)`. -/
theorem d1z_nat_eq (hd : 1 ≤ d) {ψ : Euc d → ℝ} {e : Euc d} (y : ℝ) (hy : 0 < y) :
    y ^ (d - 1) * fdlPsiHat ψ (y • e) ^ 2 = y ^ ((d : ℝ) - 0) * fdlPsiHat ψ (y • e) ^ 2 / y := by
  have h := d1f_pow_aux hd hy 0 (fdlPsiHat ψ (y • e) ^ 2)
  rw [neg_zero, Real.rpow_zero, one_mul] at h
  exact h

/-- Polar form of `∫ ψ̂²` with the Fourier-side weight `t^{d-0}/t`. -/
theorem d1z_hat_sq_polar (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {e : Euc d}
    (he : ‖e‖ = 1) :
    ∫ ξ : Euc d, fdlPsiHat ψ ξ ^ 2 =
      d1f_omega d * ∫ t in Ioi (0 : ℝ), t ^ ((d : ℝ) - 0) * fdlPsiHat ψ (t • e) ^ 2 / t := by
  have hint : ∫ ξ : Euc d, fdlPsiHat ψ (‖ξ‖ • e) ^ 2 =
      d1f_omega d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * fdlPsiHat ψ (y • e) ^ 2 :=
    d1f_polar_integral hd (fun r : ℝ => fdlPsiHat ψ (r • e) ^ 2)
  have hA : ∫ ξ : Euc d, fdlPsiHat ψ ξ ^ 2 = ∫ ξ : Euc d, fdlPsiHat ψ (‖ξ‖ • e) ^ 2 := by
    congr 1
    funext ξ
    rw [d1z_hat_ray hψ he ξ]
  have hB : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * fdlPsiHat ψ (y • e) ^ 2 =
      ∫ t in Ioi (0 : ℝ), t ^ ((d : ℝ) - 0) * fdlPsiHat ψ (t • e) ^ 2 / t :=
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => d1z_nat_eq hd y (by exact hy))
  rw [hA, hint, hB]

/-- Closed form of `ω = d · vol(B_1)` (surface area of the unit sphere). -/
theorem d1z_omega_eq (hd : 1 ≤ d) :
    d1f_omega d = 2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh : (d : ℝ) / 2 ≠ 0 := (div_pos hd0 two_pos).ne'
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (div_pos hd0 two_pos)
  have hsq : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  have hvol : (volume (Metric.ball (0 : Euc d) 1)).toReal =
      Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    have := d1f_nontrivial hd
    have hGpos : 0 < Real.Gamma ((d : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    have hnn : 0 ≤ Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) :=
      div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hGpos.le
    rw [InnerProductSpace.volume_ball, finrank_euclideanSpace_fin, ENNReal.ofReal_one, one_pow,
      one_mul, ENNReal.toReal_ofReal hnn]
  unfold d1f_omega
  rw [hvol, Real.Gamma_add_one hh, hsq]
  field_simp

/-- The constant identity `ω · rieszConst d 0 · (2π)^{-d} = 1`. -/
theorem d1z_const_inv (hd : 1 ≤ d) :
    d1f_omega d * (rieszConst d 0 * (2 * Real.pi) ^ (0 - (d : ℝ))) = 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hh : (d : ℝ) / 2 ≠ 0 := (div_pos hd0 two_pos).ne'
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (div_pos hd0 two_pos)
  have hP : 0 < Real.pi ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hrc : rieszConst d 0 =
      2 ^ ((d : ℝ) - 1) * Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by
    unfold rieszConst
    rw [if_pos rfl]
  have h2 : (2 : ℝ) ^ ((d : ℝ) - 1) = 2 ^ d / 2 := by
    rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
  have hp2 : Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ ((d : ℝ) / 2) = Real.pi ^ d := by
    rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_natCast]
    congr 1
    ring
  have hX : (2 * Real.pi) ^ (0 - (d : ℝ)) = 1 / ((2 : ℝ) ^ d * Real.pi ^ d) := by
    rw [zero_sub, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.rpow_natCast,
      mul_pow, one_div]
  rw [d1z_omega_eq hd, hrc, hX, h2, ← hp2]
  field_simp

/-- **Packet D1F0 (`s = 0`).**  For `b > 0` with `b φ(0) = 1`, the Fourier-side integral
`b ∫_0^∞ t^{d} ψ̂(te)² dt/t` converges and equals `rieszConst d 0 (2π)^{-d}`. -/
theorem d1z_zero (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {b : ℝ} (_hb0 : 0 < b)
    (hbφ : b * fdlPhi ψ 0 = 1) {e : Euc d} (he : ‖e‖ = 1) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 0) * (fdlPsiHat ψ (t • e)) ^ 2 / t) (Set.Ioi 0) ∧
    b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 0) * (fdlPsiHat ψ (t • e)) ^ 2 / t =
      rieszConst d 0 * (2 * Real.pi) ^ (0 - (d : ℝ)) := by
  have hsq := d1z_hat_sq_int hd hψ he
  have hA' : (fun ξ : Euc d => fdlPsiHat ψ (‖ξ‖ • e) ^ 2) = fun ξ => fdlPsiHat ψ ξ ^ 2 := by
    funext ξ
    rw [d1z_hat_ray hψ he ξ]
  have hsq' : Integrable (fun ξ : Euc d => fdlPsiHat ψ (‖ξ‖ • e) ^ 2) := by
    rw [hA']
    exact hsq
  have hJnat : IntegrableOn (fun y : ℝ => y ^ (d - 1) * fdlPsiHat ψ (y • e) ^ 2) (Ioi 0) :=
    (d1f_polar_integrable hd (fun r : ℝ => fdlPsiHat ψ (r • e) ^ 2)).1 hsq'
  have hJ : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 0) * (fdlPsiHat ψ (t • e)) ^ 2 / t)
      (Set.Ioi 0) :=
    hJnat.congr_fun (fun y hy => d1z_nat_eq hd y (by exact hy)) measurableSet_Ioi
  refine ⟨hJ, ?_⟩
  have hpol := d1z_hat_sq_polar hd hψ he
  have hφ0 := d1z_phi_zero_eq_int hψ hsq
  have hω := d1f_omega_pos hd
  have hc := d1z_const_inv hd
  set J : ℝ := ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - 0) * (fdlPsiHat ψ (t • e)) ^ 2 / t with hJdef
  have hφJ : fdlPhi ψ 0 = d1f_omega d * J := hφ0.trans hpol
  have h1 : d1f_omega d * (b * J) = 1 := by
    calc d1f_omega d * (b * J) = b * (d1f_omega d * J) := by ring
      _ = b * fdlPhi ψ 0 := by rw [hφJ]
      _ = 1 := hbφ
  exact mul_left_cancel₀ hω.ne' (h1.trans hc.symm)

end HRS.MC.D1F0
