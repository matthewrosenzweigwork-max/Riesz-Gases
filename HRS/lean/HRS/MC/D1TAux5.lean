import HRS.MC.D1TAux4

/-!
# Packet D1T, auxiliary file 5: the Fourier coefficients of the Riesz kernel as `t`-integrals, and the
Fubini identity `heatRiesz = b ∫ t^{d-s-1} G_ε(t) dt`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.MC.D1T

open HRS

variable {d : ℕ}

theorem d1t_coeff (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ x : Euc d, x ≠ 0 → Whole.rieszKernel d s x =
        b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t)
    (k : Lattice d) (hk : k ≠ 0) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * d1tB ψ t k / t) (Ioi 0) ∧
    b * ∫ t in Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * d1tB ψ t k / t = rieszCoeff d s k := by
  set r : ℝ := Lattice.enorm k with hr_def
  have hr1 : 1 ≤ r := one_le_enorm k hk
  have hr : 0 < r := lt_of_lt_of_le one_pos hr1
  set e : Euc d := r⁻¹ • Lattice.toEuc k with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_cancel₀ hr.ne'
  obtain ⟨hI, hJ⟩ := D1F.d1f_pos hd hs hsd hψ hb0 hb he
  set h : ℝ → ℝ := fun u => u ^ ((d : ℝ) - s) * (fdlPsiHat ψ (u • e)) ^ 2 / u with hh
  have key : ∀ t ∈ Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * d1tB ψ t k / t = r ^ (s - d + 1) * h (r * t) := by
    intro t ht
    have ht' : 0 < t := ht
    have hv : (r * t) • e = t • Lattice.toEuc k := by
      rw [he_def, smul_smul]
      have : r * t * r⁻¹ = t := by field_simp
      rw [this]
    have e1 : r ^ (s - d + 1) * r ^ ((d : ℝ) - s) = r := by
      rw [← Real.rpow_add hr]
      have : s - d + 1 + (d - s) = (1 : ℝ) := by ring
      rw [this, Real.rpow_one]
    simp only [hh, d1tB, hk, if_false, hv]
    rw [Real.mul_rpow hr.le ht'.le]
    calc t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t
        = (r ^ (s - d + 1) * r ^ ((d : ℝ) - s)) * t ^ ((d : ℝ) - s) *
            fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / (r * t) := by
          rw [e1]; field_simp
      _ = _ := by ring
  have hint : IntegrableOn (fun t : ℝ => h (r * t)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff h 0 hr]
    simpa using hI
  refine ⟨?_, ?_⟩
  · have h5 : IntegrableOn (fun t : ℝ => r ^ (s - d + 1) * h (r * t)) (Ioi 0) := hint.const_mul _
    exact IntegrableOn.congr_fun h5 (fun t ht => (key t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul]
    have h2 := integral_comp_mul_left_Ioi h 0 hr
    simp only [mul_zero] at h2
    rw [h2]
    have hbJ : b * ∫ u in Ioi (0 : ℝ), h u = rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ)) := hJ
    unfold rieszCoeff
    simp only [hk, if_false]
    rw [Real.mul_rpow (by positivity) hr.le]
    have e2 : r ^ (s - d + 1) = r ^ (s - (d : ℝ)) * r := Real.rpow_add_one hr.ne' _
    rw [smul_eq_mul]
    calc b * (r ^ (s - d + 1) * (r⁻¹ * ∫ u in Ioi (0 : ℝ), h u))
        = (r ^ (s - (d : ℝ)) * r * r⁻¹) * (b * ∫ u in Ioi (0 : ℝ), h u) := by rw [e2]; ring
      _ = _ := by rw [hbJ]; field_simp

end HRS.MC.D1T
