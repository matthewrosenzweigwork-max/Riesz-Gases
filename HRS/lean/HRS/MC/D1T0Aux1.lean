import HRS.MC.D1F0
import HRS.MC.D1T

/-!
# Packet D1T0, auxiliary file 1: coefficient and Fubini identities for `0 ≤ s < d`, with the Fourier-side
normalisation `hF` as hypothesis (supplied by `D1F.d1f_pos` for `s > 0`, `D1F0.d1z_zero` for `s = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.MC.D1T0

open HRS HRS.MC.D1T

variable {d : ℕ}

theorem d1t0_coeff (hd : 1 ≤ d) {s : ℝ} {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ}
    (hF : ∀ e : Euc d, ‖e‖ = 1 →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t) (Set.Ioi 0) ∧
      b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t =
        rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ)))
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
  obtain ⟨hI, hJ⟩ := hF e he
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

theorem d1t0_heat_eq (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb0 : 0 < b)
    (hF : ∀ e : Euc d, ‖e‖ = 1 →
      IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t) (Set.Ioi 0) ∧
      b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t =
        rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ)))
        {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    heatRiesz d s ε x = b * ∫ t in Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * d1tG ψ x ε t / t := by
  set e : Lattice d → ℝ := fun k => Real.exp (-ε * Lattice.enorm k ^ 2) with he
  let F : Lattice d → ℝ → ℝ := fun k t =>
    t ^ ((d : ℝ) - s) * (e k * d1tB ψ t k * Torus.cosMode k x) / t
  have hFeq : ∀ k, ∀ t, F k t =
      (e k * Torus.cosMode k x) * (t ^ ((d : ℝ) - s) * d1tB ψ t k / t) := by
    intro k t; simp only [F]; ring
  have hF0 : F 0 = fun _ => 0 := by
    funext t; simp [F, d1tB]
  have hFint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := by
    intro k
    by_cases hk : k = 0
    · subst hk; rw [hF0]; exact integrable_zero _ _ _
    · have : F k = fun t => (e k * Torus.cosMode k x) * (t ^ ((d : ℝ) - s) * d1tB ψ t k / t) :=
        funext (hFeq k)
      rw [this]
      exact (d1t0_coeff hd hψ hF k hk).1.const_mul _
  have hcoef : ∀ k, rieszCoeff d s k * e k * Torus.cosMode k x = b * ∫ t in Ioi (0 : ℝ), F k t := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [hF0]
      simp [rieszCoeff]
    · have : F k = fun t => (e k * Torus.cosMode k x) * (t ^ ((d : ℝ) - s) * d1tB ψ t k / t) :=
        funext (hFeq k)
      rw [this, integral_const_mul]
      have h2 := (d1t0_coeff hd hψ hF k hk).2
      calc rieszCoeff d s k * e k * Torus.cosMode k x
          = (e k * Torus.cosMode k x) * (b * ∫ t in Ioi (0 : ℝ),
              t ^ ((d : ℝ) - s) * d1tB ψ t k / t) := by rw [h2]; ring
        _ = _ := by ring
  have hFsum : Summable fun k => ∫ t in Ioi (0 : ℝ), ‖F k t‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_)
      ((summable_gauss_lattice d ε hε).mul_right (|rieszConst d s| / b))
    by_cases hk : k = 0
    · subst hk
      have h0 : ∫ t in Ioi (0 : ℝ), ‖F 0 t‖ = 0 := by rw [hF0]; simp
      rw [h0]
      positivity
    · obtain ⟨hI, hJ⟩ := d1t0_coeff hd hψ hF k hk
      set g : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s) * d1tB ψ t k / t with hg
      have hgnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := by
        intro t ht
        have ht' : 0 < t := ht
        simp only [hg]
        have := d1tB_nonneg ψ t k
        positivity
      have hnorm : ∀ t ∈ Ioi (0 : ℝ), ‖F k t‖ = |e k * Torus.cosMode k x| * g t := by
        intro t ht
        rw [hFeq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hgnn t ht)]
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm, integral_const_mul]
      have hgint : 0 ≤ ∫ t in Ioi (0 : ℝ), g t := setIntegral_nonneg measurableSet_Ioi hgnn
      have hgle : ∫ t in Ioi (0 : ℝ), g t ≤ |rieszConst d s| / b := by
        rw [le_div_iff₀ hb0]
        calc (∫ t in Ioi (0 : ℝ), g t) * b = b * ∫ t in Ioi (0 : ℝ), g t := mul_comm _ _
          _ = rieszCoeff d s k := hJ
          _ ≤ |rieszCoeff d s k| := le_abs_self _
          _ ≤ |rieszConst d s| := KernelAux.abs_rieszCoeff_le d s hsd k
      have hc : |e k * Torus.cosMode k x| ≤ e k := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_cosMode_le k x)
      exact mul_le_mul hc hgle hgint (Real.exp_pos _).le
  have hHas := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hsum : ∑' k, ∫ t in Ioi (0 : ℝ), F k t = ∫ t in Ioi (0 : ℝ), ∑' k, F k t := hHas.tsum_eq
  have hpt : ∀ t : ℝ, ∑' k, F k t = t ^ ((d : ℝ) - s) * d1tG ψ x ε t / t := by
    intro t
    simp only [F, d1tG]
    rw [tsum_div_const, tsum_mul_left]
  have h1 : heatRiesz d s ε x = ∑' k, b * ∫ t in Ioi (0 : ℝ), F k t := by
    unfold heatRiesz
    exact tsum_congr hcoef
  rw [h1, tsum_mul_left, hsum]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t

end HRS.MC.D1T0
