import HRS.MC.D1TAux5

/-!
# Packet D1T, auxiliary file 6: the Fubini identity `heatRiesz = b ∫ t^{d-s-1} G_ε(t) dt`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.MC.D1T

open HRS

variable {d : ℕ}

theorem d1t_heat_eq (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ x : Euc d, x ≠ 0 → Whole.rieszKernel d s x =
        b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t)
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
      exact (d1t_coeff hd hs hsd hψ hb0 hb k hk).1.const_mul _
  have hcoef : ∀ k, rieszCoeff d s k * e k * Torus.cosMode k x = b * ∫ t in Ioi (0 : ℝ), F k t := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [hF0]
      simp [rieszCoeff]
    · have : F k = fun t => (e k * Torus.cosMode k x) * (t ^ ((d : ℝ) - s) * d1tB ψ t k / t) :=
        funext (hFeq k)
      rw [this, integral_const_mul]
      have h2 := (d1t_coeff hd hs hsd hψ hb0 hb k hk).2
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
    · obtain ⟨hI, hJ⟩ := d1t_coeff hd hs hsd hψ hb0 hb k hk
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

end HRS.MC.D1T
