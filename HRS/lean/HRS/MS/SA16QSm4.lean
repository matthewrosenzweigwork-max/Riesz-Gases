import HRS.MS.SA16QSm3

/-!
# S.A.16 (SA16Q), E6 part 10: `L^p` bounds for the two building blocks

For `d ≥ 2`, `0 ≤ s ≤ d - 2`, `p ≥ 2`, `d < p (s+1)` and Schwartz `Ξ, Ψ` (with `G = g * ·`):

* `sa16q_D1_bound`: `‖∂_i (G Ξ)‖_p ≤ C₁ ‖Ξ‖_{q₁}`, `1/q₁ = 1/p + (d-s-1)/d`  (HLS, kernel `∂_i g`);
* `sa16q_D2_bound`: `‖∂_i ∂_j (G Ψ)‖_p ≤ C₂ ‖Ψ‖_r` with `r = p` (`s = d-2`, Calderon-Zygmund) or
  `1/r = 1/p + (d-s-2)/d` (`s < d-2`, HLS for the kernel `∂_i ∂_j g`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Bounds
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

lemma sa16q_hGs (ψ : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) := sa16q_conv_contDiff_top hd hs hs2 ψ

/-- `∂_i (g * Ξ) = K1_i * Ξ` -/
lemma sa16q_D1_eq (Ξ : 𝓢(Euc d, ℝ)) (i : Fin d) (x : Euc d) :
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ξ) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ y, sa16q_K1E s 0 i y * Ξ (x - y) := by
  obtain ⟨C, hC, hd1, hc, hD, hD'⟩ := sa16q_schwartz_hyp Ξ
  rw [(sa16q_conv_fderiv_schwartz hd hs hs2 Ξ x _).2, sa16q_conv_eq d s]
  simp only
  exact sa16q_ibp_g hd hs hs2 i x hC hd1 hc hD hD'

/-- `∂_i ∂_j (g * Ψ) = K2_{ij} * Ψ` for `s < d - 2` -/
lemma sa16q_D2_eq (hs3 : s < (d : ℝ) - 2) (Ψ : 𝓢(Euc d, ℝ)) (i j : Fin d) (x : Euc d) :
    fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ψ) y
        (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ y, sa16q_K2E s 0 i j y * Ψ (x - y) := by
  obtain ⟨C, hC, hd1, hc, hD, hD'⟩ := sa16q_schwartz_hyp Ψ
  rw [sa16q_fderiv_conv_fun hd hs hs2 Ψ (EuclideanSpace.single j (1 : ℝ)), sa16q_D1_eq hd hs hs2]
  have := sa16q_ibp_K1 hd hs hs3 i j x hC hd1 hc hD hD'
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sa16q_dS_apply]

lemma sa16q_cont_D1 (Ξ : 𝓢(Euc d, ℝ)) (i : Fin d) :
    Continuous (fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ξ) x
      (EuclideanSpace.single i (1 : ℝ))) :=
  ((sa16q_hGs hd hs hs2 Ξ).continuous_fderiv (by simp)).clm_apply continuous_const

lemma sa16q_cont_D2 (Ψ : 𝓢(Euc d, ℝ)) (i j : Fin d) :
    Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ψ) y
        (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ))) := by
  have hV : ContDiff ℝ ∞ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ψ) y
      (EuclideanSpace.single j (1 : ℝ))) :=
    ((sa16q_hGs hd hs hs2 Ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hV.continuous_fderiv (by simp)).clm_apply continuous_const

theorem sa16q_D1_bound {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ q C : ℝ, 1 < q ∧ q < p ∧ 1 / q = 1 / p + ((d : ℝ) - s - 1) / d ∧ 0 < C ∧
      ∀ (Ξ : 𝓢(Euc d, ℝ)) (i : Fin d),
        eLpNorm (fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ξ) x
          (EuclideanSpace.single i (1 : ℝ))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑Ξ) (ENNReal.ofReal q) volume := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hp0 : 0 < p := by linarith
  have hσ : 0 < (d : ℝ) - s - 1 := by linarith
  have hlt : 1 / p + ((d : ℝ) - s - 1) / d < 1 := by
    have h1 : 1 / p < (s + 1) / d := by
      rw [div_lt_div_iff₀ hp0 hd0]; linarith
    have h2 : ((d : ℝ) - s - 1) / d = 1 - (s + 1) / d := by field_simp; ring
    linarith
  obtain ⟨q, hq1, hqp, hrel, hrel'⟩ := sa16q_exps hd1 hp0 hσ hlt
  obtain ⟨C, hC, hK⟩ := sa16q_hls_conv hd1 (σ := (d : ℝ) - s - 1) (p := p) (q := q) hσ hq1 hqp hrel
  have hg := sa16q_gam_pos hs
  refine ⟨q, C * sa16q_gam s, hq1, hqp, hrel', mul_pos hC hg, fun Ξ i => ?_⟩
  refine hK (sa16q_gam s) hg.le (sa16q_K1E s 0 i) Ξ _ Ξ.continuous.aestronglyMeasurable
    (sa16q_cont_D1 hd hs hs2 Ξ i).aestronglyMeasurable (fun y hy => ?_)
    (fun x => sa16q_D1_eq hd hs hs2 Ξ i x)
  have e : ((d : ℝ) - s - 1 - d) = -(s + 1) := by ring
  rw [e]
  exact sa16q_K1E_bound hs 0 i hy

theorem sa16q_D2_bound {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ r C : ℝ, 1 < r ∧ r ≤ p ∧ 0 < C ∧
      (r = p ∨ (r < p ∧ 1 / r = 1 / p + ((d : ℝ) - s - 2) / d)) ∧
      ∀ (Ψ : 𝓢(Euc d, ℝ)) (i j : Fin d),
        eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ψ) y
          (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)))
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑Ψ) (ENNReal.ofReal r) volume := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hp0 : 0 < p := by linarith
  by_cases hs3 : s < (d : ℝ) - 2
  · have hσ : 0 < (d : ℝ) - s - 2 := by linarith
    have hlt : 1 / p + ((d : ℝ) - s - 2) / d < 1 := by
      have h1 : 1 / p < (s + 2) / d := by
        rw [div_lt_div_iff₀ hp0 hd0]; nlinarith
      have h2 : ((d : ℝ) - s - 2) / d = 1 - (s + 2) / d := by field_simp; ring
      linarith
    obtain ⟨q, hq1, hqp, hrel, hrel'⟩ := sa16q_exps hd1 hp0 hσ hlt
    obtain ⟨C, hC, hK⟩ := sa16q_hls_conv hd1 (σ := (d : ℝ) - s - 2) (p := p) (q := q) hσ hq1 hqp hrel
    have hg := sa16q_gam_pos hs
    have hc : 0 ≤ sa16q_gam s * (s + 3) := mul_nonneg hg.le (by linarith)
    refine ⟨q, C * (sa16q_gam s * (s + 3)), hq1, hqp.le, mul_pos hC (mul_pos hg (by linarith)),
      Or.inr ⟨hqp, hrel'⟩, fun Ψ i j => ?_⟩
    refine hK (sa16q_gam s * (s + 3)) hc (sa16q_K2E s 0 i j) Ψ _ Ψ.continuous.aestronglyMeasurable
      (sa16q_cont_D2 hd hs hs2 Ψ i j).aestronglyMeasurable (fun y hy => ?_)
      (fun x => sa16q_D2_eq hd hs hs2 hs3 Ψ i j x)
    have e : ((d : ℝ) - s - 2 - d) = -(s + 2) := by ring
    rw [e]
    exact sa16q_K2E_bound hs 0 i j hy
  · have hseq : s = (d : ℝ) - 2 := le_antisymm hs2 (not_lt.1 hs3)
    subst hseq
    obtain ⟨C, hC0, hCZ⟩ := HRS.S16Cze.s16cze_even_cz hd (p := p) (by linarith)
    refine ⟨p, C + 1, by linarith, le_rfl, by linarith, Or.inl rfl, fun Ψ i j => ?_⟩
    exact (hCZ i j Ψ).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)

end Bounds

end HRS.Whole.AppendixA.Phase2SA16Q
