import HRS.MS.SA16Y4Io2

/-!
# S.A.16 (SA16Y4) Io3: Hardy-Littlewood-Sobolev bound for `∂_i (g * Ξ)` in the order-1 range

`sa16y4io_D1_bound`: for `1 ≤ d`, `0 ≤ s < d-1`, `d < p(s+1)`: `‖∂_i(g*Ξ)‖_p ≤ C ‖Ξ‖_q`, `1/q = 1/p + (d-s-1)/d`, for every Schwartz `Ξ`
(the sub-case `sa16q_D1_bound` restated for `s < d - 1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Io3
variable {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
include hd hs hs1

theorem sa16y4io_conv_fderiv_schwartz (ψ : 𝓢(Euc d, ℝ)) (x e : Euc d) :
    DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) x ∧
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) x e =
      HRS.Whole.convFun (rieszKernel d s) (fun z => fderiv ℝ ψ z e) x := by
  have h := sa16q_gen_fderiv (sa16q_g_meas d s) (sa16y4io_g_WI hd hs hs1) ψ x e
  rw [sa16q_conv_eq d s ψ, sa16q_conv_eq d s (fun z => fderiv ℝ ψ z e)]
  exact h

theorem sa16y4io_conv_contDiff_top (ψ : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) := by
  rw [sa16q_conv_eq d s ψ]
  exact sa16q_gen_contDiff_top (sa16q_g_meas d s) (sa16y4io_g_WI hd hs hs1) ψ

/-- `∂_i (g * Ξ) = K1_i * Ξ` -/
lemma sa16y4io_D1_eq (Ξ : 𝓢(Euc d, ℝ)) (i : Fin d) (x : Euc d) :
    fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ξ) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ y, sa16q_K1E s 0 i y * Ξ (x - y) := by
  obtain ⟨C, hC, hd1, hc, hD, hD'⟩ := sa16q_schwartz_hyp Ξ
  rw [(sa16y4io_conv_fderiv_schwartz hd hs hs1 Ξ x _).2, sa16q_conv_eq d s]
  simp only
  exact sa16y4io_ibp_g hd hs hs1 i x hC hd1 hc hD hD'

lemma sa16y4io_cont_D1 (Ξ : 𝓢(Euc d, ℝ)) (i : Fin d) :
    Continuous (fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ξ) x
      (EuclideanSpace.single i (1 : ℝ))) :=
  ((sa16y4io_conv_contDiff_top hd hs hs1 Ξ).continuous_fderiv (by simp)).clm_apply continuous_const

theorem sa16y4io_D1_bound {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ q C : ℝ, 1 < q ∧ q < p ∧ 1 / q = 1 / p + ((d : ℝ) - s - 1) / d ∧ 0 < C ∧
      ∀ (Ξ : 𝓢(Euc d, ℝ)) (i : Fin d),
        eLpNorm (fun x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) Ξ) x
          (EuclideanSpace.single i (1 : ℝ))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (⇑Ξ) (ENNReal.ofReal q) volume := by
  have hd1 : 1 ≤ d := hd
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
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
    (sa16y4io_cont_D1 hd hs hs1 Ξ i).aestronglyMeasurable (fun y hy => ?_)
    (fun x => sa16y4io_D1_eq hd hs hs1 Ξ i x)
  have e : ((d : ℝ) - s - 1 - d) = -(s + 1) := by ring
  rw [e]
  exact sa16q_K1E_bound hs 0 i hy
end Io3

end HRS.Whole.AppendixA.Phase2SA16Q
