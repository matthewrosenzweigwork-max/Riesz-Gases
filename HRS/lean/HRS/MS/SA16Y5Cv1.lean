import HRS.MS.SA16Y5Kr3
import HRS.MS.SA16Y5Gd1
import HRS.MS.SA16ZT3
import HRS.MS.SA16RHeat18

/-!
# S.A.16 (SA16Y5) Cv1: convolution toolkit for the heat-composed Riesz kernel (K1, convolution identities)

`sa16y5_young`: `‖k ⋆ u‖_p ≤ (∫|k|) ‖u‖_p` (`k` integrable, `u` continuous).
`sa16y5_cv_cc_contDiff`: `k ⋆ φ` is smooth for `k` locally integrable and `φ ∈ C_c^∞`;
`sa16y5_cv_fderiv`: `∂_v (k ⋆ φ) = k ⋆ ∂_vφ`.
`sa16y5_cv_comm`: `k₁ ⋆ (k₂ ⋆ φ) = k₂ ⋆ (k₁ ⋆ φ)` for integrable `k₁,k₂` and `φ ∈ C_c^∞`.
`sa16y5_D1`: `∂_i (ρ ⋆ u) = rn_ε ⋆ ∂_iu + V_{ε,i} ⋆ u` (`ρ = |z|^{-s}`, `0<s<d`).
`sa16y5_ddg_cv`: `∂_i∂_j g_a ⋆ φ = g_a ⋆ ∂_j∂_iφ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Cv1
variable {d : ℕ}

lemma sa16y5_young {k u : Euc d → ℝ} (hkm : Measurable k) (hk : Integrable k) (hu : Continuous u) {p : ℝ}
    (hp : 1 ≤ p) :
    eLpNorm (sa16r_cv k u) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ z, |k z|) * eLpNorm u (ENNReal.ofReal p) volume := by
  have h := sa16r_young hkm hu hp
  have e : ENNReal.ofReal (∫ z, |k z|) = ∫⁻ z, ‖k z‖ₑ := by
    have := ofReal_integral_norm_eq_lintegral_enorm hk
    simpa [Real.norm_eq_abs] using this
  rw [e]
  exact h

lemma sa16y5_cv_cc_contDiff {k φ : Euc d → ℝ} (hk : LocallyIntegrable k volume) (hφ : IsCcInfty φ) :
    ContDiff ℝ ∞ (sa16r_cv k φ) := by
  rw [sa16r_cv_eq_conv]
  exact hφ.2.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤) hk hφ.1

lemma sa16y5_cv_fderiv {k φ : Euc d → ℝ} (hk : LocallyIntegrable k volume) (hφ : IsCcInfty φ) (x v : Euc d) :
    fderiv ℝ (sa16r_cv k φ) x v = sa16r_cv k (fun y => fderiv ℝ φ y v) x := by
  have h1 := hφ.2.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hk
    (hφ.1.of_le (by exact_mod_cast le_top)) x
  rw [sa16r_cv_eq_conv, h1.fderiv]
  have hc : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fderiv ℝ φ) := hφ.2.fderiv ℝ
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hk hcs hc x v, ← sa16r_cv_eq_conv]

lemma sa16y5_cv_cv_prod {k₁ k₂ φ : Euc d → ℝ} (h1m : Measurable k₁) (h2m : Measurable k₂)
    (h1 : Integrable k₁) (h2 : Integrable k₂) (hφ : IsCcInfty φ) (x : Euc d) :
    sa16r_cv k₁ (sa16r_cv k₂ φ) x =
      ∫ q : Euc d × Euc d, k₁ q.1 * (k₂ q.2 * φ (x - q.1 - q.2)) ∂(volume.prod volume) := by
  obtain ⟨B, hB⟩ := sa16r_cc_bdd hφ
  have hφc : Continuous φ := hφ.1.continuous
  have hFi : Integrable (fun q : Euc d × Euc d => k₁ q.1 * (k₂ q.2 * φ (x - q.1 - q.2)))
      (volume.prod volume) := by
    have hprod : Integrable (fun q : Euc d × Euc d => k₁ q.1 * k₂ q.2) (volume.prod volume) :=
      h1.mul_prod h2
    refine Integrable.mono' (hprod.norm.mul_const B) ?_ (Eventually.of_forall fun q => ?_)
    · have : Measurable (fun q : Euc d × Euc d => k₁ q.1 * (k₂ q.2 * φ (x - q.1 - q.2))) := by
        refine (h1m.comp measurable_fst).mul ((h2m.comp measurable_snd).mul ?_)
        exact (hφc.measurable.comp (by fun_prop))
      exact this.aestronglyMeasurable
    · have hb : ‖φ (x - q.1 - q.2)‖ ≤ B := by simpa [Real.norm_eq_abs] using hB _
      rw [norm_mul, norm_mul]
      calc ‖k₁ q.1‖ * (‖k₂ q.2‖ * ‖φ (x - q.1 - q.2)‖) ≤ ‖k₁ q.1‖ * (‖k₂ q.2‖ * B) := by gcongr
        _ = ‖k₁ q.1 * k₂ q.2‖ * B := by rw [norm_mul]; ring
  rw [integral_prod _ hFi]
  unfold sa16r_cv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_const_mul]

lemma sa16y5_cv_comm {k₁ k₂ φ : Euc d → ℝ} (h1m : Measurable k₁) (h2m : Measurable k₂)
    (h1 : Integrable k₁) (h2 : Integrable k₂) (hφ : IsCcInfty φ) (x : Euc d) :
    sa16r_cv k₁ (sa16r_cv k₂ φ) x = sa16r_cv k₂ (sa16r_cv k₁ φ) x := by
  rw [sa16y5_cv_cv_prod h1m h2m h1 h2 hφ, sa16y5_cv_cv_prod h2m h1m h2 h1 hφ,
    ← integral_prod_swap]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [sub_right_comm]
  ring

end Cv1

end HRS.Whole.AppendixA.Phase2SA16R
