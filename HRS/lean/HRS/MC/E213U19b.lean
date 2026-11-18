import HRS.MC.E213U19a

/-!
# Packet e213u19 (part b): `init_identification`

`D³Ψ_a(F)[ℓ_x,ℓ_x,ℓ_x] = ∫ D³Φ(I_aF + R_aΓ)[I_aℓ_x,I_aℓ_x,I_aℓ_x] dγ_0(Γ)` (differentiation under the integral sign and the
chain rule for the linear map `I_a`); averaging over `x` against `μ°` is the evaluation of `pushforward3 I_a K₀` on
`D³Φ(I_aF + R_aΓ)` (`bochTensor3_apply`); the decomposition `Z_a = I_aη^0 + R_aΓ_0` (part a) turns the double integral into
`E[(I_a^{⊗3}K₀)(D³Φ(Z_a))]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U19

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Main

variable {S : PreparedData d} {β₀ m : ℝ}

variable {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem init_identification_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    ∫ F, ∫ x, iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F
        ![ellVec S β₀ x, ellVec S β₀ x, ellVec S β₀ x] ∂S.μ0 ∂(gd.P₀.map (gd.η 0)) =
      ∫ ω, (pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)) (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
  have hH : 0 < a + T := by linarith
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (a + T) := ⟨le_rfl, hH.le⟩
  haveI := μ0_isProb S
  haveI hγp : IsProbabilityMeasure (canonFut hE (a + T) 0) :=
    (HRS.MC.E213U5.e213u5_canonFut_spec hE (a + T) hH 0 h0).2
  set Λ : (PathSpace d m T [×3]→L[ℝ] ℝ) →L[ℝ] ℝ := pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) with hΛ
  have hD3c : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ.1.continuous_iteratedFDeriv (by norm_num)
  have hbd : ∀ w, ‖iteratedFDeriv ℝ 3 Φ w‖ ≤ cbNorm 5 Φ := fun w =>
    (HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hΦ (j := 3) (by norm_num) w).trans
      (HRS.MC.E213U5.e213u5_sup_le_cbNorm (by norm_num))
  have hGc : Continuous fun w => Λ (iteratedFDeriv ℝ 3 Φ w) := Λ.continuous.comp hD3c
  have hGb : ∀ w, |Λ (iteratedFDeriv ℝ 3 Φ w)| ≤ ‖Λ‖ * cbNorm 5 Φ := fun w => by
    rw [← Real.norm_eq_abs]
    exact (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd w) (norm_nonneg _))
  rw [u19_decomp gd T hT a ha hGc _ hGb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
  obtain ⟨hK0m, hK0i⟩ := HRS.MC.E213U18.u18_ellVec_reg S β₀ hE.β₀_nonneg hE.s_lt
  have hA := bochTensor3_apply (P := S.μ0) hK0m hK0m hK0m hK0i
    (iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F)
  obtain ⟨hU1, -, -⟩ := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have hUcd : ContDiff ℝ 3 (Ucan hE T a ha Φ 0) := ((hU1 0 h0).1).of_le (by norm_num)
  have hchain : iteratedFDeriv ℝ 3 (fun z => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a z)) F =
      (iteratedFDeriv ℝ 3 (Ucan hE T a ha Φ 0) (Iwin S β₀ hE T a F)).compContinuousLinearMap
        (fun _ => Iwin S β₀ hE T a) :=
    (Iwin S β₀ hE T a).iteratedFDeriv_comp_right hUcd F (by exact_mod_cast le_refl 3)
  have hheat := (HRS.MC.E213U5.e213u5_heat_deriv (canonFut hE (a + T) 0) (winRestr a ha) hΦ).2 3 (by norm_num)
    (Iwin S β₀ hE T a F)
  have hint : Integrable (fun z => iteratedFDeriv ℝ 3 Φ (Iwin S β₀ hE T a F + winRestr a ha z))
      (canonFut hE (a + T) 0) :=
    Integrable.of_bound ((hD3c.comp (continuous_const.add (winRestr a ha).continuous)).aestronglyMeasurable)
      (cbNorm 5 Φ) (Filter.Eventually.of_forall fun z => hbd _)
  beta_reduce
  rw [← hA]
  change Kinit0 S β₀ _ = _
  rw [hchain]
  have h2 : (iteratedFDeriv ℝ 3 (Ucan hE T a ha Φ 0) (Iwin S β₀ hE T a F)) =
      ∫ z, iteratedFDeriv ℝ 3 Φ (Iwin S β₀ hE T a F + winRestr a ha z) ∂(canonFut hE (a + T) 0) := hheat
  rw [h2]
  exact (ContinuousLinearMap.integral_comp_comm Λ hint).symm

end Main

end HRS.MC.E213U19

end
