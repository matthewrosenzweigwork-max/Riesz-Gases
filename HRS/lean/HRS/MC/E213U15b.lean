import HRS.MC.E213U15a

/-!
# Packet e213u15, file b: the relocated statements `contract_drift` and `contract_J`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U15

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Final

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem contract_drift_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 3 Φ) :
    ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω) (gd.Dwin T a ω) ∂gd.P₀ =
      (1 / 2) * ∫ ω, (bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a))
        (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
  obtain ⟨ξ, hξ, h⟩ := HRS.MC.E213U13.chaos_data_proof gd T hT
  obtain ⟨hG, hGc, hDc, -⟩ := h a ha
  obtain ⟨C, hC⟩ := HRS.MC.E213U11.gd_moments_proof gd T hT
  obtain ⟨-, hZm, hDm, -, hint, -, -, -⟩ := hC a ha
  have hD1 : Integrable (fun ω => ‖gd.Dwin T a ω‖) gd.P₀ := by
    have := HRS.MC.E213U13.gd_D_memLp gd T hT a ha 1 le_rfl
    rw [ENNReal.ofReal_one, memLp_one_iff_integrable] at this
    exact this.norm
  exact u15_drift_generic gd.P₀ ξ hξ (gd.Zwin T a) (gd.Dwin T a) hG hGc (hDc 3 le_rfl) Φ hΦ hZm hDm hD1 hint

theorem contract_J_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 3 Φ) :
    ∫ ω, (gd.Jwin T a ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ =
      ∫ ω, (bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a)) (iteratedFDeriv ℝ 3 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
  obtain ⟨ξ, hξ, h⟩ := HRS.MC.E213U13.chaos_data_proof gd T hT
  obtain ⟨hG, hGc, -, hJc⟩ := h a ha
  obtain ⟨C, hC⟩ := HRS.MC.E213U11.gd_moments_proof gd T hT
  obtain ⟨hJmem, hZm, -, hJm, -, hint, -, -⟩ := hC a ha
  obtain ⟨CJ, -, hCJ⟩ := HRS.MC.E213U11.u11_J_moment2 hE gd T hT
  obtain ⟨hJ2i, -⟩ := hCJ a ha
  have heq : ∀ᵐ ω ∂gd.P₀, ((gd.JwinP T a ω : projTensor (PathSpace d m T) 2) : TensorDual (PathSpace d m T) 2) =
      gd.Jwin T a ω := by
    filter_upwards [hJmem] with ω hω
    simp [GaussData.JwinP, hω]
  have hJa : AEStronglyMeasurable (fun ω => ((gd.JwinP T a ω : projTensor (PathSpace d m T) 2) :
      TensorDual (PathSpace d m T) 2)) gd.P₀ := hJm.congr (heq.mono fun ω h => h.symm)
  have hJn : AEStronglyMeasurable (fun ω => ‖gd.Jwin T a ω‖) gd.P₀ :=
    (continuous_norm (E := TensorDual (PathSpace d m T) 2)).comp_aestronglyMeasurable hJm
  have hJ1 : Integrable (fun ω => ‖gd.Jwin T a ω‖) gd.P₀ := by
    refine ((integrable_const (1 : ℝ)).add hJ2i).mono' hJn (Eventually.of_forall fun ω => ?_)
    have h0 : 0 ≤ ‖gd.Jwin T a ω‖ := norm_nonneg (gd.Jwin T a ω)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    show ‖gd.Jwin T a ω‖ ≤ 1 + ‖gd.Jwin T a ω‖ ^ 2
    nlinarith [sq_nonneg (‖gd.Jwin T a ω‖ - 1)]
  have hJ1' : Integrable (fun ω => ‖((gd.JwinP T a ω : projTensor (PathSpace d m T) 2) :
      TensorDual (PathSpace d m T) 2)‖) gd.P₀ :=
    hJ1.congr (heq.mono fun ω h => by simp only [h])
  have hint' : Integrable (fun ω => ‖((gd.JwinP T a ω : projTensor (PathSpace d m T) 2) :
      TensorDual (PathSpace d m T) 2)‖ * ‖gd.Zwin T a ω‖) gd.P₀ :=
    hint.congr (heq.mono fun ω h => by simp only [h])
  have key := u15_J_generic gd.P₀ ξ hξ (gd.Zwin T a) hG hGc (gd.JwinP T a) 2 le_rfl (hJc 2 le_rfl) Φ hΦ hZm
    hJa hJ1' hint'
  have hb : bochTensor21 gd.P₀ (fun ω => ((gd.JwinP T a ω : projTensor (PathSpace d m T) 2) :
      TensorDual (PathSpace d m T) 2)) (gd.Zwin T a) = bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) := by
    unfold bochTensor21
    exact integral_congr_ae (heq.mono fun ω h => by simp only [h])
  rw [hb] at key
  rw [← key]
  exact integral_congr_ae (heq.mono fun ω h => by simp only [h])

end Final

end HRS.MC.E213U15

end
