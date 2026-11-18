import HRS.MC.E213U19a

/-!
# Packet e213u20: `gaussian_heat_identity`

`E Φ(Z_a) = E U_{a,Φ}(0, I_a η^0)`: by the decomposition `Z_a = I_a η^0 + R_a Γ_0` with `Γ_0 ⊥ η^0` of law `canonFut (a+T) 0`
(`u19_decomp`), the left side is `∫ ∫ Φ(I_a F + R_a z) dγ_0(z) d(law η^0)(F)`, and the inner integral is `Ucan 0 (I_a F)`
by the definition of `Ucan`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U20

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U19

variable {d : ℕ}

section Main

variable {S : PreparedData d} {β₀ m : ℝ}

variable {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem gaussian_heat_identity_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    ∫ ω, Φ (gd.Zwin T a ω) ∂gd.P₀ = ∫ ω, Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a (gd.η 0 ω)) ∂gd.P₀ := by
  have hΦc : Continuous Φ := by simpa using hΦ.1.continuous
  have hbd : ∀ w, |Φ w| ≤ cbNorm 5 Φ := fun w => by
    have := (HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hΦ (j := 0) (Nat.zero_le _) w).trans
      (HRS.MC.E213U5.e213u5_sup_le_cbNorm (Nat.zero_le _))
    simpa using this
  rw [u19_decomp gd T hT a ha hΦc _ hbd]
  have hη : Measurable (gd.η 0) := HRS.MC.E213U16.u16_eta_meas gd 0
  have hH : 0 < a + T := by linarith
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (a + T) := ⟨le_rfl, hH.le⟩
  obtain ⟨hU1, -, -⟩ := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have hmeas : AEStronglyMeasurable (fun F => Ucan hE T a ha Φ 0 (Iwin S β₀ hE T a F)) (gd.P₀.map (gd.η 0)) :=
    (((hU1 0 h0).1.continuous).comp (Iwin S β₀ hE T a).continuous).aestronglyMeasurable
  exact integral_map hη.aemeasurable hmeas

end Main

end HRS.MC.E213U20

end
