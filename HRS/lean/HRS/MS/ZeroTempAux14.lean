import HRS.MS.ZeroTempAux13

/-!
# SA11, packet D1: the expected time-integrated energy, and the per-`N` conclusion

* `sa11_energy_moment`: `E ∫_0^T ofReal(F_N(X_r,ρ_r) + oNΛ + c₂ e) dr ≤ T (𝔈_N + c₂ e_N)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.ZeroTemp

variable {d : ℕ}

theorem sa11_energy_moment {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ}
    {rs mV : ℕ} {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 rs mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {c₂ : ℝ} (hc₂ : 0 ≤ c₂) {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    (hXm : Measurable fun p : ℝ × (R N).Ω => (R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T p.1)) p.2) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
        (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀ Λ N + c₂ * e N)) ∂(R N).P ≤
      ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + c₂ * e N) := by
  haveI := (R N).isProb
  have hT : 0 ≤ S.T := S.hT.le
  set Gc : ℝ → (R N).Ω → ℝ := fun r ζ =>
    rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T r)) ζ)
      (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r))) + oNΛ d S.s C₀ Λ N + c₂ * e N with hGc
  have hGm : Measurable fun p : ℝ × (R N).Ω => Gc p.1 p.2 :=
    ((HRS.MP.RdRem.mrr_energy_meas hS hN).comp (measurable_fst.prodMk hXm)).add measurable_const
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN).le
  have hce : 0 ≤ c₂ * e N := mul_nonneg hc₂ (he N)
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N + c₂ * e N) := by
    intro r hr
    have hb := hS.energy.bound N hN r hr
    calc ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P
        ≤ ∫⁻ ζ, (ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) +
            ENNReal.ofReal (c₂ * e N)) ∂(R N).P := by
          refine lintegral_mono fun ζ => ?_
          simp only [hGc, HRS.MP.RdRem.mrrClamp_of_mem hr]
          exact ENNReal.ofReal_add_le
      _ = ∫⁻ ζ, ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) ∂(R N).P +
            ENNReal.ofReal (c₂ * e N) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (𝔈 N) + ENNReal.ofReal (c₂ * e N) := add_le_add hb le_rfl
      _ = ENNReal.ofReal (𝔈 N + c₂ * e N) := (ENNReal.ofReal_add h𝔈 hce).symm
  have hZ := HRS.MP.RdRem.mrr_time_moment (R N).P Gc hGm _ hmom
  refine le_trans (le_of_eq ?_) hZ
  refine lintegral_congr fun ζ => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only [hGc, HRS.MP.RdRem.mrrClamp_of_mem hr]

end HRS.MS.ZeroTemp
