import HRS.PDE.MovCAux5
import HRS.Equilibrium.RepulsiveBridge

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_Q_tendsto_weak (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ X, φ X ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) atTop
      (𝓝 (∫ X, φ X ∂(movT_Q (periodicRiesz d D.s) D N ρ r))) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hρ : IsProbDensity (ρ r) := h.mf.density r hr
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (h.ck r hr)
  haveI hμ : IsProbabilityMeasure (withDensityReal (ρ r)) := isProb_withDensityReal hρ
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  -- measurability of the singular energy
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (Bg + 1) := fun z _ => by
    have := hBg z; linarith
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, -⟩ := rowOK_g_h hd D.s D.hs0 D.hsd (Bg + 1) hw 0 hMρ0 hρΛ
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)
  have hFm : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d D.s) X
      (withDensityReal (ρ r))) := measurable_modulatedEnergy hgR
  have hFnm : ∀ n, Measurable (fun X : Config d N => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X
      (withDensityReal (ρ r))) := fun n =>
    measurable_modulatedEnergyKernel (movc_gReg_measurable hd D.hs0 D.hsd (M n)) _
  obtain ⟨c, hc⟩ := movc_energy_lower hd D.hs0 D.hsd (by omega : 1 ≤ N) hρ hcont (N := N)
  obtain ⟨Cφ, hCφ⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  have hae := Repulsive.ae_notMem_collisionSet hd (rfl : withDensityReal (ρ r) = withDensityReal (ρ r)) hρ N
  unfold movT_Q modulatedGibbs gibbsNormalizer
  have key := movc_gibbs_tendsto (Measure.pi fun _ : Fin N => withDensityReal (ρ r))
    (-D.invβ⁻¹ * N) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    (fun n X => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X (withDensityReal (ρ r)))
    (fun X => modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal (ρ r)))
    hFnm hFm c (fun n X => hc (M n) (hM0 n) X)
    (hae.mono fun X hX => movc_energy_tendsto hd D.hs0 D.hsd hρ hcont hM hM0 hX)
    φ hφ.measurable (max Cφ 0) (fun X => by
      have := hCφ X (Set.mem_univ _)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _))
  exact key

end HRS
