import HRS.MS.Fp81S21RawIto3
import HRS.MH.DualityRdC2
import HRS.MS.R2InterpAux7
import HRS.MS.R2MtAux3
import HRS.MS.R2SeAux1

/-! Identify the fluctuation residual with the raw pair energy, retaining the
physical deleted-diagonal convention and its built-in factor `1/2`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd
open HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2Mt

theorem fp81s21_particle_flucInteraction_eq_neg_pairEnergy
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (Fp : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A T)
    {f : Euc p.d → ℝ} (hf : IsR2Test f)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (ζ : A.Ω)
    (hno : Fp.X u.toNNReal ζ ∉ eucCollisionSet p.d N) :
    flucInteractionRd (quadraticGradientDyn p.d p.s p.a p.β) f
        (Fp.X u.toNNReal ζ) (R.ρ u) =
      -pairEnergy (commutatorKernel p.d p.s (fun x => gradient f x))
        (Fp.X u.toNNReal ζ) (r26t3_mu R u) := by
  classical
  let D : WholeDyn p.d := quadraticGradientDyn p.d p.s p.a p.β
  have hfMemCb : MemCb 2 f := HRS.MH.DualityRd.db1_memCb_of_compact
    (hf.1.of_le (by norm_num)) hf.2
  obtain ⟨L, hL0, hLip⟩ := HRS.MH.DualityRd.db1_grad_lip hfMemCb
  have hgradLip : LipschitzWith ⟨L, hL0⟩ (gradient f) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hLip x y
  let Lnn : ℝ≥0 := ⟨L, hL0⟩
  have hKernel :
      IsBoundedPairKernel p.s ((p.s + 1) * (Lnn : ℝ))
        (commutatorKernel p.d p.s (fun x => gradient f x)) := by
    simpa [Lnn] using S99.s99_comm_isBounded p.hs0 Lnn hgradLip
  obtain ⟨M, Lρ, hround⟩ := hphys.round2
  have hroundu : IsRound2Density p.d p.s M Lρ (R.ρ u) := hround u hu
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hkernelInt : ∀ x : Euc p.d,
      Integrable (fun y => commutatorKernel p.d p.s (fun x => gradient f x) x y)
        (r26t3_mu R u) := by
    have hInt := HRS.MS.R2Mt.s92_kernel_integrable hd1 p.hs0 hsd M
      hroundu.prob hroundu.bdd hKernel
    intro x
    simpa [r26t3_mu] using hInt.1 x
  have hNpos : 0 < N := by omega
  exact HRS.MS.R2Interp.s102_flucInteractionRd_eq D rfl hNpos f
    (Fp.X u.toNNReal ζ) hno (R.ρ u) hkernelInt

#print axioms HRS.Fp81.S21.fp81s21_particle_flucInteraction_eq_neg_pairEnergy

end HRS.Fp81.S21
