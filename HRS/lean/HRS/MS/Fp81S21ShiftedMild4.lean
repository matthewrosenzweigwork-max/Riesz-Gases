import HRS.MS.Fp81S21ShiftedMild3
import HRS.MS.CritWholeW2Shift
import HRS.MD.EQLawPath1

/-!
# HRS S2.1(iii), packet 9c: shifted Hilbert feature martingale

The local feature at time `u` is the compiled `r2WindowFeature` at physical
noise time `b+u`.  Its noise integrand is `s105Phi` on the shifted particle
path and shifted Brownian filtration.  Consequently the time integral in the
Hilbert covariation is over `[0,H]`, with no contribution from `[0,b]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.R26T3
open HRS.MD.EQLawPath
open HRS.MP.RdRem

/-- Local-time form of the shifted window feature. -/
def fp81s21_shiftedNoiseLocalFeatureFamily
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (H b : ℝ) : Fin p.d → ℝ → Euc p.d →
      KSpace p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H :=
  fun a u x => r2WindowFeature (r26t3_coeff R)
    ((wholeSpaceIndex p.d : ℕ) : ℝ) H (gradComp a) b (b + u) x

/-- Translate the compiled physical-time `S105Feat` estimate to the local
time interval `[0,H]`. -/
theorem fp81s21_shiftedNoiseLocalFeature_regular
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hphysical : HRS.MS.R2GenInit.S105Feat p.d
      ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b)) :
    HRS.MS.R2GenInit.S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H H
      (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) := by
  have hτ : 0 ≤ b + H := by linarith
  obtain ⟨B, hB, hbound⟩ := hphysical.bound
  refine ⟨⟨B, hB, ?_⟩, ?_, ?_⟩
  · intro a u hu x
    have hbu : b + u ∈ Icc (0 : ℝ) (b + H) := by constructor <;> linarith [hu.1, hu.2]
    change ‖r2WindowFeature (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ)
      H (gradComp a) b (b + u) x‖ ≤ B
    exact hbound a (b + u) hbu x
  · intro a u hu
    have hbu : b + u ∈ Icc (0 : ℝ) (b + H) := by constructor <;> linarith [hu.1, hu.2]
    change Continuous (fun x => r2WindowFeature (r26t3_coeff R)
      ((wholeSpaceIndex p.d : ℕ) : ℝ) H (gradComp a) b (b + u) x)
    exact hphysical.cont_x a (b + u) hbu
  · intro a x e
    have hweak := hphysical.weak_r a x e
    have hcomp : Measurable (fun u : ℝ =>
        inner ℝ e (fp81s21_shiftedNoiseFeatureFamily p R H b a
          (mrrClamp (b + H) (b + mrrClamp H u)) x)) := by
      exact hweak.comp (continuous_const.add (continuous_mrrClamp H)).measurable
    have heq : (fun u : ℝ => inner ℝ e
        (fp81s21_shiftedNoiseLocalFeatureFamily p R H b a (mrrClamp H u) x)) =
        fun u => inner ℝ e (fp81s21_shiftedNoiseFeatureFamily p R H b a
          (mrrClamp (b + H) (b + mrrClamp H u)) x) := by
      funext u
      have hu' : mrrClamp H u ∈ Icc (0 : ℝ) H := mrrClamp_mem hH u
      have hbu : b + mrrClamp H u ∈ Icc (0 : ℝ) (b + H) := by
        constructor <;> linarith [hu'.1, hu'.2]
      rw [mrrClamp_of_mem hbu]
      rfl
    rw [heq]
    exact hcomp

/-- The shifted window feature has a Hilbert-valued Itô martingale on the
shifted filtration.  Its covariation density is the exact `hsCovForm` of the
shifted `s105Phi` integrand. -/
theorem fp81s21_shiftedNoise_feature_martingale
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : HRS.MS.R2GenInit.S105Feat p.d
      ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b)) :
    ∃ M : ℝ → A.Ω → KSpace p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H,
      IsHilbertItoIntegral A.P
        (HRS.Whole.BreakdownS81.s81b_shiftFil F.ℱ b.toNNReal)
        (HRS.MD.EQLawPath.shiftProc F.Wc b.toNNReal)
        (HRS.MS.R2GenInit.s105Phi
          (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
          (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X)) M ∧
      IsHilbertMartingaleWithCovariation A.P
        (HRS.Whole.BreakdownS81.s81b_shiftFil F.ℱ b.toNNReal) H M
        (fun u ζ => hsCovForm
          (HRS.MS.R2GenInit.s105Phi
            (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
            (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X) u ζ)) := by
  have hlocal := fp81s21_shiftedNoiseLocalFeature_regular p R hH.le hb hphysical
  let ub : ℝ≥0 := b.toNNReal
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil F.ℱ ub
  let Wb := HRS.MD.EQLawPath.shiftProc F.Wc ub
  let Xb := HRS.Whole.S79.s79p_shiftX ub F.X
  have hfiltered := HRS.Whole.BreakdownS81.s81b_filtered_shift F.filtered ub
  have hq : 0 ≤ p.β⁻¹ := le_of_lt (inv_pos.mpr p.hβ)
  have hN1 : 1 ≤ N := by omega
  obtain ⟨M, hIto, hHM⟩ := HRS.MS.R2GenInit.s105_particle_martingale
    (le_of_lt hH) hlocal N hN1 p.β⁻¹ hq A.P ℱb Wb Xb hfiltered.brownian hfiltered.progressive
  exact ⟨M, hIto, hHM⟩

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoiseLocalFeature_regular
#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_feature_martingale

end HRS.Fp81.S21

end
