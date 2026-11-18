import HRS.MS.Fp81S21HilbertMart
import HRS.MS.Fp81S21MovingDuality
import HRS.MS.Fp81S21WeightedMoments
import HRS.MS.Fp81S21CoeffMoments4

/-!
# HRS S2.1(iii), packet 32b B6-ii, SOL169 U2: raw compact-test Itô equation

This unit keeps the raw empirical field. In particular, it does not use the centered
`moving_orbit_zeta` identity. The `FilteredParticle` binder is explicit because the target Itô
integral uses its filtration and Brownian coordinates.

The intended exported U2 statement is `fp81s21_particle_raw_compact_ito` with
`physicalDrift := fp81s21_particle_raw_physicalDrift` and
`If := fp81s21_particle_raw_testIto` below. The proof is staged through the empirical Itô
identity in `Fp81S21RawIto2` before subtracting the mean-field weak equation and identifying the
raw commutator with `pairEnergy`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MH.DualityRd
open HRS.MS.R26T3 HRS.MS.R2Interp

/-- The coefficient of the raw quadratic field in the physical drift. -/
abbrev fp81s21_particle_raw_cN (N : ℕ) : ℝ := (Real.sqrt (N : ℝ))⁻¹

/-- The compact-test martingale integrand, with the physical B6-i normalization. -/
noncomputable def fp81s21_particle_raw_Phi
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (Fp : FilteredParticle A) (f : Euc p.d → ℝ) :
    ℝ → A.Ω → (Fin N × Fin p.d) → ℝ :=
  fun v ζ ik => fp81s21_b6i_scale N p.β *
    gradient f (Fp.X v.toNNReal ζ ik.1) ik.2

/-- The real-valued Itô integral associated with `fp81s21_particle_raw_Phi`. -/
noncomputable def fp81s21_particle_raw_testIto
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (Fp : FilteredParticle A) (f : Euc p.d → ℝ) :
    ℝ → A.Ω → ℝ :=
  itoIntegral A.P Fp.ℱ Fp.Wc (fp81s21_particle_raw_Phi p A Fp f)

/-- The raw, moving-reference drift for a compact test. -/
noncomputable def fp81s21_particle_raw_physicalDrift
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (f : Euc p.d → ℝ) (v : ℝ) (ζ : A.Ω) : ℝ :=
  fp81s21_particleEmpField R N A v ζ (generatorW (r26t3_coeff R) v f) -
    fp81s21_particle_raw_cN N * fp81s21_particleQuadRawField R N A v ζ f

/-- The raw empirical field is exactly `√N` times empirical-minus-reference pairing. -/
theorem fp81s21_particleEmpField_eq_sqrt_pair
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (v : ℝ) (ζ : A.Ω) (f : Euc p.d → ℝ) :
    fp81s21_particleEmpField R N A v ζ f =
      Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical (A.X v.toNNReal ζ)) f -
          HRS.Whole.pair (r26t3_mu R v) f) := by
  rfl

/-- The raw commutator field is exactly `N` times the physical pair energy. -/
theorem fp81s21_particleQuadRawField_eq_N_pairEnergy
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (v : ℝ) (ζ : A.Ω) (f : Euc p.d → ℝ) :
    fp81s21_particleQuadRawField R N A v ζ f =
      (N : ℝ) * pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X v.toNNReal ζ) (r26t3_mu R v) := by
  rfl

#print axioms HRS.Fp81.S21.fp81s21_particleEmpField_eq_sqrt_pair
#print axioms HRS.Fp81.S21.fp81s21_particleQuadRawField_eq_N_pairEnergy

end HRS.Fp81.S21
