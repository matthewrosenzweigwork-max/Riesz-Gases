import HRS.MS.Fp81S21JointN

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped BigOperators
open HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

namespace HRS.Fp81.S21

local instance fp81s21_jointN2_U_measSpace (H : ℝ) :
    MeasurableSpace (fp81s21_jointP_U H) := borel _
local instance fp81s21_jointN2_U_borelSpace (H : ℝ) :
    BorelSpace (fp81s21_jointP_U H) := ⟨rfl⟩

/-- The raw particle fluctuation used by `flucPathW`, expressed through the
compiled `etaB` and moving-law definitions. -/
def fp81s21_jointN_rawEtaAt {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (u : ℝ) (ω : A.Ω) :
    OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
  HRS.Whole.etaB (wholeSpaceIndex p.d : ℝ) (A.X u.toNNReal ω)
    (r26t3_mu R u)

/-- A time-class representative of the raw finite-rank particle polynomial
field for the shared rank family. The raw polynomial is the `JointW`
polynomial `fp81s21_polyAt` already loaded by the common-rank chain. -/
def fp81s21_ParticleRawPolynomialTime31
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k N : ℕ) (A : Particle R N) (a H : ℝ)
    (Uraw : A.Ω → fp81s21_jointP_U H) : Prop :=
  ∃ Mraw : ℝ, ∃ qraw : ℝ → A.Ω → r26t6_Coeff,
    Measurable (Function.uncurry qraw) ∧
    (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      qraw u ω = ∑ j : Fin m,
        fp81s21_polyAt (D (θ j) k)
          (fp81s21_jointN_rawEtaAt R A u ω) • fp81s21_coeffBasis j) ∧
    fp81s21_TimeL2Rep A.P qraw Mraw a H Uraw

/-- The three approximation stages used for the particle joint estimate:
spatial projection, shared-rank kernel approximation, and the uniform
finite-rank diagonal correction. -/
theorem fp81s21_jointN_pair_sqerr_compose
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Uη UB Pη PB Uraw Ur : Ω → V)
    (spatialError kernelError diagonalError : ℝ)
    (hspatial : 0 ≤ spatialError) (hkernel : 0 ≤ kernelError)
    (hdiagonal : 0 ≤ diagonalError)
    (hUη : AEStronglyMeasurable Uη P) (hUB : AEStronglyMeasurable UB P)
    (hPη : AEStronglyMeasurable Pη P) (hPB : AEStronglyMeasurable PB P)
    (hUr : AEStronglyMeasurable Ur P)
    (hcenter : AEStronglyMeasurable (fp81s21_center P Uraw) P)
    (hproj : fp81s21_SqErr P (fun ω => (Uη ω, UB ω))
      (fun ω => (Pη ω, PB ω)) spatialError)
    (hkernelPair : fp81s21_SqErr P (fun ω => (Pη ω, PB ω))
      (fun ω => (Pη ω, Ur ω)) kernelError)
    (hdiag : fp81s21_SqErr P (fp81s21_center P Uraw) Ur diagonalError) :
    fp81s21_SqErr P (fun ω => (Uη ω, UB ω))
      (fun ω => (Pη ω, fp81s21_center P Uraw ω))
      (spatialError + kernelError + diagonalError) := by
  have hdiagPair := fp81s21_jointG_kernel_pair_sqerr P Pη
    (fp81s21_center P Uraw) Ur diagonalError hdiagonal hdiag
  have hmid := fp81s21_jointG_sqerr_trans P
    (fun ω => (Uη ω, UB ω))
    (fun ω => (Pη ω, PB ω))
    (fun ω => (Pη ω, Ur ω))
    spatialError kernelError
    (hUη.prodMk hUB) (hPη.prodMk hPB) (hPη.prodMk hUr)
    hspatial hkernel hproj hkernelPair
  have hlast := fp81s21_jointG_sqerr_trans P
    (fun ω => (Uη ω, UB ω))
    (fun ω => (Pη ω, Ur ω))
    (fun ω => (Pη ω, fp81s21_center P Uraw ω))
    (spatialError + kernelError) diagonalError
    (hUη.prodMk hUB) (hPη.prodMk hUr) (hPη.prodMk hcenter)
    (add_nonneg hspatial hkernel) hdiagonal hmid hdiagPair
  simpa [add_assoc] using hlast

#print axioms fp81s21_jointN_rawEtaAt
#print axioms fp81s21_ParticleRawPolynomialTime31
#print axioms fp81s21_jointN_pair_sqerr_compose

end HRS.Fp81.S21

end
