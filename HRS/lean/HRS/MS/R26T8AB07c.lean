import HRS.MS.R26T8AD01
import HRS.MS.WrQuadAux1
import HRS.MS.Comm
import HRS.MS.CritForceDefs
import HRS.MS.R26T8AB07a1

/-!
# S8.2 observed-time layer, packet T8A.B07c: identification of the actual centering

At every `w` the centered integrand `s82Centered ... b r w` is `√N/2` times the centered pair functional of the
commutator kernel of the test function `propagatorW C r b φ_α` evaluated at `X_r(w)`, minus its mean under the actual
law `P`.  The functional is measurable (jointly measurable kernel), so its mean under `P` is its mean under the law of
`X_r`, which is `canonicalP` by the Gibbs invariance field of the realization.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b07c_pointwise (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (alpha : MultiIndex d) (b r : ℝ) (hr : 0≤r) (hrb : r≤b) :
    ∀ w, HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha b r w =
      scalarForcing a beta rho
        (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) (X r.toNNReal w) := by
  classical
  intro w
  obtain ⟨C0, hC0, hCb⟩ := r26t8a_b07a1_int_bound d hd a beta ha hbeta
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := (hCb rho hrho).1
  set f := propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha) with hf
  have hGm : Measurable (gradient f) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  have hhm : Measurable (Function.uncurry (commutatorKernel d (criticalS d) (gradient f))) :=
    HRS.MS.Comm.comm_meas (s := criticalS d) (gradient f) hGm
  have hDm : Measurable fun Y : EucConfig d N => centeredPairFunctional
      (commutatorKernel d (criticalS d) (gradient f)) Y (HRS.Whole.withDensityReal rho) :=
    HRS.MS.Wr.wr14a_measurable_D hhm _
  have hlaw : P.map (X r.toNNReal) = canonicalP d N a beta :=
    hX.invariant P b X0 W X hX.brownian hX.indep hX.init (hX.solution b) r.toNNReal
      (by rw [Real.coe_toNNReal r hr]; exact hrb)
  have hint : ∫ ζ, centeredPairFunctional (commutatorKernel d (criticalS d) (gradient f))
      (X r.toNNReal ζ) (HRS.Whole.withDensityReal rho) ∂P =
      ∫ Y, centeredPairFunctional (commutatorKernel d (criticalS d) (gradient f)) Y
        (HRS.Whole.withDensityReal rho) ∂(canonicalP d N a beta) := by
    rw [← hlaw, integral_map ((hX.solution b).adapted _).aemeasurable hDm.aestronglyMeasurable]
  show Real.sqrt N / 2 * (centeredPairFunctional (commutatorKernel d (criticalS d) (gradient f))
      (X r.toNNReal w) (HRS.Whole.withDensityReal rho) -
      ∫ ζ, centeredPairFunctional (commutatorKernel d (criticalS d) (gradient f))
        (X r.toNNReal ζ) (HRS.Whole.withDensityReal rho) ∂P) =
    Real.sqrt N / 2 * (centeredPairFunctional (commutatorKernel d (criticalS d) (gradient f))
      (X r.toNNReal w) (HRS.Whole.withDensityReal rho) -
      ∫ Y, centeredPairFunctional (commutatorKernel d (criticalS d) (gradient f)) Y
        (HRS.Whole.withDensityReal rho) ∂(canonicalP d N a beta))
  rw [hint]

theorem r26t8a_centering_identification (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (alpha : MultiIndex d) (b r : ℝ) (hr : 0≤r) (hrb : r≤b) :
    HRS.MS.S82BD.s82Centered d N a beta m rho P X alpha b r =ᵐ[P]
      fun w => scalarForcing a beta rho
        (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) (X r.toNNReal w) :=
  Filter.Eventually.of_forall (r26t8a_b07c_pointwise d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho
    Psi hPsi horb P X0 W X hX alpha b r hr hrb)

end HRS.MS.R26T8A

end
