import HRS.MS.S21F_E00
import HRS.MS.CritForceAssemblyMaj
import HRS.MS.GapRevAux1
import HRS.MS.MfeConfAux99
import HRS.MS.S82P2Mom
import HRS.MS.MfeConfAux16

/-!
# S8.2 observed-time layer, packet T8A.V00: cutoff transition kernel, density and drift in flattened coordinates

Definitions only.  `r26t8a_flat` is a continuous linear equivalence (built from the explicit linear equivalence
`finProdFinEquiv`, continuous because both spaces are finite dimensional).  The R26-T3 E00 definitions are taken from
the compiled `S21F_E00` (`HRS.MS.R26T3.r26t3_*`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

def r26t8a_flat (d N : ℕ) : EucConfig d N ≃L[ℝ] Euc (N*d) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => WithLp.toLp 2 (fun k => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      invFun := fun x i => WithLp.toLp 2 (fun j => x (finProdFinEquiv (i,j)))
      left_inv := fun X => by funext i; ext j; simp
      right_inv := fun x => by
        ext k
        show x (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = x k
        rw [Prod.mk.eta, Equiv.apply_symm_apply]
      map_add' := fun X Y => by ext k; simp
      map_smul' := fun c X => by ext k; simp }

def r26t8a_cutTransition {Omega : Type*} [mOmega : MeasurableSpace Omega]
    (d N : ℕ) (s a beta : ℝ) (M : ℕ) (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ)
    (hW : IsBrownianFiltration P F W) (t : ℝ) (x : EucConfig d N) : Measure (EucConfig d N) :=
  (P.map (HRS.MD.EQLawPath.bfPath hW)).map (fun w => HRS.MS.R26T3.r26t3_flow d N s a beta M t (x,w))

def r26t8a_cutDensity (d N : ℕ) (s a beta : ℝ) (M : ℕ) (x : Euc (N*d)) : ℝ :=
  (HRS.MS.R26T3.r26t3_ZM d N s a beta M)⁻¹ *
    HRS.MS.R26T3.r26t3_weightM d N s a beta M ((r26t8a_flat d N).symm x)

def r26t8a_cutB (d N : ℕ) (s a beta : ℝ) (M : ℕ) (x : Euc (N*d)) : Euc (N*d) :=
  beta • (r26t8a_flat d N) (HRS.MS.MfeConf.sb1DriftM (quadraticGradientDyn d s a beta)
    (HRS.MS.R26T3.r26t3_regKernel d s M) N ((r26t8a_flat d N).symm x)) + (beta*a) • x

end HRS.MS.R26T8A

end
