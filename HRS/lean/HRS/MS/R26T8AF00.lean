import HRS.MH.ScreenedS3
import HRS.MS.CritForceAssemblyMaj
import HRS.MS.MovOscAux4
import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.F00: the actual critical convolution and unprojected generator iterates
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

def r26t8a_forceConv {d : ℕ} (i : Fin d) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  (convGradConvW (rieszKernelGrad d (criticalS d)) h x) i

def r26t8a_Euler {d : ℕ} (h : Euc d → ℝ) (x : Euc d) : ℝ := fderiv ℝ h x x

def r26t8a_SobSmooth {d : ℕ} (f : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ r : ℕ, HRS.PDE.ToolboxRd.MemSobolev (r : ℝ) f

def r26t8a_LIter {d : ℕ} (a beta : ℝ) (rho : Euc d → ℝ) (j : ℕ) (f : Euc d → ℝ) : Euc d → ℝ :=
  (fun h => generatorW (critCoeff d a beta rho) 0 h)^[j] f

def r26t8a_localP {d : ℕ} (a beta : ℝ) (rho f : Euc d → ℝ) (x : Euc d) : ℝ :=
  beta⁻¹ * Laplacian.laplacian f x - a * fderiv ℝ f x x -
    inner ℝ (forceMean rho x) (gradient f x)

end HRS.MS.R26T8A

end
