import HRS.MS.Fp81S21WindowCovId3
import HRS.MS.Fp81S21RSValue4
import HRS.MC.E213U2

/-! The scalar RS identification once the window selection is available. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O

/-- Restriction of projective covariance tensors to the physical window. -/
def fp81s21_windowCovarianceMap (p : Parameters) (a : ℝ) (ha : 0 ≤ a) :
    projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2 →L[ℝ]
      projTensor (Window p) 2 :=
  ((tensorPow' 2 (HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
    (H := a + p.T) ha le_rfl)).comp
      (projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2).subtypeL).codRestrict
    (projTensor (Window p) 2) (fun v => HRS.MC.E213U2.e213u2_tensorPow'_mem 2 _ v.2)

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_windowCovarianceMap
