import HRS.MP.SelfSimP4Reg
import HRS.Stochastic.Integral

/-!
# S8.2 observed-time layer, packet T8A.S08: an Itô integral for the shifted filtration is one for the original filtration

`p4r_shiftFil F t = F (max t 0)`.  Every simple integrand has nonnegative partition points, so its `ℱ`-measurability
and its `shiftFil ℱ`-measurability agree, and it is the same integrand for both filtrations.  The approximation
property transfers verbatim, and `M` vanishes for `t ≤ 0`, so it is adapted to `F` as well.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- the same elementary integrand, viewed in the shifted filtration -/
def r26t8a_s08_toShift (ℱ : Filtration ℝ mΩ) (Ψ : SimpleIntegrand ℱ ι) :
    SimpleIntegrand (HRS.MP.SelfSimP4Impl.p4r_shiftFil ℱ) ι where
  n := Ψ.n
  t := Ψ.t
  mono := Ψ.mono
  nonneg := Ψ.nonneg
  ξ := Ψ.ξ
  meas := fun i => by
    have h0 : 0 ≤ Ψ.t i.castSucc := Ψ.nonneg.trans (Ψ.mono (Fin.zero_le _))
    have h := Ψ.meas i
    rw [HRS.MP.SelfSimP4Impl.p4r_shiftFil_apply, max_eq_left h0]
    exact h
  bdd := Ψ.bdd

theorem r26t8a_ito_unshift (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Phi : ℝ → Ω → ι → ℝ) (M : ℝ → Ω → ℝ)
    (hM : IsItoIntegral P (HRS.MP.SelfSimP4Impl.p4r_shiftFil F) W Phi M) :
    IsItoIntegral P F W Phi M := by
  refine ⟨hM.cont, ?_, hM.zero, ?_⟩
  · intro t
    by_cases ht : 0 ≤ t
    · have h := hM.adapted t
      rw [HRS.MP.SelfSimP4Impl.p4r_shiftFil_apply, max_eq_left ht] at h
      exact h
    · have hz : M t = 0 := funext fun w => hM.zero t (not_le.1 ht).le w
      rw [hz]
      exact measurable_const
  · intro t ht Ψ hΨ
    exact hM.approx t ht (fun n => r26t8a_s08_toShift F (Ψ n)) hΨ

end HRS.MS.R26T8A

end
