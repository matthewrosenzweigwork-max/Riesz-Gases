import HRS.MS.R26T6CI06Bound
import HRS.MS.S111X2Aux4

/-!
# S11.1 I06: screened response is invariant under a.e. changes of its datum

The uniqueness theorem for the native L2 response is applied to the very
same solution after transporting equality of the centered forcing.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.S111X2
variable {d : ℕ}

theorem r26t6c_response_congr (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg : ℝ)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (f f' : Euc d → ℝ) (hf : MemLp f 2 mu)
    (hf' : MemLp f' 2 mu) (hae : f =ᵐ[mu] f') :
    HRS.Whole.responseInverse g mu gamma f =ᵐ[mu]
      HRS.Whole.responseInverse g mu gamma f' := by
  have hmean : HRS.Whole.pair mu f = HRS.Whole.pair mu f' := by
    exact integral_congr_ae hae
  have hP : HRS.Whole.projMean mu f =ᵐ[mu]
      HRS.Whole.projMean mu f' := by
    filter_upwards [hae] with x hx
    simp [HRS.Whole.projMean, hmean, hx]
  have hsolf : HRS.Whole.IsResponse g mu gamma f
      (HRS.Whole.responseInverse g mu gamma f) :=
    (s111x2_responseForm hK hgamma (le_refl gamma)).solution f hf
  have hsol' : HRS.Whole.IsResponse g mu gamma f'
      (HRS.Whole.responseInverse g mu gamma f) :=
    ⟨hsolf.1, by
      filter_upwards [hsolf.2, hP] with x h1 h2
      exact h1.trans h2⟩
  exact (s111x2_resp_unique hK hgamma hf' hsol').trans
    (s111x2_responseInverse_ae hK hgamma hf').symm

end HRS.MS.R26T6C
