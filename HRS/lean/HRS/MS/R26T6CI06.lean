import HRS.MS.R26T6CI06LinearMap

/-!
# S11.1 R26-T6C.I06: actual bounded linear response on L3

The response is constructed on Lp equivalence classes and its norm is
bounded by the constant in the frozen packet, including gamma=0.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.S111X2
variable {d : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem r26t6c_response_L3_CLM (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg C : ℝ) (hC : 0 ≤ C)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (h23 : ∀ f : Euc d → ℝ, MemLp f 2 mu →
      MemLp (HRS.Whole.Kop g mu f) 3 mu ∧
      eLpNorm (HRS.Whole.Kop g mu f) 3 mu ≤
        ENNReal.ofReal C * eLpNorm f 2 mu)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    ∃ R : Lp ℝ 3 mu →L[ℝ] Lp ℝ 3 mu,
      ‖R‖ ≤ 2 * (1 + gamma * C) ∧
      ∀ f : Euc d → ℝ, ∀ hf : MemLp f 3 mu,
        (R (hf.toLp f) : Euc d → ℝ) =ᵐ[mu]
          HRS.Whole.responseInverse g mu gamma f := by
  obtain ⟨Rlin, hRlin⟩ :=
    r26t6c_response_L3_linear_map mu g K Mg C hC hK h23 gamma hgamma
  have hbound : ∀ F : Lp ℝ 3 mu,
      ‖Rlin F‖ ≤ 2 * (1 + gamma * C) * ‖F‖ := by
    intro F
    have hae : (Rlin F : Euc d → ℝ) =ᵐ[mu]
        HRS.Whole.responseInverse g mu gamma (F : Euc d → ℝ) := by
      simpa only [Lp.toLp_coeFn] using hRlin (F : Euc d → ℝ) (Lp.memLp F)
    have hnorm : ‖Rlin F‖ = lpNorm (Rlin F : Euc d → ℝ) 3 mu := by
      rw [Lp.norm_def]
      rfl
    have hnormF : ‖F‖ = lpNorm (F : Euc d → ℝ) 3 mu := by
      rw [Lp.norm_def]
      rfl
    rw [hnorm, hnormF]
    have hcongr : lpNorm (Rlin F : Euc d → ℝ) 3 mu =
        lpNorm (HRS.Whole.responseInverse g mu gamma (F : Euc d → ℝ)) 3 mu :=
      congrArg ENNReal.toReal (eLpNorm_congr_ae hae)
    rw [hcongr]
    exact r26t6c_response_L3_norm_bound mu g K Mg C hC hK h23
      gamma hgamma (F : Euc d → ℝ) (Lp.memLp F)
  have hB : 0 ≤ 2 * (1 + gamma * C) := by positivity
  let R : Lp ℝ 3 mu →L[ℝ] Lp ℝ 3 mu :=
    Rlin.mkContinuous (2 * (1 + gamma * C)) hbound
  refine ⟨R, LinearMap.mkContinuous_norm_le Rlin hB hbound, ?_⟩
  intro f hf
  exact hRlin f hf

end HRS.MS.R26T6C
