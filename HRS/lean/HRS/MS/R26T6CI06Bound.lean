import HRS.MS.R26T6CI05

/-!
# S11.1 I06: norm estimate underlying the L3 continuous linear response
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_response_L3_norm_bound (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg C : ℝ) (hC : 0 ≤ C)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (h23 : ∀ f : Euc d → ℝ, MemLp f 2 mu →
      MemLp (HRS.Whole.Kop g mu f) 3 mu ∧
      eLpNorm (HRS.Whole.Kop g mu f) 3 mu ≤
        ENNReal.ofReal C * eLpNorm f 2 mu)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (f : Euc d → ℝ)
    (hf : MemLp f 3 mu) :
    lpNorm (HRS.Whole.responseInverse g mu gamma f) 3 mu ≤
      2 * (1 + gamma * C) * lpNorm f 3 mu := by
  have hR := r26t6c_response_L3 mu g K Mg C hC hK h23 gamma hgamma f hf
  have hP := r26t6c_centered_L3 mu f hf
  have hA : 0 ≤ 1 + gamma * C := by positivity
  have hEN : eLpNorm (HRS.Whole.responseInverse g mu gamma f) 3 mu ≤
      ENNReal.ofReal (2 * (1 + gamma * C)) * eLpNorm f 3 mu := by
    calc
      _ ≤ ENNReal.ofReal (1 + gamma * C) *
        eLpNorm (HRS.Whole.projMean mu f) 3 mu := hR.2
      _ ≤ ENNReal.ofReal (1 + gamma * C) *
        (2 * eLpNorm f 3 mu) := mul_le_mul' le_rfl hP.2
      _ = ENNReal.ofReal (2 * (1 + gamma * C)) * eLpNorm f 3 mu := by
        have hx : (2 : ℝ≥0∞) * ENNReal.ofReal (1 + gamma * C) =
            ENNReal.ofReal (2 * (1 + gamma * C)) := by
          calc
            _ = ENNReal.ofReal 2 * ENNReal.ofReal (1 + gamma * C) := by norm_num
            _ = _ := (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
        calc
          _ = (2 * ENNReal.ofReal (1 + gamma * C)) * eLpNorm f 3 mu := by ac_rfl
          _ = _ := by rw [hx]
  have hfFin : eLpNorm f 3 mu ≠ ⊤ := hf.eLpNorm_ne_top
  have htop : ENNReal.ofReal (2 * (1 + gamma * C)) * eLpNorm f 3 mu ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf).ne
  have hFinal := ENNReal.toReal_mono htop hEN
  simpa only [toReal_eLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA)] using hFinal

end HRS.MS.R26T6C
