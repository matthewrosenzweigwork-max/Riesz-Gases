import HRS.MS.S111X2Aux3
import HRS.MS.R26T6CI04

/-!
# S11.1 R26-T6C.I05: L3 stability of the screened response

The native L2 resolvent contraction and an L2-to-L3 kernel estimate
imply the response is in L3, with the exact source coefficient.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.S111X2
variable {d : ℕ}

theorem r26t6c_response_L3 (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg C : ℝ) (hC : 0 ≤ C)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (h23 : ∀ f : Euc d → ℝ, MemLp f 2 mu →
      MemLp (HRS.Whole.Kop g mu f) 3 mu ∧
      eLpNorm (HRS.Whole.Kop g mu f) 3 mu ≤
        ENNReal.ofReal C * eLpNorm f 2 mu)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (f : Euc d → ℝ)
    (hf : MemLp f 3 mu) :
    MemLp (HRS.Whole.responseInverse g mu gamma f) 3 mu ∧
    eLpNorm (HRS.Whole.responseInverse g mu gamma f) 3 mu ≤
      ENNReal.ofReal (1 + gamma * C) *
        eLpNorm (HRS.Whole.projMean mu f) 3 mu := by
  letI : IsProbabilityMeasure mu := inferInstance
  have hf2 : MemLp f 2 mu := hf.mono_exponent (by norm_num)
  have hc2 : MemLp (HRS.Whole.projMean mu f) 2 mu :=
    (s111x2_memL2Zero_projMean hf2).1
  have hc3 := r26t6c_centered_L3 mu f hf
  let H : Lp ℝ 2 mu := s111x2_Res hK.posOp hgamma (s111x2_cl hf2)
  have hRae : HRS.Whole.responseInverse g mu gamma f =ᵐ[mu]
      (H : Euc d → ℝ) := s111x2_responseInverse_ae hK hgamma hf2
  have hR2 : MemLp (HRS.Whole.responseInverse g mu gamma f) 2 mu :=
    (memLp_congr_ae hRae).2 (Lp.memLp H)
  have hR2bound : eLpNorm (HRS.Whole.responseInverse g mu gamma f) 2 mu ≤
      eLpNorm (HRS.Whole.projMean mu f) 2 mu := by
    have hb := (s111x2_Res_bounds hK.posOp hgamma (s111x2_cl hf2)).2.2
    have hbe : ‖H‖ₑ ≤ ‖s111x2_cl hf2‖ₑ := by
      simpa only [enorm_le_iff_norm_le] using hb
    rw [eLpNorm_congr_ae hRae, ← Lp.enorm_def,
      eLpNorm_congr_ae (s111x2_cl_ae hf2), ← Lp.enorm_def]
    exact hbe
  have hc23 : eLpNorm (HRS.Whole.projMean mu f) 2 mu ≤
      eLpNorm (HRS.Whole.projMean mu f) 3 mu :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hK3 := h23 (HRS.Whole.responseInverse g mu gamma f) hR2
  have hsol : HRS.Whole.IsResponse g mu gamma f
      (HRS.Whole.responseInverse g mu gamma f) := by
    have hex : ∃ u, HRS.Whole.IsResponse g mu gamma f u :=
      ⟨_, s111x2_resp_exists hK hgamma hf2⟩
    unfold HRS.Whole.responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  let R : Euc d → ℝ := HRS.Whole.responseInverse g mu gamma f
  let P : Euc d → ℝ := HRS.Whole.projMean mu f
  let T : Euc d → ℝ := HRS.Whole.Kop g mu R
  have hEq : R =ᵐ[mu] (fun x => P x - gamma * T x) := by
    filter_upwards [hsol.2] with x hx
    dsimp [R, P, T] at hx ⊢
    linarith
  have hR3 : MemLp R 3 mu := by
    have hm : MemLp (fun x => P x - gamma * T x) 3 mu :=
      hc3.1.sub (hK3.1.const_mul gamma)
    exact (memLp_congr_ae hEq).2 hm
  refine ⟨hR3, ?_⟩
  have hTbound : eLpNorm T 3 mu ≤
      ENNReal.ofReal C * eLpNorm P 3 mu := by
    calc
      _ ≤ ENNReal.ofReal C * eLpNorm R 2 mu := hK3.2
      _ ≤ ENNReal.ofReal C * eLpNorm P 2 mu :=
        mul_le_mul' le_rfl hR2bound
      _ ≤ ENNReal.ofReal C * eLpNorm P 3 mu :=
        mul_le_mul' le_rfl hc23
  have htriangle := eLpNorm_sub_le (f := P)
    (g := fun x => gamma * T x) (μ := mu)
    (show (1 : ℝ≥0∞) ≤ 3 by norm_num)
  have hscale : eLpNorm (fun x => gamma * T x) 3 mu =
      ENNReal.ofReal gamma * eLpNorm T 3 mu := by
    calc
      _ = eLpNorm (gamma • T) 3 mu := by rfl
      _ = ‖gamma‖ₑ * eLpNorm T 3 mu := eLpNorm_const_smul gamma T 3 mu
      _ = _ := by rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hgamma]
  calc
    eLpNorm R 3 mu = eLpNorm (fun x => P x - gamma * T x) 3 mu :=
      eLpNorm_congr_ae hEq
    _ ≤ eLpNorm P 3 mu + eLpNorm (fun x => gamma * T x) 3 mu := by
      change eLpNorm (P - fun x => gamma * T x) 3 mu ≤ _
      exact htriangle
    _ = eLpNorm P 3 mu + ENNReal.ofReal gamma * eLpNorm T 3 mu := by rw [hscale]
    _ ≤ eLpNorm P 3 mu + ENNReal.ofReal gamma *
        (ENNReal.ofReal C * eLpNorm P 3 mu) :=
      add_le_add_right (mul_le_mul' le_rfl hTbound) _
    _ = ENNReal.ofReal (1 + gamma * C) * eLpNorm P 3 mu := by
      calc
        _ = ((1 : ℝ≥0∞) + ENNReal.ofReal (gamma * C)) * eLpNorm P 3 mu := by
          rw [ENNReal.ofReal_mul hgamma]
          ring
        _ = _ := by
          congr 1
          simpa using (ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
            (mul_nonneg hgamma hC)).symm
end HRS.MS.R26T6C
