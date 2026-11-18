import HRS.MS.R26T6CI06Congr

/-! S11.1 I06: a.e. linearity and the zero response on its native L2 domain. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.S111X2
variable {d : ℕ}

theorem r26t6c_response_zero (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg : ℝ)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    HRS.Whole.responseInverse g mu gamma (fun _ => 0) =ᵐ[mu]
      (fun _ => 0) := by
  have hzero : HRS.Whole.IsResponse g mu gamma
      (fun _ => 0) (fun _ => 0) := by
    refine ⟨⟨MemLp.zero, by simp⟩, ae_of_all _ fun x => ?_⟩
    simp [HRS.Whole.Kop, HRS.Whole.projMean, HRS.Whole.pair]
  have huniq := s111x2_resp_unique hK hgamma
    (show MemLp (fun _ : Euc d => (0 : ℝ)) 2 mu from MemLp.zero) hzero
  exact ((s111x2_responseInverse_ae hK hgamma
      (show MemLp (fun _ : Euc d => (0 : ℝ)) 2 mu from MemLp.zero)).trans
      huniq.symm).trans (ae_eq_refl _)

theorem r26t6c_response_linear_ae (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg : ℝ)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (f h : Euc d → ℝ) (hf : MemLp f 2 mu) (hh : MemLp h 2 mu)
    (c : ℝ) :
    HRS.Whole.responseInverse g mu gamma (f + c • h) =ᵐ[mu]
      (fun x => HRS.Whole.responseInverse g mu gamma f x +
        c * HRS.Whole.responseInverse g mu gamma h x) := by
  have hl := (s111x2_responseForm hK hgamma (le_refl gamma)).linear
      f h hf hh c
  filter_upwards [hl] with x hx
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx

theorem r26t6c_response_smul_ae (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg : ℝ)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (f : Euc d → ℝ) (hf : MemLp f 2 mu) (c : ℝ) :
    HRS.Whole.responseInverse g mu gamma (c • f) =ᵐ[mu]
      (fun x => c * HRS.Whole.responseInverse g mu gamma f x) := by
  have hl := r26t6c_response_linear_ae mu g K Mg hK gamma hgamma
    (fun _ => 0) f MemLp.zero hf c
  have hz := r26t6c_response_zero mu g K Mg hK gamma hgamma
  filter_upwards [hl, hz] with x hx hz0
  have heq : (fun _ : Euc d => (0 : ℝ)) + c • f = c • f := by
    funext y
    simp [Pi.add_apply, Pi.smul_apply]
  rw [heq] at hx
  simpa [Pi.smul_apply, smul_eq_mul, hz0] using hx

end HRS.MS.R26T6C
