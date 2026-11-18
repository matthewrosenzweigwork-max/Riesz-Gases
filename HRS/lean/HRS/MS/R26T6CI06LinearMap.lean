import HRS.MS.R26T6CI06LinearAE

/-!
# S11.1 I06: the response descends linearly to L3 equivalence classes.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.S111X2
variable {d : ℕ}

theorem r26t6c_response_L3_linear_map (mu : Measure (Euc d))
    [IsProbabilityMeasure mu] (g : Euc d → ℝ)
    (K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) (Mg C : ℝ) (hC : 0 ≤ C)
    (hK : HRS.MS.S111X2.KRep g mu K Mg)
    (h23 : ∀ f : Euc d → ℝ, MemLp f 2 mu →
      MemLp (HRS.Whole.Kop g mu f) 3 mu ∧
      eLpNorm (HRS.Whole.Kop g mu f) 3 mu ≤
        ENNReal.ofReal C * eLpNorm f 2 mu)
    (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    ∃ R : Lp ℝ 3 mu →ₗ[ℝ] Lp ℝ 3 mu,
      ∀ f : Euc d → ℝ, ∀ hf : MemLp f 3 mu,
        (R (hf.toLp f) : Euc d → ℝ) =ᵐ[mu]
          HRS.Whole.responseInverse g mu gamma f := by
  let S : Lp ℝ 3 mu → Lp ℝ 3 mu := fun F =>
    ((r26t6c_response_L3 mu g K Mg C hC hK h23 gamma hgamma
      (F : Euc d → ℝ) (Lp.memLp F)).1).toLp
      (HRS.Whole.responseInverse g mu gamma (F : Euc d → ℝ))
  have hS (F : Lp ℝ 3 mu) :
      (S F : Euc d → ℝ) =ᵐ[mu]
        HRS.Whole.responseInverse g mu gamma (F : Euc d → ℝ) :=
    MemLp.coeFn_toLp _
  have hAdd : ∀ F G : Lp ℝ 3 mu, S (F + G) = S F + S G := by
    intro F G
    have hF2 : MemLp (F : Euc d → ℝ) 2 mu :=
      (Lp.memLp F).mono_exponent (by norm_num)
    have hG2 : MemLp (G : Euc d → ℝ) 2 mu :=
      (Lp.memLp G).mono_exponent (by norm_num)
    have hFG2 : MemLp (fun x : Euc d => F x + G x) 2 mu := hF2.add hG2
    have hL : HRS.Whole.responseInverse g mu gamma (F + G : Lp ℝ 3 mu) =ᵐ[mu]
        HRS.Whole.responseInverse g mu gamma (fun x => F x + G x) :=
      r26t6c_response_congr mu g K Mg hK gamma hgamma _ _
        ((Lp.memLp (F + G)).mono_exponent (by norm_num)) hFG2
        (Lp.coeFn_add F G)
    have hR : HRS.Whole.responseInverse g mu gamma
        (fun x : Euc d => F x + G x) =ᵐ[mu]
        (fun x => HRS.Whole.responseInverse g mu gamma (F : Euc d → ℝ) x +
          HRS.Whole.responseInverse g mu gamma (G : Euc d → ℝ) x) := by
      have h := r26t6c_response_linear_ae mu g K Mg hK gamma hgamma
        (F : Euc d → ℝ) (G : Euc d → ℝ) hF2 hG2 1
      have heq : (fun x : Euc d => F x + G x) =
          ((F : Euc d → ℝ) + (1 : ℝ) • (G : Euc d → ℝ)) := by
        funext x
        simp [Pi.add_apply, Pi.smul_apply]
      rw [heq]
      simpa [one_smul, Pi.add_apply] using h
    apply Lp.ext
    filter_upwards [hS (F + G), hL, hR, (hS F).symm, (hS G).symm,
      Lp.coeFn_add (S F) (S G)] with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5]
    simpa only [Pi.add_apply] using h6.symm
  have hSmul : ∀ (c : ℝ) (F : Lp ℝ 3 mu), S (c • F) = c • S F := by
    intro c F
    have hF2 : MemLp (F : Euc d → ℝ) 2 mu :=
      (Lp.memLp F).mono_exponent (by norm_num)
    have hcf2 : MemLp (c • (F : Euc d → ℝ)) 2 mu := hF2.const_smul c
    have hL := r26t6c_response_congr mu g K Mg hK gamma hgamma
      (c • F : Lp ℝ 3 mu) (c • (F : Euc d → ℝ))
      ((Lp.memLp (c • F)).mono_exponent (by norm_num)) hcf2
      (Lp.coeFn_smul c F)
    have hR := r26t6c_response_smul_ae mu g K Mg hK gamma hgamma
      (F : Euc d → ℝ) hF2 c
    apply Lp.ext
    filter_upwards [hS (c • F), hL, hR, (hS F).symm,
      Lp.coeFn_smul c (S F)] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4]
    simpa only [Pi.smul_apply, smul_eq_mul] using h5.symm
  let R : Lp ℝ 3 mu →ₗ[ℝ] Lp ℝ 3 mu :=
    { toFun := S, map_add' := hAdd, map_smul' := hSmul }
  refine ⟨R, ?_⟩
  intro f hf
  have hfcoe : (hf.toLp f : Euc d → ℝ) =ᵐ[mu] f :=
    MemLp.coeFn_toLp hf
  have hf2 := hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  exact (hS (hf.toLp f)).trans
    (r26t6c_response_congr mu g K Mg hK gamma hgamma
      (hf.toLp f) f
      ((Lp.memLp (hf.toLp f)).mono_exponent (by norm_num)) hf2 hfcoe)

end HRS.MS.R26T6C
