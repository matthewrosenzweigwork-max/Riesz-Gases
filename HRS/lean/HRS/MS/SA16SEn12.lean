import HRS.MS.SA16SEn11

/-!
# S.A.16 (SA16S) En12: the energy inequality of the generator on `W^{m+2,p}` (packet P7, step 13)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section En12
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16sz_rpow_pred_mul {a p : ℝ} (ha : 0 ≤ a) (hp : 1 < p) : a ^ (p - 1) * a = a ^ p := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · rw [← h0, Real.zero_rpow (by linarith : p ≠ 0)]; simp
  · rw [← Real.rpow_add_one hpos.ne']; congr 1; ring

lemma sa16sz_jetEnergy_cont (k : ℕ) : Continuous (jetEnergy d k p) :=
  continuous_iff_continuousAt.2 fun G => (sa16v2_jetEnergy_hasFDerivAt d k p G).continuousAt

set_option maxHeartbeats 1000000 in
theorem sa16sz_gen_energy (m : ℕ) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ {ν B CG : ℝ}, 0 ≤ ν → ∀ {bc : Fin d → Euc d → ℝ}, SA16BddCoef (m + 1) B bc →
      ∀ (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p), ‖T0‖ ≤ CG → ∀ G : WmpSpace d (m + 1 + 1) p,
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) -
            T0 (sa16sz_iota2 d m p G)) ≤
          (p * sa16sz_cTr d m p B + p * CJ * CG) * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨hN, ⟨CJ, hCJ0, hCJ⟩, hpow, -⟩ := closed_jet_energy_calculus d m p
  refine ⟨CJ, hCJ0, fun {ν B CG} hν {bc} hb T0 hT0 G => ?_⟩
  have hCG : 0 ≤ CG := (norm_nonneg T0).trans hT0
  have hder : fderiv ℝ (jetEnergy d m p) = sa16v2_Dj d m p :=
    funext fun G => (sa16v2_jetEnergy_hasFDerivAt d m p G).fderiv
  have hDc : Continuous (sa16v2_Dj d m p) := sa16v2_Dj_continuous d m p
  have hι2 := (sa16sz_iota2 d m p).continuous
  -- the diffusion term
  have hD : ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (sa16so_Lap d m p G) ≤ 0 := by
    intro G
    refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on G (isClosed_le ?_ continuous_const) (fun φ => ?_)
    · rw [hder]
      exact (hDc.comp hι2).clm_apply (sa16so_Lap d m p).continuous
    · rw [sa16sz_iota2_Jcc, sa16sz_Lap_Jcc, sa16sz_fderiv_cc]
      exact mul_nonpos_of_nonneg_of_nonpos hp0.le (sa16sz_diffusion m φ)
  -- the transport term
  have hT : ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (sa16r_iota d m p (sa16so_B d (m + 1) p bc G)) ≤
        p * sa16sz_cTr d m p B * jetEnergy d m p (sa16sz_iota2 d m p G) := by
    intro G
    refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on G (isClosed_le ?_ ?_) (fun φ => ?_)
    · rw [hder]
      exact (hDc.comp hι2).clm_apply ((sa16r_iota d m p).continuous.comp (sa16so_B d (m + 1) p bc).continuous)
    · exact continuous_const.mul ((sa16sz_jetEnergy_cont m).comp hι2)
    · rw [sa16sz_iota2_Jcc, sa16sz_B_Jcc m hb, sa16sz_fderiv_cc, sa16sz_energy_cc]
      have := sa16sz_transport (p := p) m hb φ
      calc p * ∫ x, sa16sz_dens m p φ.1 (sa16so_transportFun bc φ.1) x
          ≤ p * (sa16sz_cTr d m p B * ∑ j : Fin (m + 1), ∫ x, sa16sz_vn φ.1 j x ^ p) :=
            mul_le_mul_of_nonneg_left this hp0.le
        _ = _ := by ring
  -- the nonlocal term
  have hNl : ∀ G' : WmpSpace d m p, fderiv ℝ (jetEnergy d m p) G' (-(T0 G')) ≤ p * CJ * CG * jetEnergy d m p G' := by
    intro G'
    refine (sa16sz_fderiv_le m G' (-(T0 G'))).trans ?_
    set a := jetNorm d m p G' with ha
    have ha0 : 0 ≤ a := hN.nonneg G'
    have hneg : jetNorm d m p (-(T0 G')) = jetNorm d m p (T0 G') := by
      have := hN.smul (-1 : ℝ) (T0 G')
      rw [neg_one_smul ℝ] at this
      rw [this]; simp
    rw [hneg]
    have h1 : jetNorm d m p (T0 G') ≤ CJ * (CG * a) := by
      refine (hCJ _).2.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCJ0.le
      calc ‖T0 G'‖ ≤ ‖T0‖ * ‖G'‖ := T0.le_opNorm G'
        _ ≤ CG * a := mul_le_mul hT0 (hCJ G').1 (norm_nonneg _) hCG
    have h2 : p * a ^ (p - 1) * jetNorm d m p (T0 G') ≤ p * a ^ (p - 1) * (CJ * (CG * a)) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hp0.le (Real.rpow_nonneg ha0 _))
    have h3 : p * a ^ (p - 1) * (CJ * (CG * a)) = p * CJ * CG * a ^ p := by
      rw [← sa16sz_rpow_pred_mul ha0 (by linarith : 1 < p)]; ring
    rw [← hpow G']
    linarith
  -- assemble
  have hlin : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
      (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) - T0 (sa16sz_iota2 d m p G)) =
      ν * fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (sa16so_Lap d m p G) +
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (sa16r_iota d m p (sa16so_B d (m + 1) p bc G)) +
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(T0 (sa16sz_iota2 d m p G))) := by
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
      ContinuousLinearMap.map_neg, smul_eq_mul, sub_eq_add_neg]
  rw [hlin]
  have h1 := mul_nonpos_of_nonneg_of_nonpos hν (hD G)
  have h2 := hT G
  have h3 := hNl (sa16sz_iota2 d m p G)
  have h4 : (p * sa16sz_cTr d m p B + p * CJ * CG) * jetEnergy d m p (sa16sz_iota2 d m p G) =
      p * sa16sz_cTr d m p B * jetEnergy d m p (sa16sz_iota2 d m p G) +
        p * CJ * CG * jetEnergy d m p (sa16sz_iota2 d m p G) := by ring
  rw [h4]
  linarith

end En12

end HRS.Whole.AppendixA.Phase2SA16R
