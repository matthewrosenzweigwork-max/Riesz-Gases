import HRS.MS.SA16TEn1

/-!
# S.A.16 (SA16T) En2: the energy bound for the Duhamel solution with coefficient bounds on the derivatives of order `>= 1` only

`sa16t_gen_energy`, `sa16t_energy_solution`: `sa16sz_gen_energy`, `sa16sz_energy_solution` with the constant
`p (cTr(B) + C_J CG)` depending on the uniform bound `B` of `‖D^i bc‖` (`1 <= i <= m+1`) and not on the sup bound `Bn` of `SA16BddCoef`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section En2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1000000 in
theorem sa16t_gen_energy (m : ℕ) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ {ν B Bn CG : ℝ}, 0 ≤ ν → ∀ {bc : Fin d → Euc d → ℝ}, SA16BddCoef (m + 1) Bn bc → 0 ≤ B →
      (∀ l, ∀ i, 1 ≤ i → i ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ i (bc l) x‖ ≤ B) →
      ∀ (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p), ‖T0‖ ≤ CG → ∀ G : WmpSpace d (m + 1 + 1) p,
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) -
            T0 (sa16sz_iota2 d m p G)) ≤
          (p * sa16sz_cTr d m p B + p * CJ * CG) * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨hN, ⟨CJ, hCJ0, hCJ⟩, hpow, -⟩ := closed_jet_energy_calculus d m p
  refine ⟨CJ, hCJ0, fun {ν B Bn CG} hν {bc} hb hB0 hbb T0 hT0 G => ?_⟩
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
      have := sa16t_transport (p := p) m hb hB0 hbb φ
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


set_option maxHeartbeats 1600000 in
/-- **Energy bound for the Duhamel solution** (packet P7, sub case). -/
theorem sa16t_energy_solution (m : ℕ) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ {ν T B Bn Bk CG : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) Bn (bc r)) (hB0 : 0 ≤ B)
    (hbb : ∀ r ∈ Icc (0 : ℝ) T, ∀ l, ∀ i, 1 ≤ i → i ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ i (bc r l) x‖ ≤ B)
    (T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ r ∈ Icc (0 : ℝ) T, (sa16r_iota d m p).comp (T1 r) = (T0 r).comp (sa16r_iota d m p))
    (hT0 : ∀ r ∈ Icc (0 : ℝ) T, ‖T0 r‖ ≤ CG)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - (T1 r).comp (sa16r_iota d (m + 1) p))
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk) (hBk : 0 ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ),
    ∀ τ ∈ Icc (0 : ℝ) T,
      jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
        jetEnergy d m p (sa16sz_iota2 d m p φ) *
          Real.exp ((p * sa16sz_cTr d m p B + p * CJ * CG) * τ) := by
  obtain ⟨CJ, hCJ0, hgen⟩ := sa16t_gen_energy (d := d) (p := p) m
  refine ⟨CJ, hCJ0, ?_⟩
  intro ν T B Bn Bk CG hν hT bc hbc hB0 hbb T1 T0 hcomp hT0 K hK hKb hBk hKc φ u hu hsol
  set c : ℝ := p * sa16sz_cTr d m p B + p * CJ * CG with hc
  set e : ℝ → ℝ := fun τ => jetEnergy d m p (sa16sz_iota2 d m p (u τ)) with he
  have hcont : ContinuousOn e (Icc 0 T) :=
    (sa16sz_jetEnergy_cont m).comp_continuousOn ((sa16sz_iota2 d m p).continuous.comp_continuousOn hu)
  have hderiv : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧ e' ≤ c * e τ := by
    intro τ hτ
    have hτI : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
    have hdu := sa16sx_hasDerivAt hν hT K hKb hBk hKc φ hu hsol hτ
    have hE := (sa16v2_jetEnergy_hasFDerivAt d m p (sa16sz_iota2 d m p (u τ))).comp_hasDerivAt τ hdu
    refine ⟨sa16v2_Dj d m p (sa16r_iota d m p (sa16r_iota d (m + 1) p (u τ))) (sa16sx_f m ν K u τ), hE, ?_⟩
    have hf : sa16sx_f m ν K u τ = ν • sa16so_Lap d m p (u τ) +
        sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) - T0 τ (sa16sz_iota2 d m p (u τ)) := by
      unfold sa16sx_f
      rw [hK τ]
      have h1 := congrArg (fun L => L (sa16r_iota d (m + 1) p (u τ))) (hcomp τ hτI)
      simp only [ContinuousLinearMap.comp_apply] at h1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub, h1]
      unfold sa16sz_iota2
      simp only [ContinuousLinearMap.comp_apply]
      abel
    have hder : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p (u τ)) =
        sa16v2_Dj d m p (sa16sz_iota2 d m p (u τ)) :=
      (sa16v2_jetEnergy_hasFDerivAt d m p _).fderiv
    have := hgen hν.le (hbc τ hτI) hB0 (hbb τ hτI) (T0 τ) (hT0 τ hτI) (u τ)
    rw [hder, ← hf] at this
    exact this
  have hmain := sa16sz_gronwall hcont hderiv
  have h0 : e 0 = jetEnergy d m p (sa16sz_iota2 d m p φ) := by
    have := sa16sx_strong hν hT K hKb hBk hKc φ hu hsol 0 ⟨le_rfl, hT.le⟩
    simp only [he, intervalIntegral.integral_same, add_zero] at this ⊢
    unfold sa16sz_iota2
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
  intro τ hτ
  have := hmain τ hτ
  rw [h0] at this
  exact this

end En2

end HRS.Whole.AppendixA.Phase2SA16R
