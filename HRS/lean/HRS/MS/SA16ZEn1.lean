import HRS.MS.SA16SEn13

/-!
# S.A.16 (SA16Z) En1: the energy inequality with a dissipative nonlocal term (packet P7, iso / hilbert, step 1)

`sa16zz_gen_energy_diss`: for every map `N : W^{m+2,p} → W^{m,p}` (the nonlocal term `𝒢`) satisfying the dissipativity
`d(jetEnergy)_{ι²G}(-N G) ≤ cNl jetEnergy(ι²G)` (replacing `‖T0‖ ≤ CG`), the generator
`ν Δ + b·∇ - N` satisfies `d(jetEnergy)_{ι²G}(νΔG + ι(b·∇G) - N G) ≤ (p cTr + cNl) jetEnergy(ι²G)`.

`sa16zz_energy_strong`: for `u` continuous into `W^{m+2,p}` on `[0,T]` such that `ι² u` has the derivative
`νΔu + ι(b_τ·∇u) - N_τ u` on `(0,T)`: `jetEnergy(ι²u(τ)) ≤ jetEnergy(ι²u(0)) exp(cτ)`, `c = p cTr + cNl`.

`sa16zz_energy_solution`: the same for the mild solution of `sa16r_fixedn_mild` with `K_r = B_{b_r} - N'_r`,
`N'_r : W^{m+2,p} → W^{m+1,p}` bounded (shape of `sa16sz_energy_solution`, with the dissipativity hypothesis instead of the
operator bound).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section ZEn1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1000000 in
theorem sa16zz_gen_energy_diss (m : ℕ) {ν B cNl : ℝ} (hν : 0 ≤ ν) {bc : Fin d → Euc d → ℝ}
    (hb : SA16BddCoef (m + 1) B bc) (N : WmpSpace d (m + 1 + 1) p → WmpSpace d m p)
    (hN : ∀ G : WmpSpace d (m + 1 + 1) p, fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N G)) ≤
      cNl * jetEnergy d m p (sa16sz_iota2 d m p G)) (G : WmpSpace d (m + 1 + 1) p) :
    fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
        (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) - N G) ≤
      (p * sa16sz_cTr d m p B + cNl) * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
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
  have hlin : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
      (ν • sa16so_Lap d m p G + sa16r_iota d m p (sa16so_B d (m + 1) p bc G) - N G) =
      ν * fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (sa16so_Lap d m p G) +
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (sa16r_iota d m p (sa16so_B d (m + 1) p bc G)) +
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N G)) := by
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
      ContinuousLinearMap.map_neg, smul_eq_mul, sub_eq_add_neg]
  rw [hlin]
  have h1 := mul_nonpos_of_nonneg_of_nonpos hν (hD G)
  have h2 := hT G
  have h3 := hN G
  have h4 : (p * sa16sz_cTr d m p B + cNl) * jetEnergy d m p (sa16sz_iota2 d m p G) =
      p * sa16sz_cTr d m p B * jetEnergy d m p (sa16sz_iota2 d m p G) +
        cNl * jetEnergy d m p (sa16sz_iota2 d m p G) := by ring
  rw [h4]
  linarith

/-- **Energy bound for a strong solution** (shape: `ι² u` is differentiable on `(0,T)` with the stated derivative). -/
theorem sa16zz_energy_strong {m : ℕ} {ν T B cNl : ℝ} (hν : 0 ≤ ν)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Ioo (0 : ℝ) T, SA16BddCoef (m + 1) B (bc r))
    (N : ℝ → WmpSpace d (m + 1 + 1) p → WmpSpace d m p)
    (hN : ∀ r ∈ Ioo (0 : ℝ) T, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N r G)) ≤ cNl * jetEnergy d m p (sa16sz_iota2 d m p G))
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hder : ∀ τ ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r => sa16sz_iota2 d m p (u r))
      (ν • sa16so_Lap d m p (u τ) + sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) - N τ (u τ)) τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
      jetEnergy d m p (sa16sz_iota2 d m p (u 0)) * Real.exp ((p * sa16sz_cTr d m p B + cNl) * τ) := by
  set e : ℝ → ℝ := fun τ => jetEnergy d m p (sa16sz_iota2 d m p (u τ)) with he
  have hcont : ContinuousOn e (Icc 0 T) :=
    (sa16sz_jetEnergy_cont m).comp_continuousOn ((sa16sz_iota2 d m p).continuous.comp_continuousOn hu)
  have hderiv : ∀ τ ∈ Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧ e' ≤ (p * sa16sz_cTr d m p B + cNl) * e τ := by
    intro τ hτ
    have hE := (sa16v2_jetEnergy_hasFDerivAt d m p (sa16sz_iota2 d m p (u τ))).comp_hasDerivAt τ (hder τ hτ)
    refine ⟨_, hE, ?_⟩
    have hfd : fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p (u τ)) =
        sa16v2_Dj d m p (sa16sz_iota2 d m p (u τ)) :=
      (sa16v2_jetEnergy_hasFDerivAt d m p _).fderiv
    rw [← hfd]
    exact sa16zz_gen_energy_diss m hν (hbc τ hτ) (N τ) (hN τ hτ) (u τ)
  exact sa16sz_gronwall hcont hderiv

set_option maxHeartbeats 1600000 in
/-- **Energy bound for the Duhamel solution with a dissipative nonlocal term** (shape of `sa16sz_energy_solution`):
`K_r = B_{b_r} - N'_r`, `N'_r : W^{m+2,p} → W^{m+1,p}` bounded, `d(jetEnergy)_{ι²G}(-ι N'_r G) ≤ cNl jetEnergy(ι²G)`. -/
theorem sa16zz_energy_solution {m : ℕ} {ν T B Bk cNl : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B (bc r))
    (N' : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hN : ∀ r ∈ Icc (0 : ℝ) T, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' r G))) ≤
        cNl * jetEnergy d m p (sa16sz_iota2 d m p G))
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - N' r)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk) (hBk : 0 ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
      jetEnergy d m p (sa16sz_iota2 d m p φ) * Real.exp ((p * sa16sz_cTr d m p B + cNl) * τ) := by
  have hderiv : ∀ τ ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r => sa16sz_iota2 d m p (u r))
      (ν • sa16so_Lap d m p (u τ) + sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) -
        (fun r G => sa16r_iota d m p (N' r G)) τ (u τ)) τ := by
    intro τ hτ
    have hdu := sa16sx_hasDerivAt hν hT K hKb hBk hKc φ hu hsol hτ
    refine hdu.congr_deriv ?_
    unfold sa16sx_f
    rw [hK τ]
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  have := sa16zz_energy_strong (m := m) (ν := ν) (T := T) (B := B) (cNl := cNl) hν.le bc
    (fun r hr => hbc r ⟨hr.1.le, hr.2.le⟩) (fun r G => sa16r_iota d m p (N' r G))
    (fun r hr G => hN r ⟨hr.1.le, hr.2.le⟩ G) hu hderiv
  intro τ hτ
  have h0 := sa16sx_strong hν hT K hKb hBk hKc φ hu hsol 0 ⟨le_rfl, hT.le⟩
  have hu0 : sa16sz_iota2 d m p (u 0) = sa16sz_iota2 d m p φ := by
    simp only [intervalIntegral.integral_same, add_zero] at h0
    unfold sa16sz_iota2
    simp only [ContinuousLinearMap.comp_apply]
    exact h0
  have := this τ hτ
  rwa [hu0] at this

end ZEn1

end HRS.Whole.AppendixA.Phase2SA16R
