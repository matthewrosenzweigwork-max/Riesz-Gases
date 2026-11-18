import HRS.MS.SA16Y5Mm1
import HRS.MS.SA16Y3Diss1
import HRS.MS.SA16Y3Sk1

/-!
# S.A.16 (SA16Y5) Ds1: the dissipativity hypothesis `hN` for the order-one operator (`d-2 < s < d-1`, `M = -λ I`)

`sa16y5_diss`: let `N' : W^{m+2,p} →L W^{m+1,p}` satisfy `wrep (N' (Jcc φ)) = eucNonlocal s (-(λ•1)) μ φ` a.e. (`φ ∈ C_c^∞`; this is
the operator of `sa16y4io_G_exists` with `M = -λ I`) for a nonnegative `C_b^∞` density `μ` with `Cb 2 Λ`, `Dec (m+2) W`.
Then for EVERY `G ∈ W^{m+2,p}`: `d(jetEnergy_m)_{ι²G}(-ι N' G) ≤ p λ C jetEnergy_m(ι²G)`, `C = C(d,s,p,Λ,W,m)`.
This is hypothesis `hN` of `sa16y3_energy_solution_dissD` (`cNl = p λ C`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section Ds1
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1600000 in
theorem sa16y5_diss (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s < (d : ℝ) - 1)
    (hθ0 : 0 < s + 2 - d) (hfar : (d : ℝ) < p * (s + 1)) {Wd : ℝ} (hWd : 0 ≤ Wd) (Λ : ℝ) (hΛ : 0 ≤ Λ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → sa16z_Cb 2 Λ μ →
      sa16y5_Dec (m + 2) Wd μ → ∀ {lam : ℝ}, 0 ≤ lam →
      ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        (∀ φ : ccSub d, wrep d (m + 1) p (N' (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
          HRS.MH.AdjointRd.eucNonlocal s (-(lam • (1 : Matrix (Fin d) (Fin d) ℝ))) μ φ.1) →
        ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            p * lam * C * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨C, hC0, hC⟩ := sa16y5_iso_pairing hd hs0 hsd hs1 hθ0 hp2 hfar hWd Λ hΛ m
  refine ⟨C, hC0, fun {μ} hμ hpos hCb hdec {lam} hlam N' hN' G => ?_⟩
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have hder : fderiv ℝ (jetEnergy d m p) = sa16v2_Dj d m p :=
    funext fun G => (sa16v2_jetEnergy_hasFDerivAt d m p G).fderiv
  have hDc : Continuous (sa16v2_Dj d m p) := sa16v2_Dj_continuous d m p
  have hι2 := (sa16sz_iota2 d m p).continuous
  refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on G (isClosed_le ?_ ?_) (fun φ => ?_)
  · rw [hder]
    exact (hDc.comp hι2).clm_apply ((sa16r_iota d m p).continuous.comp N'.continuous).neg
  · exact continuous_const.mul ((sa16sz_jetEnergy_cont m).comp hι2)
  · -- the jets of `P_μ φ`
    have hφ := φ.2
    have hS : MemLp (sa16j_S d m (sa16z_P s μ φ.1)) (ENNReal.ofReal p) volume :=
      sa16y5_S_memLp hd hs0 hsd hs1 hp2 hfar hWd hμs hφ m (sa16y5_Dec_mono (by omega) hdec)
    have hmem : sa16z_P s μ φ.1 ∈ sa16r_S d m p := sa16r_mem_S m (sa16z_P_smooth hs0 hsd hμs hφ) hS
    set f0 : sa16r_S d m p := ⟨sa16z_P s μ φ.1, hmem⟩ with hf0
    have hJc := sa16r_J_coe (p := p) m (f := f0) hS
    -- `-ι N'(Jφ) = lam • J f0`
    have hH : -(sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ))) = lam • sa16r_J d m p f0 := by
      refine sa16r_wrep_inj d m p _ _ ?_
      have h1 := sa16r_wrep_smul d m p lam (sa16r_J d m p f0)
      have h2 := sa16r_J_spec d m p f0
      have h3 := sa16r_iota_wrep (p := p) m (N' (sa16r_Jcc d (m + 1 + 1) p φ))
      have h4 := hN' φ
      have h5 : wrep d m p (-(sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ)))) =ᵐ[volume]
          fun x => -wrep d m p (sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ))) x := by
        set Y := sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ)) with hY
        have ha := sa16r_wrep_add d m p Y (-Y)
        have hz := sa16r_wrep_zero d m p
        rw [add_neg_cancel] at ha
        filter_upwards [ha, hz] with x e1 e2
        rw [e2] at e1
        linarith
      filter_upwards [h1, h2, h3, h4, h5] with x e1 e2 e3 e4 e5
      rw [e5, e1, e2, e3, e4]
      have := sa16y3_eucNonlocal_split (s := s) lam 0 μ φ.1 x
      simp only [add_zero] at this
      rw [this]
      simp [sa16y3_PA, f0]
    rw [sa16sz_iota2_Jcc, hH, map_smul, sa16y3_fderiv_pair m φ (sa16r_J d m p f0) hJc, sa16sz_energy_cc]
    have h1 := hC hμ hpos hφ hCb hdec
    simp only [smul_eq_mul]
    calc lam * (p * ∫ x, sa16sz_dens m p φ.1 (sa16z_P s μ φ.1) x)
        = (p * lam) * ∫ x, sa16sz_dens m p φ.1 (sa16z_P s μ φ.1) x := by ring
      _ ≤ (p * lam) * (C * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ.1 k x ^ p) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hp0.le hlam)
      _ = _ := by ring

end Ds1

end HRS.Whole.AppendixA.Phase2SA16R
