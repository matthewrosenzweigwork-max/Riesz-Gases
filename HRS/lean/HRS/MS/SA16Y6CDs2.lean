import HRS.MS.SA16Y6CHl1
import HRS.MS.SA16Y5Hl2
import HRS.MS.SA16Y6CDs1
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Ds2

/-! # SA16Y6 critical-case copy of SA16Y5Ds2 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section Ds2
variable {d : ℕ} {s p : ℝ} [Fact (2 ≤ p)]
set_option maxHeartbeats 3200000 in
theorem sa16y6c_diss_hilb (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1)
    (hθ0 : 0 < s + 2 - d) (hfar : (d : ℝ) < p * (s + 1)) {Wd : ℝ} (hWd : 0 ≤ Wd) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (m : ℕ) (AB : ℝ) (hAB : 0 ≤ AB) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb 2 Λ μ → sa16y5_Dec (m + 2) Wd μ → ∀ {lam : ℝ}, 0 ≤ lam →
      ∀ {A : Matrix (Fin d) (Fin d) ℝ}, (∀ i j, |A i j| ≤ AB) → A.transpose = -A →
      ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        (∀ φ : ccSub d, wrep d (m + 1) p (N' (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume]
          HRS.MH.AdjointRd.eucNonlocal s (-(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) μ φ.1) →
        ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            p * (lam * C1 + C2) * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨C1, hC10, hC1⟩ := sa16y6c_iso_pairing hd hs0 hsd hs1 hθ0 hp2 hfar hWd Λ hΛ m
  have hKj := sa16y6c_PA_bound hd hs0 hsd hs1 hp2 hfar hWd AB hAB
  choose Kj hKj0 hKj using hKj
  set Ks : ℝ := ∑ j ∈ Finset.range (m + 1), Kj j with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun j _ => hKj0 j
  have hKle : ∀ j ≤ m, Kj j ≤ Ks := fun j hj =>
    Finset.single_le_sum (f := Kj) (fun k _ => hKj0 k) (Finset.mem_range.2 (by omega))
  obtain ⟨C2, hC20, hC2⟩ := sa16y5_dens_le (d := d) hp2 m hKs0
  refine ⟨C1, C2, hC10, hC20, fun {μ} hμ hpos hCb hdec {lam} hlam {A} hA hskew N' hN' G => ?_⟩
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have hder : fderiv ℝ (jetEnergy d m p) = sa16v2_Dj d m p :=
    funext fun G => (sa16v2_jetEnergy_hasFDerivAt d m p G).fderiv
  have hDc : Continuous (sa16v2_Dj d m p) := sa16v2_Dj_continuous d m p
  have hι2 := (sa16sz_iota2 d m p).continuous
  refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on G (isClosed_le ?_ ?_) (fun φ => ?_)
  · rw [hder]
    exact (hDc.comp hι2).clm_apply ((sa16r_iota d m p).continuous.comp N'.continuous).neg
  · exact continuous_const.mul ((sa16sz_jetEnergy_cont m).comp hι2)
  · have hφ := φ.2
    -- jets of `P_μ φ` and `P^A_μ φ`
    have hS : MemLp (sa16j_S d m (sa16z_P s μ φ.1)) (ENNReal.ofReal p) volume :=
      sa16y6c_S_memLp hd hs0 hsd hs1 hp2 hfar hWd hμs hφ m (sa16y5_Dec_mono (by omega) hdec)
    have hmem : sa16z_P s μ φ.1 ∈ sa16r_S d m p := sa16r_mem_S m (sa16z_P_smooth hs0 hsd hμs hφ) hS
    set f0 : sa16r_S d m p := ⟨sa16z_P s μ φ.1, hmem⟩ with hf0
    have hJc := sa16r_J_coe (p := p) m (f := f0) hS
    have hPAs : ContDiff ℝ ∞ (sa16y3_PA s A μ φ.1) := sa16y3_PA_smooth hs0 hsd A hμs hφ
    have hPAb : ∀ j ≤ m, ∀ idx : Fin j → Fin d, eLpNorm (partialDeriv idx (sa16y3_PA s A μ φ.1))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal Ks * sa16z_S p φ.1 j := fun j hj idx =>
      (hKj j hA hskew hμs hφ (sa16y5_Dec_mono (by omega) hdec) idx).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (hKle j hj)) le_rfl)
    have hS1 : MemLp (sa16j_S d m (sa16y3_PA s A μ φ.1)) (ENNReal.ofReal p) volume := by
      have hg : MemLp (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d,
          ‖partialDeriv idx (sa16y3_PA s A μ φ.1) x‖) (ENNReal.ofReal p) volume := by
        refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun idx _ => ?_
        have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
        have hmm : MemLp (partialDeriv idx (sa16y3_PA s A μ φ.1)) (ENNReal.ofReal p) volume :=
          lt_of_le_of_lt (hPAb j hjm idx) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (sa16y3_S_lt_top hφ _))
        exact hmm.norm
      refine hg.mono' (sa16j_S_cont hPAs m).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d m _ x)]
      simpa [Real.norm_eq_abs] using sa16j_S_le m (sa16y3_PA s A μ φ.1) x
    have hmem1 : sa16y3_PA s A μ φ.1 ∈ sa16r_S d m p := sa16r_mem_S m hPAs hS1
    set f1 : sa16r_S d m p := ⟨sa16y3_PA s A μ φ.1, hmem1⟩ with hf1
    have hJc1 := sa16r_J_coe (p := p) m (f := f1) hS1
    -- `-ι N'(Jφ) = lam • J f0 - J f1`
    have hH : -(sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ))) = lam • sa16r_J d m p f0 - sa16r_J d m p f1 := by
      refine sa16r_wrep_inj d m p _ _ ?_
      have h1 := sa16r_wrep_smul d m p lam (sa16r_J d m p f0)
      have h2 := sa16r_J_spec d m p f0
      have h2' := sa16r_J_spec d m p f1
      have h3 := sa16r_iota_wrep (p := p) m (N' (sa16r_Jcc d (m + 1 + 1) p φ))
      have h4 := hN' φ
      have h6 := sa16so_wrep_sub (p := p) m (lam • sa16r_J d m p f0) (sa16r_J d m p f1)
      have h5 : wrep d m p (-(sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ)))) =ᵐ[volume]
          fun x => -wrep d m p (sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ))) x := by
        set Y := sa16r_iota d m p (N' (sa16r_Jcc d (m + 1 + 1) p φ)) with hY
        have ha := sa16r_wrep_add d m p Y (-Y)
        have hz := sa16r_wrep_zero d m p
        rw [add_neg_cancel] at ha
        filter_upwards [ha, hz] with x e1 e2
        rw [e2] at e1
        linarith
      filter_upwards [h1, h2, h2', h3, h4, h5, h6] with x e1 e2 e2' e3 e4 e5 e6
      rw [e5, e6, e1, e2, e2', e3, e4, sa16y3_eucNonlocal_split (s := s) lam A μ φ.1 x]
      simp [f0, f1]
      ring
    rw [sa16sz_iota2_Jcc, hH, map_sub, map_smul, sa16y3_fderiv_pair m φ (sa16r_J d m p f0) hJc,
      sa16y3_fderiv_pair m φ (sa16r_J d m p f1) hJc1, sa16sz_energy_cc]
    have h1 := hC1 hμ hpos hφ hCb hdec
    have hneg : ContDiff ℝ ∞ (fun x => -sa16y3_PA s A μ φ.1 x) := hPAs.neg
    have h2 := hC2 hφ hneg (fun j hj idx => by
      rw [sa16y5_pd_neg hPAs idx]
      have : eLpNorm (fun x => -partialDeriv idx (sa16y3_PA s A μ φ.1) x) (ENNReal.ofReal p) volume =
          eLpNorm (partialDeriv idx (sa16y3_PA s A μ φ.1)) (ENNReal.ofReal p) volume := eLpNorm_neg _ _ _
      rw [this]
      exact hPAb j hj idx)
    have hint : ∫ x, sa16sz_dens m p φ.1 (fun y => -sa16y3_PA s A μ φ.1 y) x =
        -∫ x, sa16sz_dens m p φ.1 (sa16y3_PA s A μ φ.1) x := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun x => sa16y5_dens_neg hPAs m x)
    rw [hint] at h2
    simp only [smul_eq_mul]
    have e0 : ∫ x, sa16sz_dens m p φ.1 (f0 : Euc d → ℝ) x = ∫ x, sa16sz_dens m p φ.1 (sa16z_P s μ φ.1) x := rfl
    have e1 : ∫ x, sa16sz_dens m p φ.1 (f1 : Euc d → ℝ) x =
        ∫ x, sa16sz_dens m p φ.1 (sa16y3_PA s A μ φ.1) x := rfl
    rw [e0, e1]
    have hprod : lam * (p * ∫ x, sa16sz_dens m p φ.1 (sa16z_P s μ φ.1) x) ≤
        lam * (p * (C1 * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ.1 k x ^ p)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hp0.le) hlam
    have hprod2 := mul_le_mul_of_nonneg_left h2 hp0.le
    nlinarith [hprod, hprod2]

end Ds2

end HRS.Whole.AppendixA.Phase2SA16R
