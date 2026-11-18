import HRS.MS.S111X2Aux4
import HRS.MS.TransOpAux23

/-!
# S11.1 X2, packet E01: the thermal reference carries a `KRep` operator, hence `ResponseForm`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111X2

open HRS.Whole HRS.Whole.Q34
open HRS (Euc)

variable {d : ℕ}

/-- For a reference density with a Gaussian envelope, `Kop` is represented by a bounded positive operator. -/
theorem s111x2_krep_of_tcref (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M₀ c S : ℝ} (hc : 0 < c)
    {N : ℕ} {ρ : Euc d → ℝ} (h : HRS.MS.TcDefs.TcRef d ρ M₀ c S N)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)] :
    ∃ (Mg : ℝ) (K : Lp ℝ 2 (HRS.Whole.withDensityReal ρ) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal ρ)),
      KRep (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) K Mg := by
  have hρ := h.prob
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    obtain ⟨Mg, hk⟩ := HRS.MS.TcR.tc2_tcker_log hd hρ hc h.gauss
    have hl2 := HRS.MS.TcR.tc2_l_memLp hρ hc h.gauss
    have hp := HRS.MS.TcR.tc2_pos_log hd hρ hk
    exact ⟨Mg, HRS.MS.TcR.tc2_Kc hk, ⟨HRS.MS.TcR.tc2_Kc_symm hk, HRS.MS.TcR.tc2_Kc_pos hk hp,
      hk.mg_nonneg, HRS.MS.TcR.tc2_Kc_norm_le hk, HRS.MS.TcR.tc2_Pc_Kc hk,
      HRS.MS.TcR.tc2_kop_class_log hρ hk hl2⟩⟩
  · have hQ : Q34Hyp d s ρ M₀ := ⟨hd, h0, hsd, hρ, HRS.MS.TcR.tc2_le_M0 hρ hc h.gauss⟩
    have hM0 : 0 ≤ M₀ := (hρ.nonneg 0).trans (hQ.hM 0)
    exact ⟨Mg d s M₀, Kc hQ, ⟨Kc_symm hQ, Kc_pos hQ, Mg_nonneg hQ.hd hQ.hsd hM0, Kc_norm_le hQ,
      Pc_Kc hQ, fun U hU => kop_class hQ (Filter.EventuallyEq.refl _ _) hU⟩⟩

/-- **E01.** Uniform response forms for the thermal reference, including `θ = 0`. -/
theorem s111x2_thermal_response_forms (hd : 2 ≤ d)
    (s a beta Gamma : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hGamma : 0 ≤ Gamma) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧
      ∀ rho : Euc d → ℝ, HRS.Whole.IsThermalEquilibrium d s a beta rho →
        ∀ theta ∈ Set.Icc (0 : ℝ) Gamma,
          ResponseForm (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal rho) theta eta := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  by_cases hex : ∃ rho : Euc d → ℝ, HRS.Whole.IsThermalEquilibrium d s a beta rho
  · obtain ⟨ρ1, hρ1⟩ := hex
    obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hbeta hρ1
    haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ1) := isProbabilityMeasure_nu hTc.prob
    obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
    have hMg := hK.nonneg
    refine ⟨(1 + Gamma * Mg)⁻¹, by positivity, ?_, ?_⟩
    · apply inv_le_one_of_one_le₀
      nlinarith
    · intro rho hrho theta hθ
      have e1 := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho
      have e2 := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hρ1
      have : rho = ρ1 := e1.trans e2.symm
      subst this
      exact s111x2_responseForm hK hθ.1 hθ.2
  · refine ⟨1, one_pos, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩

end HRS.MS.S111X2
