import HRS.MC.E213U21e

/-!
# Packet e213u21 (part f): the Gaussian side: splitting and integrability of the Riemann--Stieltjes integrals

* `u21_gauss_whole_int_A/J`: the whole Gaussian integrals are integrable (a.e. limits of the Riemann sums
  `SnD`, `SnJ`, dominated by `Gblk`, resp. `‖procWin‖`);
* `u21_gauss_split_A/J`: a.s. whole `=` near `+` far (pathwise `rs_split_*`);
* `u21_gauss_near_int_A/J`: the near parts are integrable (functionals of `pairLim`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U10 HRS.MC.E213U11
  HRS.MC.E213U16

variable {d : ℕ}

section Gauss

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u21_gauss_whole_int_A (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    Integrable (fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
      (fun v => NegSobolev.embed m (gd.B v ω))) gd.P₀ := by
  obtain ⟨K, hK0, hbd⟩ := u16_Sn_bound gd T hT a ha Φ hΦ
  have hlim := u16_Sn_tendsto gd T hT a ha Φ hΦ
  have hmeas : AEStronglyMeasurable (fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ)
      (gd.Zwin (a + T) 0 ω) (fun v => NegSobolev.embed m (gd.B v ω))) gd.P₀ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => SnD gd T a ha Φ (n + 1))
      (fun n => (u16_Sn_integrable gd T hT a ha Φ hΦ (Nat.le_add_left 1 n)).aestronglyMeasurable) ?_
    filter_upwards [hlim] with ω h
    exact (tendsto_add_atTop_iff_nat 1).2 h
  refine ((u16_Gblk_integrable gd (a + T)).const_mul (cbNorm 5 Φ * K)).mono' hmeas ?_
  filter_upwards [hbd, hlim] with ω hb hl
  have := le_of_tendsto hl.norm (Eventually.of_forall hb)
  simpa [mul_assoc] using this

theorem u21_gauss_whole_int_J (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    Integrable (fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
      (fun v => NegSobolev.embed m (gd.η v ω))) gd.P₀ := by
  obtain ⟨K, hK0, hbd⟩ := u16_SnJ_bound gd T hT a ha Φ hΦ
  have hlim := u16_SnJ_tendsto gd T hT a ha Φ hΦ
  have hH : 0 < a + T := by linarith
  have hmeas : AEStronglyMeasurable (fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ)
      (gd.Zwin (a + T) 0 ω) (fun v => NegSobolev.embed m (gd.η v ω))) gd.P₀ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => SnJ gd T a ha Φ (n + 1))
      (fun n => (u16_SnJ_integrable gd T hT a ha Φ hΦ (Nat.le_add_left 1 n)).aestronglyMeasurable) ?_
    filter_upwards [hlim] with ω h
    exact (tendsto_add_atTop_iff_nat 1).2 h
  refine ((u16_Wnorm_integrable gd (a + T) hH).const_mul K).mono' hmeas ?_
  filter_upwards [hbd, hlim] with ω hb hl
  exact le_of_tendsto hl.norm (Eventually.of_forall hb)

theorem u21_gauss_split_A (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    ∀ᵐ ω ∂gd.P₀,
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (fun v => NegSobolev.embed m (gd.B v ω)) =
        rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (nearCoef b (fun v => NegSobolev.embed m (gd.B v ω))) +
        rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (farCoef b (fun v => NegSobolev.embed m (gd.B v ω))) := by
  have hH : 0 < a + T := by linarith
  filter_upwards [u11_B_integrable gd (a + T) hH] with ω hint
  exact (HRS.MC.E213U7.rs_split_drift_proof hE T hT a ha Φ hΦ (gd.Zwin (a + T) 0 ω) (fun v => gd.B v ω)
    (u11_B_nearCoef_measurable gd ω) hint b hb hba).2.2

theorem u21_gauss_split_J (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    ∀ᵐ ω ∂gd.P₀,
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (fun v => NegSobolev.embed m (gd.η v ω)) =
        rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (nearCoef b (fun v => NegSobolev.embed m (gd.η v ω))) +
        rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
          (farCoef b (fun v => NegSobolev.embed m (gd.η v ω))) := by
  filter_upwards [ae_all_iff.2 (fun L : ℕ => u11_eta_cont gd (L : ℝ))] with ω hcL
  have hcI : ContinuousOn (fun t => gd.η t ω) (Set.Ici 0) := HRS.MC.E213U14.u14_continuousOn_Ici hcL
  have hzm : Measurable (nearCoef 0 (fun v => gd.η v ω)) :=
    HRS.MC.E213U14.u14_nearCoef_meas_of_continuousOn hcI
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := a + T)).exists_bound_of_continuousOn
    (hcI.mono Set.Icc_subset_Ici_self)
  exact (HRS.MC.E213U7.rs_split_J_proof hE T hT a ha Φ hΦ (gd.Zwin (a + T) 0 ω) (fun v => gd.η v ω) hzm M hM
    b hb hba).2.2

theorem u21_gauss_near_int_A (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a)
    (hL : 0 < L) (hH : a + T ≤ b + L) (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY)
    (hCD : U10_DriftNear hE T a ha b CD) (hCY : U10_PredBound hE T a ha CY)
    (hq : Integrable (fun ω => ‖(pairLim (rLvl d) L b gd.η gd.B ω).2‖ ^ (2 : ℝ)) gd.P₀) :
    Integrable (fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef b (fun v => NegSobolev.embed m (gd.B v ω)))) gd.P₀ := by
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hcb : cbNorm 5 Φ ≤ 1 := hΦ.2.2
  have hpl := u10_pairLim_aemeasurable hE gd L hL b hb
  have hFDc := u10_FD_cont hE T hT a ha Φ hΦ1 hcb b L hb hL.le hH CD CY hCD0 hCY0 hCD hCY
  have hA1 := u10_gauss_A hE gd T hT a ha Φ hΦ1 b L hb hba hL hH
  have hfm : AEStronglyMeasurable (fun ω => ‖(pairLim (rLvl d) L b gd.η gd.B ω).2‖) gd.P₀ :=
    (continuous_snd.norm).aestronglyMeasurable.comp_aemeasurable hpl
  have hf1 := u21_integrable_of_sq gd.P₀ _ hfm (by simpa only [norm_norm] using hq)
  have hmeas : AEStronglyMeasurable (fun ω => u10_FD hE T a ha Φ b L hL.le hH
      (pairLim (rLvl d) L b gd.η gd.B ω)) gd.P₀ :=
    hFDc.aestronglyMeasurable.comp_aemeasurable hpl
  have hint : Integrable (fun ω => u10_FD hE T a ha Φ b L hL.le hH
      (pairLim (rLvl d) L b gd.η gd.B ω)) gd.P₀ := by
    refine (hf1.const_mul (CD * Real.sqrt L)).mono' hmeas (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact u10_FD_abs_le hE T hT a ha Φ hΦ1 hcb b L hL.le hH CD hCD0 hCD _
  exact hint.congr (hA1.mono fun ω h => h.symm)

theorem u21_gauss_near_int_J (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a)
    (hL : 0 < L) (hH : a + T ≤ b + L) (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY)
    (hJ : U10_JNear hE T a ha b CJ) (hCY : U10_PredBound hE T a ha CY)
    (hf : Integrable (fun ω => ‖procWin (rLvl d) L b gd.η ω‖ ^ (2 : ℝ)) gd.P₀) :
    Integrable (fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef b (fun v => NegSobolev.embed m (gd.η v ω)))) gd.P₀ := by
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hcb : cbNorm 5 Φ ≤ 1 := hΦ.2.2
  have hpl := u10_pairLim_aemeasurable hE gd L hL b hb
  have hGJc := u10_GJ_cont hE T hT a ha Φ hΦ1 hcb b L hb hL.le hH CJ CY hCJ0 hCY0 hJ hCY 0
  have hJ1 := u10_gauss_J hE gd T hT a ha Φ hΦ1 b L hb hba hL hH
  have hcm : Continuous fun x : U10B d L => ‖x.1 + 0‖ := (continuous_fst.add continuous_const).norm
  have hfm : AEStronglyMeasurable (fun ω => ‖(pairLim (rLvl d) L b gd.η gd.B ω).1 + 0‖) gd.P₀ :=
    hcm.aestronglyMeasurable.comp_aemeasurable hpl
  have hf1 : Integrable (fun ω => ‖(pairLim (rLvl d) L b gd.η gd.B ω).1 + 0‖) gd.P₀ := by
    refine u21_integrable_of_sq gd.P₀ _ hfm ?_
    refine hf.congr (Eventually.of_forall fun ω => ?_)
    simp only [norm_norm, add_zero]
    rfl
  have hmeas : AEStronglyMeasurable (fun ω => u10_GJ hE T a ha Φ b L hL.le hH 0
      (pairLim (rLvl d) L b gd.η gd.B ω)) gd.P₀ :=
    hGJc.aestronglyMeasurable.comp_aemeasurable hpl
  have hint : Integrable (fun ω => u10_GJ hE T a ha Φ b L hL.le hH 0
      (pairLim (rLvl d) L b gd.η gd.B ω)) gd.P₀ := by
    refine (hf1.const_mul (CJ * L)).mono' hmeas (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact u10_FJ_abs_le hE T hT a ha Φ hΦ1 hcb b L hb hL.le hH CJ hCJ0 hJ _
  exact hint.congr (hJ1.mono fun ω h => h.symm)

end Gauss

end HRS.MC.E213U21

end
