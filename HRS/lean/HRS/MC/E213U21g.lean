import HRS.MC.E213U21f

/-!
# Packet e213u21 (part g): the integral splittings `∫ whole = ∫ near + ∫ far`

For the particle system and the Gaussian limit, drift and covariance parts, with `b = max (a - Rw) 0` and
window length `L = Rw + T`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U10 HRS.MC.E213U11
  HRS.MC.E213U16

variable {d : ℕ}

theorem u21_int_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g h : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hfgh : ∀ᵐ ω ∂μ, f ω = g ω + h ω) :
    ∫ ω, f ω ∂μ = ∫ ω, g ω ∂μ + ∫ ω, h ω ∂μ := by
  have hh : Integrable h μ := by
    refine (hf.sub hg).congr ?_
    filter_upwards [hfgh] with ω hω
    simp only [Pi.sub_apply, hω]
    ring
  rw [← integral_add hg hh]
  exact integral_congr_ae hfgh

section Split

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u21_int_split_PA (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (fam : PrepFamily S β₀ hE) (Rw : ℝ)
    (hRw : 0 < Rw) {N : ℕ} (hN : 2 ≤ N) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) :
    ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (fun v => quadFieldAt m (regime S β₀ hE).D.s (fun t => withDensityReal ((regime S β₀ hE).ρ t))
          (fam.P N) (fam.X N) v ω) ∂(fam.P N) =
      ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (nearCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
          (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N) +
      ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (farCoef (max (a - Rw) 0) (fun v => quadFieldAt m (regime S β₀ hE).D.s
          (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N) := by
  have hN1 : 1 ≤ N := by omega
  have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Rw + T := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hH : a + T ≤ max (a - Rw) 0 + L := by
    rw [hLdef]; have := le_max_left (a - Rw) 0; linarith
  obtain ⟨CD, hCDpos, hCD⟩ := HRS.MC.E213U1.winDrift_near_proof hE T hT
  obtain ⟨CY, hCY1, hCY⟩ := u10_winPred_norm_le hE T hT
  obtain ⟨Cq, hCq⟩ := HRS.MC.Sec7.S7FCF5N.fcf5_F6c_B_moments_proof (regime S β₀ hE) (rLvl d) rfl L hL0 2
    (by norm_num)
  have hreal := fam.hreal N hN1
  have hq := hCq (max (a - Rw) 0) hb N hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal
  have hwhole := (HRS.MC.E213U8.window_identity_proof hE T hT a ha N hN1 (fam.P N) (fam.X₀ N) (fam.W N)
    (fam.X N) hreal Φ hΦ1).1
  have hnear := u21_near_int_A hE T hT a ha Φ hΦ _ L hb hba hL0 hH CD CY hCDpos.le (by linarith)
    (hCD a ha _ hb) (hCY a ha) hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal hq.1
  exact u21_int_split _ _ _ _ hwhole hnear
    (u21_split_ae_A hE T hT a ha Φ hΦ1 _ hb hba hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal)

theorem u21_int_split_PJ (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE)
    (fam : PrepFamily S β₀ hE) (Rw : ℝ) (hRw : 0 < Rw) {N : ℕ} (hN : 2 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) :
    ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (fun v => etaE m ((fam.X N) v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))) ∂(fam.P N) =
      ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (nearCoef (max (a - Rw) 0) (fun v => etaE m ((fam.X N) v.toNNReal ω)
          (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N) +
      ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
        (farCoef (max (a - Rw) 0) (fun v => etaE m ((fam.X N) v.toNNReal ω)
          (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N) := by
  have hN1 : 1 ≤ N := by omega
  have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hab : a - max (a - Rw) 0 ≤ Rw := by
    rcases le_total (a - Rw) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Rw + T := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hH : a + T ≤ max (a - Rw) 0 + L := by
    rw [hLdef]; have := le_max_left (a - Rw) 0; linarith
  obtain ⟨CJ, hCJpos, hCJ⟩ := HRS.MC.E213U2.winJ_near_proof hE T hT Rw hRw
  obtain ⟨CY, hCY1, hCY⟩ := u10_winPred_norm_le hE T hT
  obtain ⟨Cf, hCf⟩ := HRS.MC.Sec7.S7FCF5R.fcf5_E3b_F5_zeta_moments_proof (regime S β₀ hE) (rLvl d) rfl L hL0 2
    (by norm_num)
  have hreal := fam.hreal N hN1
  have hf := hCf (max (a - Rw) 0) hb N hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal
  obtain ⟨mm, hmm1, hmm2⟩ := HRS.MC.Sec7.S7UCD.s7_UC_D5_mean_window_proof (regime S β₀ hE) (rLvl d) rfl L hL0
    fam.P fam.X₀ fam.W fam.X fam.hreal gd.P₀ gd.η gd.limit (max (a - Rw) 0) hb N hN
  have hJa : U10_JNear hE T a ha (max (a - Rw) 0) CJ := fun zr hzm M hM u u' hu huu hu' =>
    (hCJ a ha _ hb hba hab zr hzm M hM u u' hu huu hu').2
  have hwhole := (HRS.MC.E213U8.window_identity_proof hE T hT a ha N hN1 (fam.P N) (fam.X₀ N) (fam.W N)
    (fam.X N) hreal Φ hΦ1).2.1
  have hnear := u21_near_int_J hE T hT a ha Φ hΦ _ L hb hba hL0 hH CJ CY hCJpos.le (by linarith)
    hJa (hCY a ha) hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal mm hmm2 hf.2.1
  exact u21_int_split _ _ _ _ hwhole hnear
    (u21_split_ae_J hE T hT a ha Φ hΦ1 _ hb hba hN (fam.P N) (fam.X₀ N) (fam.W N) (fam.X N) hreal)

theorem u21_int_split_GA (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE) (Rw : ℝ)
    (hRw : 0 < Rw) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) :
    ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.B v ω)) ∂gd.P₀ =
      ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀ +
      ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀ := by
  have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Rw + T := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hH : a + T ≤ max (a - Rw) 0 + L := by
    rw [hLdef]; have := le_max_left (a - Rw) 0; linarith
  obtain ⟨CD, hCDpos, hCD⟩ := HRS.MC.E213U1.winDrift_near_proof hE T hT
  obtain ⟨CY, hCY1, hCY⟩ := u10_winPred_norm_le hE T hT
  obtain ⟨C, -, hC⟩ := u11_B_moment gd L hL0 2 (by norm_num)
  have hq : Integrable (fun ω => ‖(pairLim (rLvl d) L (max (a - Rw) 0) gd.η gd.B ω).2‖ ^ (2 : ℝ)) gd.P₀ :=
    (hC _ hb).2.1
  have hnear := u21_gauss_near_int_A gd T hT a ha Φ hΦ _ L hb hba hL0 hH CD CY hCDpos.le (by linarith)
    (hCD a ha _ hb) (hCY a ha) hq
  exact u21_int_split _ _ _ _ (u21_gauss_whole_int_A gd T hT a ha Φ hΦ1) hnear
    (u21_gauss_split_A gd T hT a ha Φ hΦ1 _ hb hba)

theorem u21_int_split_GJ (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE) (Rw : ℝ)
    (hRw : 0 < Rw) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) :
    ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.η v ω)) ∂gd.P₀ =
      ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (nearCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀ +
      ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (farCoef (max (a - Rw) 0) (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀ := by
  have hb : 0 ≤ max (a - Rw) 0 := le_max_right _ _
  have hba : max (a - Rw) 0 ≤ a := max_le (by linarith) ha
  have hab : a - max (a - Rw) 0 ≤ Rw := by
    rcases le_total (a - Rw) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Rw + T := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hH : a + T ≤ max (a - Rw) 0 + L := by
    rw [hLdef]; have := le_max_left (a - Rw) 0; linarith
  obtain ⟨CJ, hCJpos, hCJ⟩ := HRS.MC.E213U2.winJ_near_proof hE T hT Rw hRw
  obtain ⟨CY, hCY1, hCY⟩ := u10_winPred_norm_le hE T hT
  obtain ⟨C, -, hC⟩ := u11_eta_moment gd L hL0 2 (by norm_num)
  have hJa : U10_JNear hE T a ha (max (a - Rw) 0) CJ := fun zr hzm M hM u u' hu huu hu' =>
    (hCJ a ha _ hb hba hab zr hzm M hM u u' hu huu hu').2
  have hnear := u21_gauss_near_int_J gd T hT a ha Φ hΦ _ L hb hba hL0 hH CJ CY hCJpos.le (by linarith)
    hJa (hCY a ha) (hC _ hb).2.1
  exact u21_int_split _ _ _ _ (u21_gauss_whole_int_J gd T hT a ha Φ hΦ1) hnear
    (u21_gauss_split_J gd T hT a ha Φ hΦ1 _ hb hba)

end Split

end HRS.MC.E213U21

end
