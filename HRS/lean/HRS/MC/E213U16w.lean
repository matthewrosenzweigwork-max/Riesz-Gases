import HRS.MC.E213U16v
import HRS.MC.E213U16r

/-!
# Packet e213u16, file w: Riemann sums of the covariance summand and `cond_removal_J`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10 HRS.MC.E213U11

variable {d : ℕ}

section SumAdj

theorem u16_sum_adj {X : Type*} [AddCommGroup X] (f : ℝ → ℝ → X) (p : ℕ → ℝ) (h0 : f (p 0) (p 0) = 0) (n : ℕ)
    (hadd : ∀ i, i < n → f (p 0) (p (i + 1)) = f (p 0) (p i) + f (p i) (p (i + 1))) :
    ∑ i ∈ Finset.range n, f (p i) (p (i + 1)) = f (p 0) (p n) := by
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (fun i hi => hadd i (Nat.lt_succ_of_lt hi)), hadd k (Nat.lt_succ_self k)]

end SumAdj


section IncInt

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_incJ_integrable (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτ : τ ≤ a + T) (hτ0 : 0 < τ) :
    Integrable (fun ω => winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u τ)
        (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω))) gd.P₀ ∧
    Integrable (fun ω => winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u τ)
        (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ)
          (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ))) gd.P₀ := by
  have hτI : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hτ0.le, hτ⟩
  obtain ⟨Λ, W', ⟨CΛ, hCΛ0, hCΛ⟩, hW', haeW, hJ⟩ := u16_Jinc_past gd T hT a ha hu huτ hτ hτ0
  have hWi := u16_Wnorm_integrable gd τ hτ0
  have hWm := u16_Wtau_aem gd τ hτ0
  have hcb : 0 ≤ cbNorm 5 Φ := (norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0)
  constructor
  · have hg : Integrable (fun ω => Λ (procWin (rLvl d) τ 0 gd.η ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω))) gd.P₀ := by
      have hc : Continuous fun p : PathSpace d (rLvl d) τ × PathSpace d m T =>
          Λ p.1 (iteratedFDeriv ℝ 2 Φ p.2) :=
        (Λ.continuous.comp continuous_fst).clm_apply ((u16_iter2_cont hΦ).comp continuous_snd)
      have hmeas := hc.aestronglyMeasurable.comp_aemeasurable (hWm.prodMk (u16_Zwin_aem gd T hT a ha))
      refine (hWi.const_mul (CΛ * cbNorm 5 Φ)).mono' hmeas (Eventually.of_forall fun ω => ?_)
      calc ‖Λ (procWin (rLvl d) τ 0 gd.η ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω))‖
          ≤ ‖Λ (procWin (rLvl d) τ 0 gd.η ω)‖ * ‖iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)‖ :=
            (Λ _).le_opNorm _
        _ ≤ (CΛ * ‖procWin (rLvl d) τ 0 gd.η ω‖) * cbNorm 5 Φ :=
            mul_le_mul (hCΛ _) (u16_norm_iter2_le hΦ _) (norm_nonneg _) (by positivity)
        _ = CΛ * cbNorm 5 Φ * ‖procWin (rLvl d) τ 0 gd.η ω‖ := by ring
    refine hg.congr ?_
    filter_upwards [hJ] with ω h
    rw [h]
  · have hg : Integrable (fun ω => Λ (procWin (rLvl d) τ 0 gd.η ω) (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ)
        (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ))) gd.P₀ := by
      have hc : Continuous fun p : PathSpace d (rLvl d) τ × PathSpace d m T =>
          Λ p.1 (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) p.2) :=
        (Λ.continuous.comp continuous_fst).clm_apply
          ((u16_Ucan_iter2_cont hE T hT a ha Φ hΦ hτI).comp continuous_snd)
      have hmeas := hc.aestronglyMeasurable.comp_aemeasurable (hWm.prodMk (u16_Y_aem gd T hT a ha hτI))
      refine (hWi.const_mul (CΛ * cbNorm 5 Φ)).mono' hmeas (Eventually.of_forall fun ω => ?_)
      calc ‖Λ (procWin (rLvl d) τ 0 gd.η ω) (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ)
            (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ))‖
          ≤ ‖Λ (procWin (rLvl d) τ 0 gd.η ω)‖ * ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ)
            (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)‖ :=
            (Λ _).le_opNorm _
        _ ≤ (CΛ * ‖procWin (rLvl d) τ 0 gd.η ω‖) * cbNorm 5 Φ :=
            mul_le_mul (hCΛ _) (u16_Ucan_iter2_bound hE T hT a ha Φ hΦ hτI _) (norm_nonneg _) (by positivity)
        _ = CΛ * cbNorm 5 Φ * ‖procWin (rLvl d) τ 0 gd.η ω‖ := by ring
    refine hg.congr ?_
    filter_upwards [hJ] with ω h
    rw [h]

end IncInt


section Sn

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The Riemann sum of the covariance summand on the uniform partition with right-endpoint tags. -/
def SnJ (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (n : ℕ) (ω : gd.Ω₀) : ℝ :=
  ∑ i ∈ Finset.range n, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
    (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))
    (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
      (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1))))

theorem u16_SnJ_integrable (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {n : ℕ} (hn : 1 ≤ n) : Integrable (SnJ gd T a ha Φ n) gd.P₀ := by
  have hH : 0 < a + T := by linarith
  refine integrable_finsetSum _ fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  have hpos : 0 < uPart (a + T) n (i + 1) := (uPart_strictMono hH hn) (Nat.lt_succ_self i) |>.trans_le' (uPart_nonneg hH.le n i)
  exact (u16_incJ_integrable gd T hT a ha Φ hΦ (uPart_nonneg hH.le n i) (uPart_mono hH.le n (Nat.le_succ i))
    (uPart_le hH.le hn (Nat.succ_le_of_lt hi')) hpos).2

theorem u16_SnJ_integral (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, SnJ gd T a ha Φ n ω ∂gd.P₀ = ∫ ω, (gd.Jwin T a ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
  have hH : 0 < a + T := by linarith
  have hu0 := uPart_nonneg hH.le n
  have hmono := uPart_mono hH.le n
  have hle : ∀ i, i < n → uPart (a + T) n (i + 1) ≤ a + T := fun i hi =>
    uPart_le hH.le hn (Nat.succ_le_of_lt hi)
  have hpos : ∀ i, 0 < uPart (a + T) n (i + 1) := fun i =>
    ((uPart_strictMono hH hn) (Nat.lt_succ_self i)).trans_le' (hu0 i)
  obtain ⟨C, -, hCae⟩ := u16_Jinc_ae gd T hT a ha
  -- the decomposition of `Jwin`
  have hD : ∀ᵐ ω ∂gd.P₀, gd.Jwin T a ω = ∑ i ∈ Finset.range n,
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
        (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1))) := by
    filter_upwards [hCae] with ω hω
    obtain ⟨hnorm, hadd⟩ := hω
    have h0 : winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
        (Set.Ioc (uPart (a + T) n 0) (uPart (a + T) n 0)) = 0 := by
      have := hnorm (uPart (a + T) n 0) (uPart (a + T) n 0) (hu0 0) le_rfl
        (by rw [uPart_zero]; exact hH.le)
      rw [sub_self, mul_zero] at this
      exact norm_le_zero_iff.1 this
    have key := u16_sum_adj (fun u u' => winJ (regime S β₀ hE) m T a ha
        (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u')) (uPart (a + T) n) h0 n (fun i hi =>
      hadd _ _ _ (hu0 0) (hmono (Nat.zero_le i)) (hmono (Nat.le_succ i)) (hle i hi))
    rw [uPart_zero, uPart_last hn] at key
    unfold GaussData.Jwin
    rw [dif_pos ha]
    exact key.symm
  calc ∫ ω, SnJ gd T a ha Φ n ω ∂gd.P₀
      = ∑ i ∈ Finset.range n, ∫ ω, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
          (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))
          (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
            (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1)))) ∂gd.P₀ := by
        unfold SnJ
        rw [integral_finsetSum]
        intro i hi
        exact (u16_incJ_integrable gd T hT a ha Φ hΦ (hu0 i) (hmono (Nat.le_succ i)) (hle i (Finset.mem_range.1 hi))
          (hpos i)).2
    _ = ∑ i ∈ Finset.range n, ∫ ω, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
          (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))
          (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        exact (u16_cond_incJ gd T hT a ha Φ hΦ (hu0 i) (hmono (Nat.le_succ i)) (hle i (Finset.mem_range.1 hi))
          (hpos i)).symm
    _ = ∫ ω, ∑ i ∈ Finset.range n, winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
          (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))
          (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
        rw [integral_finsetSum]
        intro i hi
        exact (u16_incJ_integrable gd T hT a ha Φ hΦ (hu0 i) (hmono (Nat.le_succ i)) (hle i (Finset.mem_range.1 hi))
          (hpos i)).1
    _ = ∫ ω, (gd.Jwin T a ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
        refine integral_congr_ae ?_
        filter_upwards [hD] with ω hω
        rw [hω, sum_apply]

end Sn

end HRS.MC.E213U16

end
