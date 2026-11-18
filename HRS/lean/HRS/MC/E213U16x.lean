import HRS.MC.E213U16w

/-!
# Packet e213u16, file x: domination, convergence of the covariance Riemann sums and `cond_removal_J`
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

section SnBoundJ

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_SnJ_bound (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂gd.P₀, ∀ n : ℕ,
      ‖SnJ gd T a ha Φ n ω‖ ≤ K * ‖procWin (rLvl d) (a + T) 0 gd.η ω‖ := by
  obtain ⟨C, hC0, hCae⟩ := u16_Jinc_ae gd T hT a ha
  have hH : 0 < a + T := by linarith
  have hcb : 0 ≤ cbNorm 5 Φ := (norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0)
  refine ⟨C * cbNorm 5 Φ * (a + T), by positivity, ?_⟩
  filter_upwards [hCae] with ω hω n
  obtain ⟨hnorm, -⟩ := hω
  set W := procWin (rLvl d) (a + T) 0 gd.η ω with hW
  have hW0 : 0 ≤ ‖W‖ := norm_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [SnJ, Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hn1 : 1 ≤ n := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmono := uPart_mono hH.le n
  have hu0 := uPart_nonneg hH.le n
  have hle : ∀ i, i < n → uPart (a + T) n (i + 1) ≤ a + T := fun i hi => uPart_le hH.le hn1 (Nat.succ_le_of_lt hi)
  calc ‖SnJ gd T a ha Φ n ω‖ ≤ ∑ i ∈ Finset.range n, ‖winJ (regime S β₀ hE) m T a ha
        (fun v => NegSobolev.embed m (gd.η v ω))
        (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))
        (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
          (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1))))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, (C * ‖W‖ * cbNorm 5 Φ) * ((a + T) / n) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hτI : uPart (a + T) n (i + 1) ∈ Set.Icc (0 : ℝ) (a + T) := ⟨(hu0 _), hle i hi'⟩
        have h1 := hnorm (uPart (a + T) n i) (uPart (a + T) n (i + 1)) (hu0 i) (hmono (Nat.le_succ i)) (hle i hi')
        rw [uPart_succ_sub hn1] at h1
        refine ((winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω))
          (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))).le_opNorm _).trans ?_
        calc _ ≤ (C * ‖W‖ * ((a + T) / n)) * cbNorm 5 Φ :=
              mul_le_mul h1 (u16_Ucan_iter2_bound hE T hT a ha Φ hΦ hτI _) (norm_nonneg _) (by positivity)
          _ = _ := by ring
    _ = (C * cbNorm 5 Φ * (a + T)) * ‖W‖ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end SnBoundJ


section SnLimJ

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_SnJ_tendsto (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    ∀ᵐ ω ∂gd.P₀, Tendsto (fun n => SnJ gd T a ha Φ n ω) atTop
      (𝓝 (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.η v ω)))) := by
  have hH : 0 < a + T := by linarith
  filter_upwards [gaussian_rs_exists_proof gd T hT a ha Φ hΦ] with ω hω
  obtain ⟨-, hRS⟩ := hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hpart⟩ := hRS ε hε
  refine ⟨⌈(a + T) / δ⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmesh : (a + T) / n < δ := by
    rw [div_lt_iff₀ hnpos]
    have h1 : (a + T) / δ < n := by
      exact lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast (show ⌈(a + T) / δ⌉₊ < n by omega))
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hsm : StrictMono (fun i : Fin (n + 1) => uPart (a + T) n i) :=
    (uPart_strictMono hH hn1).comp Fin.val_strictMono
  have key := hpart n (fun i : Fin (n + 1) => uPart (a + T) n i) (fun i : Fin n => uPart (a + T) n (i + 1)) hsm
    (by simp [uPart_zero]) (by simp [uPart_last hn1])
    (fun i => ⟨by simpa using uPart_mono hH.le n (Nat.le_succ i), by simp⟩)
    (fun i => by
      simp only [Fin.val_succ, Fin.coe_castSucc]
      rw [uPart_succ_sub hn1]
      exact hmesh)
  rw [Real.dist_eq]
  have hsum : ∑ i : Fin n, rsSumJ (Ucan hE T a ha Φ)
      (fun τ => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
      (fun u u' => winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.η v ω)) (Set.Ioc u u'))
      (uPart (a + T) n ((i : ℕ) + 1)) (uPart (a + T) n i) (uPart (a + T) n ((i : ℕ) + 1)) =
      SnJ gd T a ha Φ n ω := by
    unfold SnJ rsSumJ
    exact Fin.sum_univ_eq_sum_range (fun i => winJ (regime S β₀ hE) m T a ha
      (fun v => NegSobolev.embed m (gd.η v ω))
      (Set.Ioc (uPart (a + T) n i) (uPart (a + T) n (i + 1)))
      (iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
        (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1))))) n
  simp only [Fin.val_succ, Fin.coe_castSucc] at key
  rw [← hsum]
  exact key

end SnLimJ


section Final

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem cond_removal_J_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.η v ω)) ∂gd.P₀ =
      ∫ ω, (gd.Jwin T a ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀ := by
  obtain ⟨K, hK, hbd⟩ := u16_SnJ_bound gd T hT a ha Φ hΦ
  have hH : 0 < a + T := by linarith
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun n ω => SnJ gd T a ha Φ n ω)
    (f := fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.η v ω)))
    (bound := fun ω => K * ‖procWin (rLvl d) (a + T) 0 gd.η ω‖)
    (fun n => ?_) ((u16_Wnorm_integrable gd (a + T) hH).const_mul K) (fun n => ?_)
    (u16_SnJ_tendsto gd T hT a ha Φ hΦ)
  · have hconst : Tendsto (fun n : ℕ => ∫ ω, SnJ gd T a ha Φ n ω ∂gd.P₀) atTop
        (𝓝 (∫ ω, (gd.Jwin T a ω) (iteratedFDeriv ℝ 2 Φ (gd.Zwin T a ω)) ∂gd.P₀)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (u16_SnJ_integral gd T hT a ha Φ hΦ hn).symm
    exact tendsto_nhds_unique hlim hconst
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [SnJ, Finset.range_zero, Finset.sum_empty]
      exact aestronglyMeasurable_const
    · exact (u16_SnJ_integrable gd T hT a ha Φ hΦ hn).aestronglyMeasurable
  · filter_upwards [hbd] with ω hω using hω n

end Final

end HRS.MC.E213U16

end
