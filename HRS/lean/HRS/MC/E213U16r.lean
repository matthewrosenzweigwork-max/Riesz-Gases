import HRS.MC.E213U16q
import HRS.MC.E213U16a

/-!
# Packet e213u16, file r: Riemann sums on the uniform partition and `cond_removal_drift`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Unif

/-- The uniform partition `i H / n`. -/
def uPart (H : ℝ) (n i : ℕ) : ℝ := (i : ℝ) * H / n

theorem uPart_zero (H : ℝ) (n : ℕ) : uPart H n 0 = 0 := by simp [uPart]

theorem uPart_last {H : ℝ} {n : ℕ} (hn : 1 ≤ n) : uPart H n n = H := by
  have : (n : ℝ) ≠ 0 := by positivity
  simp [uPart, this]

theorem uPart_mono {H : ℝ} (hH : 0 ≤ H) (n : ℕ) : Monotone (uPart H n) := by
  intro i j hij
  unfold uPart
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hH) (Nat.cast_nonneg n)

theorem uPart_nonneg {H : ℝ} (hH : 0 ≤ H) (n i : ℕ) : 0 ≤ uPart H n i := by
  unfold uPart; positivity

theorem uPart_le {H : ℝ} (hH : 0 ≤ H) {n i : ℕ} (hn : 1 ≤ n) (hi : i ≤ n) : uPart H n i ≤ H :=
  (uPart_mono hH n hi).trans (uPart_last hn).le

theorem uPart_succ_sub {H : ℝ} {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : uPart H n (i + 1) - uPart H n i = H / n := by
  have : (n : ℝ) ≠ 0 := by positivity
  unfold uPart
  push_cast
  field_simp
  ring

theorem uPart_strictMono {H : ℝ} (hH : 0 < H) {n : ℕ} (hn : 1 ≤ n) : StrictMono (uPart H n) := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  have := uPart_succ_sub (H := H) hn i
  have h2 : 0 < H / n := by positivity
  linarith

end Unif


section Sn

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The Riemann sum of the drift summand on the uniform partition with right-endpoint tags. -/
def SnD (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (n : ℕ) (ω : gd.Ω₀) : ℝ :=
  ∑ i ∈ Finset.range n, fderiv ℝ (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
    (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1)))
    (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
      (uPart (a + T) n i) (uPart (a + T) n (i + 1)))

theorem u16_Sn_integrable (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {n : ℕ} (hn : 1 ≤ n) : Integrable (SnD gd T a ha Φ n) gd.P₀ := by
  have hH : 0 < a + T := by linarith
  refine integrable_finsetSum _ fun i hi => ?_
  have hi' : i < n := Finset.mem_range.1 hi
  exact u16_incR_integrable gd T hT a ha Φ hΦ (uPart_nonneg hH.le n i) (uPart_mono hH.le n (Nat.le_succ i))
    (uPart_le hH.le hn (Nat.succ_le_of_lt hi'))

theorem u16_Sn_integral (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ ω, SnD gd T a ha Φ n ω ∂gd.P₀ = ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω) (gd.Dwin T a ω) ∂gd.P₀ := by
  have hH : 0 < a + T := by linarith
  have hu0 := uPart_nonneg hH.le n
  have hmono := uPart_mono hH.le n
  have hle : ∀ i, i < n → uPart (a + T) n (i + 1) ≤ a + T := fun i hi =>
    uPart_le hH.le hn (Nat.succ_le_of_lt hi)
  -- the decomposition of `Dwin`
  have hD : ∀ᵐ ω ∂gd.P₀, gd.Dwin T a ω = ∑ i ∈ Finset.range n,
      winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
        (uPart (a + T) n i) (uPart (a + T) n (i + 1)) := by
    filter_upwards [HRS.MC.E213U11.u11_B_integrable gd (a + T) hH] with ω hint
    unfold GaussData.Dwin
    rw [dif_pos ha]
    have := u16_winDrift_sum hE T hT a ha (fun v => gd.B v ω) (HRS.MC.E213U11.u11_B_nearCoef_measurable gd ω) hint
      (uPart (a + T) n) hmono (hu0 0) hn (by rw [uPart_last hn])
    rw [uPart_zero, uPart_last hn] at this
    exact this
  calc ∫ ω, SnD gd T a ha Φ n ω ∂gd.P₀
      = ∑ i ∈ Finset.range n, ∫ ω, fderiv ℝ (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
          (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1)))
          (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
            (uPart (a + T) n i) (uPart (a + T) n (i + 1))) ∂gd.P₀ := by
        unfold SnD
        rw [integral_finset_sum]
        intro i hi
        exact u16_incR_integrable gd T hT a ha Φ hΦ (hu0 i) (hmono (Nat.le_succ i)) (hle i (Finset.mem_range.1 hi))
    _ = ∑ i ∈ Finset.range n, ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω)
          (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
            (uPart (a + T) n i) (uPart (a + T) n (i + 1))) ∂gd.P₀ := by
        refine Finset.sum_congr rfl fun i hi => ?_
        exact (u16_cond_inc gd T hT a ha Φ hΦ (hu0 i) (hmono (Nat.le_succ i)) (hle i (Finset.mem_range.1 hi))).symm
    _ = ∫ ω, ∑ i ∈ Finset.range n, fderiv ℝ Φ (gd.Zwin T a ω)
          (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
            (uPart (a + T) n i) (uPart (a + T) n (i + 1))) ∂gd.P₀ := by
        rw [integral_finset_sum]
        intro i hi
        exact u16_incL_integrable gd T hT a ha Φ hΦ (hu0 i) (hmono (Nat.le_succ i)) (hle i (Finset.mem_range.1 hi))
    _ = ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω) (gd.Dwin T a ω) ∂gd.P₀ := by
        refine integral_congr_ae ?_
        filter_upwards [hD] with ω hω
        rw [hω, map_sum]

end Sn


section SnBound

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Sn_bound (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ ω ∂gd.P₀, ∀ n : ℕ, ‖SnD gd T a ha Φ n ω‖ ≤ cbNorm 5 Φ * K * Gblk gd (a + T) ω := by
  obtain ⟨K, hK, hbd⟩ := u16_winDrift_norm_bound (S := S) (β₀ := β₀) hE T
  have hH : 0 < a + T := by linarith
  have hcb : 0 ≤ cbNorm 5 Φ := (norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0)
  refine ⟨K, hK, ?_⟩
  filter_upwards [HRS.MC.E213U11.u11_B_integrable gd (a + T) hH, u16_B_int_bound gd (a + T) hH] with ω hint hG n
  have hGn : 0 ≤ Gblk gd (a + T) ω := by
    unfold Gblk
    exact Finset.sum_nonneg fun k _ => norm_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [SnD]
    positivity
  have hn1 : 1 ≤ n := hn
  have hmono := uPart_mono hH.le n
  have hu0 := uPart_nonneg hH.le n
  have hle : ∀ i, i < n → uPart (a + T) n (i + 1) ≤ a + T := fun i hi => uPart_le hH.le hn1 (Nat.succ_le_of_lt hi)
  have hii : ∀ i, i < n → IntervalIntegrable (fun x => ‖gd.B x ω‖) volume (uPart (a + T) n i) (uPart (a + T) n (i + 1)) := by
    intro i hi
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hmono (Nat.le_succ i))]
    exact hint.mono_set fun v hv => ⟨(hu0 i).trans hv.1.le, hv.2.trans (hle i hi)⟩
  calc ‖SnD gd T a ha Φ n ω‖ ≤ ∑ i ∈ Finset.range n, ‖fderiv ℝ (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
        (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1)))
        (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
          (uPart (a + T) n i) (uPart (a + T) n (i + 1)))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, cbNorm 5 Φ * K * ∫ x in (uPart (a + T) n i)..(uPart (a + T) n (i + 1)), ‖gd.B x ω‖ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hτI : uPart (a + T) n (i + 1) ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu0 _, hle i hi'⟩
        rw [Real.norm_eq_abs]
        refine (u16_Ucan_fderiv_bound hE T hT a ha Φ hΦ hτI _ _).trans ?_
        have h2 := hbd a ha (fun v => gd.B v ω) hint (uPart (a + T) n i) (uPart (a + T) n (i + 1)) (hu0 i)
          (hmono (Nat.le_succ i)) (hle i hi')
        rw [intervalIntegral.integral_of_le (hmono (Nat.le_succ i)), mul_assoc]
        exact mul_le_mul_of_nonneg_left h2 hcb
    _ = cbNorm 5 Φ * K * ∫ x in (uPart (a + T) n 0)..(uPart (a + T) n n), ‖gd.B x ω‖ := by
        rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals (a := uPart (a + T) n)
          (fun i hi => hii i hi)]
    _ ≤ cbNorm 5 Φ * K * Gblk gd (a + T) ω := by
        rw [uPart_zero, uPart_last hn1, intervalIntegral.integral_of_le hH.le]
        exact mul_le_mul_of_nonneg_left hG (mul_nonneg hcb hK.le)

end SnBound


section SnLim

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem u16_Sn_tendsto (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    ∀ᵐ ω ∂gd.P₀, Tendsto (fun n => SnD gd T a ha Φ n ω) atTop
      (𝓝 (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.B v ω)))) := by
  have hH : 0 < a + T := by linarith
  filter_upwards [gaussian_rs_exists_proof gd T hT a ha Φ hΦ] with ω hω
  obtain ⟨hRS, -⟩ := hω
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
  have hsum : ∑ i : Fin n, rsSumD (Ucan hE T a ha Φ)
      (fun τ => winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) τ)
      (fun u u' => winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω)) u u')
      (uPart (a + T) n ((i : ℕ) + 1)) (uPart (a + T) n i) (uPart (a + T) n ((i : ℕ) + 1)) =
      SnD gd T a ha Φ n ω := by
    unfold SnD rsSumD
    exact Fin.sum_univ_eq_sum_range (fun i => fderiv ℝ (Ucan hE T a ha Φ (uPart (a + T) n (i + 1)))
      (winPred (regime S β₀ hE) m T a ha (gd.Zwin (a + T) 0 ω) (uPart (a + T) n (i + 1)))
      (winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (gd.B v ω))
        (uPart (a + T) n i) (uPart (a + T) n (i + 1)))) n
  simp only [Fin.val_succ, Fin.coe_castSucc] at key
  rw [← hsum]
  exact key

end SnLim

end HRS.MC.E213U16

end
