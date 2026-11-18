import HRS.MC.E214N7
import HRS.MC.E214N2
import HRS.MC.E214N3

/-!
# E214N8: the shifted `GaussData` and the pointwise bound of `D_{a+h} - D^{(h)}_a`

`shiftGD_proof` is the same structure as `E214Plan.shiftGD`, with our proved `shifted_limit_proof`, `shifted_wick_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section ShiftGD

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

/-- The shifted `GaussData` (same probability space). -/
def shiftGD_proof (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (hh : 0 ≤ h) : GaussData sd.Ss S.β sd.hEs where
  Ω₀ := gds.Ω₀
  P₀ := gds.P₀
  η := fun u ω => gds.η (h + u) ω
  B := fun u ω => gds.B (h + u) ω
  limit := shifted_limit_proof sd gds h hh
  B_meas := (shifted_wick_proof sd gds h hh).1
  B_wick := (shifted_wick_proof sd gds h hh).2.1
  B_L2 := fun Rw hRw a ha => by
    have := (shifted_wick_proof sd gds h hh).2.2 Rw hRw a ha
    exact this

theorem shift_procWin (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (T a : ℝ) :
    (fun ω : gds.Ω₀ => procWin (rLvl d) T a (fun u ω => gds.η (h + u) ω) ω) =
      fun ω : gds.Ω₀ => procWin (rLvl d) T (a + h) gds.η ω := by
  funext ω
  unfold procWin
  congr 1
  funext t ω
  show gds.η (h + (a + t)) ω = gds.η (a + h + t) ω
  rw [show h + (a + t) = a + h + t by ring]

theorem shift_Zwin (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (hh : 0 ≤ h) (T a : ℝ) :
    (shiftGD_proof sd gds h hh).Zwin T a = gds.Zwin T (a + h) := by
  show (fun ω : gds.Ω₀ => HRS.MD.EQInterp.epath (rLvl_le sd.hEs) T
      (procWin (rLvl d) T a (fun u ω => gds.η (h + u) ω) ω)) = gds.Zwin T (a + h)
  funext ω
  have := congrFun (shift_procWin sd gds h T a) ω
  unfold GaussData.Zwin
  rw [this]

theorem hρ_stat (sd : StatDatum S β₀ m hE) : ∀ t t' : ℝ, (regime sd.Ss S.β sd.hEs).ρ t = (regime sd.Ss S.β sd.hEs).ρ t' :=
  fun t t' => stat_rho_const sd t t'

end ShiftGD

section Tail

/-- The tail of the exponentially weighted integral, bounded by the unit blocks. -/
theorem tail_weighted_le (φ : ℝ → ℝ) (hφ0 : ∀ v, 0 ≤ φ v) (n : ℕ) (hφ : IntegrableOn φ (Set.Icc 0 (n : ℝ)))
    (c a h X : ℝ) (hc : 0 ≤ c) (hh : h ≤ n) :
    ∫ v in Set.Ioc 0 X ∩ Set.Iio h, Real.exp (-c * (a + h - v)) * φ v ≤
      Real.exp (-c * a) * ∑ k ∈ Finset.range n, Real.exp (-c * (h - ((k : ℝ) + 1))) *
        ∫ x in (k : ℝ)..((k : ℝ) + 1), φ x := by
  have hg : Continuous fun v : ℝ => Real.exp (-c * (a + h - v)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hfi : IntegrableOn (fun v => Real.exp (-c * (a + h - v)) * φ v) (Set.Ioc 0 h) := by
    refine (IntegrableOn.continuousOn_mul hg.continuousOn hφ isCompact_Icc).mono_set ?_
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hh)
  have s1 : ∫ v in Set.Ioc 0 X ∩ Set.Iio h, Real.exp (-c * (a + h - v)) * φ v ≤
      ∫ v in Set.Ioc 0 h, Real.exp (-c * (a + h - v)) * φ v := by
    refine setIntegral_mono_set hfi (Eventually.of_forall fun v => mul_nonneg (Real.exp_pos _).le (hφ0 v)) ?_
    refine HasSubset.Subset.eventuallyLE ?_
    intro v hv
    exact ⟨hv.1.1, hv.2.le⟩
  refine s1.trans ?_
  have e1 : ∫ v in Set.Ioc 0 h, Real.exp (-c * (a + h - v)) * φ v =
      Real.exp (-c * a) * ∫ v in Set.Ioc 0 h, Real.exp (-c * (h - v)) * φ v := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun v _ => ?_)
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e1]
  exact mul_le_mul_of_nonneg_left (HRS.MC.E213U11.u11_weighted_block φ hφ0 n hφ c h h hc hh) (Real.exp_pos _).le

end Tail

section DBound

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

theorem shift_D_bound (gds : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (h : ℝ) (hh : 0 ≤ h) (a : ℝ), 0 ≤ a → ∀ᵐ ω ∂gds.P₀,
      ‖gds.Dwin T (a + h) ω - (shiftGD_proof sd gds h hh).Dwin T a ω‖ ≤
        K * Real.exp (-c * a) * ∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) *
          ‖toL2 (rLvl d) 1 (fun t => gds.B ((k : ℝ) + t) ω)‖ := by
  obtain ⟨Cf, c, hCf, hc, hb⟩ := winDrift_shift_bound sd.hEs (hρ_stat sd) T hT
  refine ⟨Cf, c, hCf, hc, fun h hh a ha => ?_⟩
  have hn : (0 : ℝ) < (⌈h + T⌉₊ : ℝ) := by
    have : 0 < ⌈h + T⌉₊ := Nat.ceil_pos.2 (by linarith)
    exact_mod_cast this
  have hHn : h + T ≤ (⌈h + T⌉₊ : ℝ) := Nat.le_ceil _
  have hpos : 0 < a + h + T := by linarith
  filter_upwards [HRS.MC.E213U11.u11_B_integrable gds (a + h + T) hpos,
    HRS.MC.E213U11.u11_B_integrable gds (⌈h + T⌉₊ : ℝ) hn, HRS.MC.E213U11.u11_B_blocks gds] with ω hint hintn hblk
  have h1 := hb ha hh (fun v => gds.B v ω) (HRS.MC.E213U11.u11_B_nearCoef_measurable gds ω) hint
  have e1 : gds.Dwin T (a + h) ω = winDrift (regime sd.Ss S.β sd.hEs) m T (a + h) (add_nonneg ha hh)
      (fun v => NegSobolev.embed m (gds.B v ω)) 0 (a + h + T) := by
    unfold GaussData.Dwin
    rw [dif_pos (add_nonneg ha hh)]
  have e2 : (shiftGD_proof sd gds h hh).Dwin T a ω = winDrift (regime sd.Ss S.β sd.hEs) m T a ha
      (fun v => NegSobolev.embed m (gds.B (h + v) ω)) 0 (a + T) := by
    unfold GaussData.Dwin
    rw [dif_pos ha]
    rfl
  rw [e1, e2]
  refine h1.trans ?_
  have hφ0 : ∀ v, 0 ≤ ‖gds.B v ω‖ := fun v => norm_nonneg _
  have h2 := tail_weighted_le (fun v => ‖gds.B v ω‖) hφ0 ⌈h + T⌉₊ hintn c a h (a + h + T) hc.le (by linarith)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (h2.trans ?_) hCf.le
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (HRS.MC.E213U11.u11_block_integral_le (fun v => gds.B v ω) k (hblk k))
    (Real.exp_pos _).le

end DBound

end HRS.MC.E214N

end
