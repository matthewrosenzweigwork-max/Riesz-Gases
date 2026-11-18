import HRS.MC.E214N8

/-!
# E214N9: pointwise bound of `J_{a+h} - J^{(h)}_a`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem winJ_congr_coef (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) {z z' : ℝ → NegSobolev d m} {I : Set ℝ}
    (hIm : MeasurableSet I) (hzz : ∀ u ∈ I, 0 ≤ u → z u = z' u) :
    winJ R m T a ha z I = winJ R m T a ha z' I := by
  unfold winJ
  rw [HRS.MC.E213U11.u11_jTensor_congr R m (a + T) hIm hzz]

section JBound

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

theorem shift_J_bound (gds : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (h : ℝ) (hh : 0 ≤ h) (a : ℝ), 0 ≤ a → ∀ᵐ ω ∂gds.P₀,
      ‖gds.Jwin T (a + h) ω - (shiftGD_proof sd gds h hh).Jwin T a ω‖ ≤
        K * Real.exp (-c * a) * ∑ k ∈ Finset.range ⌈h + T⌉₊, Real.exp (-c * (h - ((k : ℝ) + 1))) *
          ‖procWin (rLvl d) 1 (k : ℝ) gds.η ω‖ := by
  obtain ⟨Cf, c, hCf, hc, hb⟩ := winJ_shift_bound sd.hEs (hρ_stat sd) T hT
  refine ⟨Cf, c, hCf, hc, fun h hh a ha => ?_⟩
  have ha' : 0 ≤ a + h := add_nonneg ha hh
  set L : ℝ := a + h + T + 1 with hL
  have hL0 : (0 : ℝ) ≤ L := by rw [hL]; linarith
  filter_upwards [HRS.MC.E213U11.u11_eta_cont gds L] with ω hc0
  have hc0' : ContinuousOn (fun t => gds.η t ω) (Set.Icc 0 (0 + L)) := by simpa using hc0
  set w := procWin (rLvl d) L 0 gds.η ω with hw
  set zr : ℝ → NegSobolev d (rLvl d) := HRS.MC.E213U11.u11_cp hL0 w with hzr
  have hcpv : ∀ v ∈ Set.Icc (0 : ℝ) L, zr v = gds.η v ω := fun v hv => by
    rw [hzr, HRS.MC.E213U11.u11_cp_of_mem hL0 w hv, hw,
      HRS.MC.E213U11.u11_procWin_at gds.η L 0 ω hc0' hL0 ⟨v, hv⟩]
    simp
  have e1 : gds.Jwin T (a + h) ω = winJ (regime sd.Ss S.β sd.hEs) m T (a + h) ha'
      (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + h + T)) := by
    unfold GaussData.Jwin
    rw [dif_pos ha']
    refine winJ_congr_coef _ m T (a + h) ha' measurableSet_Ioc (fun u hu hu0 => ?_)
    show NegSobolev.embed m (gds.η u ω) = NegSobolev.embed m (zr u)
    rw [hcpv u ⟨hu0, by rw [hL]; linarith [hu.2]⟩]
  have e2 : (shiftGD_proof sd gds h hh).Jwin T a ω = winJ (regime sd.Ss S.β sd.hEs) m T a ha
      (fun v => NegSobolev.embed m (zr (h + v))) (Set.Ioc 0 (a + T)) := by
    unfold GaussData.Jwin
    rw [dif_pos ha]
    refine winJ_congr_coef _ m T a ha measurableSet_Ioc (fun u hu hu0 => ?_)
    show NegSobolev.embed m (gds.η (h + u) ω) = NegSobolev.embed m (zr (h + u))
    rw [hcpv (h + u) ⟨by linarith, by rw [hL]; linarith [hu.2]⟩]
  rw [e1, e2]
  refine (hb ha hh zr (HRS.MC.E213U11.u11_cp_continuous hL0 w) ‖w‖
    (HRS.MC.E213U11.u11_cp_norm_le hL0 w)).trans ?_
  have hφc : Continuous fun v => ‖zr v‖ := (HRS.MC.E213U11.u11_cp_continuous hL0 w).norm
  have hHn : h + T ≤ (⌈h + T⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈h + T⌉₊ : ℝ) < h + T + 1 := Nat.ceil_lt_add_one (by linarith)
  have h2 := tail_weighted_le (fun v => ‖zr v‖) (fun v => norm_nonneg _) ⌈h + T⌉₊ hφc.integrableOn_Icc c a h
    (a + h + T) hc.le (by linarith)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (h2.trans ?_) hCf.le
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hk1 : (k : ℝ) + 1 ≤ ⌈h + T⌉₊ := by exact_mod_cast Finset.mem_range.1 hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hckk : ContinuousOn (fun t => gds.η t ω) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) :=
    hc0.mono (Set.Icc_subset_Icc hk0 (by rw [hL]; linarith))
  have hbl : ∀ x ∈ Set.uIoc (k : ℝ) ((k : ℝ) + 1),
      ‖(fun v => ‖zr v‖) x‖ ≤ ‖procWin (rLvl d) 1 (k : ℝ) gds.η ω‖ := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxL : x ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [hx.1], by rw [hL]; linarith [hx.2]⟩
    simp only [norm_norm]
    rw [hcpv x hxL]
    exact HRS.MC.E213U11.u11_procWin_norm_ge gds.η 1 (k : ℝ) ω hckk zero_le_one ⟨hx.1.le, hx.2⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbl
  rw [abs_of_nonneg (by linarith), show (k : ℝ) + 1 - k = 1 by ring, mul_one] at this
  exact (Real.le_norm_self _).trans this

end JBound

end HRS.MC.E214N

end
