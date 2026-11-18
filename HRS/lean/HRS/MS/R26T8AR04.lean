import HRS.MS.R26T8AR03
import HRS.MS.S82P2Mar1

/-!
# S8.2 observed-time layer, packet T8A.R04: finite threshold field switch

The field `hh N` is replaced by `0` below a threshold `N0`. Since `deltaN N → 0`, the threshold can be chosen so that
`C * deltaN N ≤ 1` above it; then the switched field satisfies both the `C deltaN` bound and the bound by `1` for all
`N ≥ 2`, and it agrees eventually with `hh`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.MS.Phase2S82

/-- `deltaN N = (1 + log N) / N → 0` -/
theorem r26t8a_f04_deltaN_tendsto :
    Tendsto (fun N : ℕ => HRS.MS.Phase2S82.deltaN N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have h4 : Tendsto (fun N : ℕ => 1 / (N : ℝ) + Real.log N / (N : ℝ)) atTop (𝓝 ((0 : ℝ) + 0)) :=
    (h2.add h1).comp tendsto_natCast_atTop_atTop
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold HRS.MS.Phase2S82.deltaN HRS.MS.Phase2S82.logN
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0, Real.log_exp]
  field_simp

theorem r26t8a_field_switch {d : ℕ} (C : ℝ) (hC : 0 < C)
    (Ncal : ℕ) (hh : ℕ → Euc d → ℝ) (hhm : ∀ N, Measurable (hh N))
    (hhb : ∀ N, Ncal ≤ N → 2 ≤ N → ∀ x, |hh N x| ≤ C * HRS.MS.Phase2S82.deltaN N) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ Ncal ≤ N0 ∧
      let h := fun N x => if N0 ≤ N then hh N x else 0
      (∀ N, Measurable (h N)) ∧
      (∀ N, 2 ≤ N → ∀ x, |h N x| ≤ C * HRS.MS.Phase2S82.deltaN N ∧ |h N x| ≤ 1) ∧
      h =ᶠ[atTop] hh := by
  have hev : ∀ᶠ N : ℕ in atTop, HRS.MS.Phase2S82.deltaN N < 1 / C :=
    r26t8a_f04_deltaN_tendsto.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  refine ⟨max (max 2 Ncal) N1, le_trans (le_max_left 2 Ncal) (le_max_left _ _),
    le_trans (le_max_right 2 Ncal) (le_max_left _ _), ?_, ?_, ?_⟩
  · intro N
    dsimp only
    by_cases hN : max (max 2 Ncal) N1 ≤ N
    · simp only [if_pos hN]
      exact hhm N
    · simp only [if_neg hN]
      exact measurable_const
  · intro N hN2 x
    dsimp only
    by_cases hN : max (max 2 Ncal) N1 ≤ N
    · rw [if_pos hN]
      have hNc : Ncal ≤ N := le_trans (le_trans (le_max_right 2 Ncal) (le_max_left _ _)) hN
      have hb := hhb N hNc hN2 x
      have hsmall : C * HRS.MS.Phase2S82.deltaN N ≤ 1 := by
        have := hN1 N (le_trans (le_max_right _ _) hN)
        have h' := (lt_div_iff₀ hC).1 this
        linarith
      exact ⟨hb, hb.trans hsmall⟩
    · rw [if_neg hN]
      have hδ : 0 ≤ HRS.MS.Phase2S82.deltaN N := HRS.MS.S82P2.s82p2_deltaN_nonneg (by omega)
      simp only [abs_zero]
      exact ⟨mul_nonneg hC.le hδ, zero_le_one⟩
  · filter_upwards [eventually_ge_atTop (max (max 2 Ncal) N1)] with N hN
    funext x
    exact if_pos hN

end HRS.MS.R26T8A

end
