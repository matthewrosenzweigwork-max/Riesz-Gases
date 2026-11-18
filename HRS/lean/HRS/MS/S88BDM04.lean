import HRS.MS.S88BDDefs
import HRS.Whole.Orbits

/-!
# S8.8.M04: the full time supremum equals the rational-time supremum

`s88_sup_eq_rational`: if every coordinate is continuous in `t ∈ [0,T]` then the supremum over `[0,T]` of the extended
`ℓ²` norm equals its supremum over the rational times.  For a finite set `F` of coordinates, `t ↦ ∑_{α∈F} Y_t(α)²` is
continuous on `[0,T]`, the rationals of `[0,T]` are dense in it (`T > 0`), so the bound `≤ R²` passes from rational times to
all times; then `ℓ²` is the supremum over finite `F`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

lemma s88_rat_closure (T : ℝ) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    t ∈ closure {x : ℝ | x ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = x} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hne : max 0 (t - ε) < min T (t + ε) := by
    refine max_lt_iff.2 ⟨lt_min_iff.2 ⟨hT, by linarith [ht.1]⟩, lt_min_iff.2 ⟨by linarith [ht.2], by linarith⟩⟩
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open (isOpen_Ioo (a := max 0 (t - ε))
    (b := min T (t + ε))) (Set.nonempty_Ioo.2 hne)
  have h1 := max_lt_iff.1 hq.1
  have h2 := lt_min_iff.1 hq.2
  refine ⟨(q : ℝ), ⟨⟨h1.1.le, h2.1.le⟩, q, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.2, h2.2]

theorem s88_sup_eq_rational {κ : Type*} [Countable κ] (T : ℝ) (hT : 0 < T)
    (Y : ℝ → κ → ℝ)
    (hcont : ∀ α : κ, ContinuousOn (fun t : ℝ => Y t α) (Set.Icc (0 : ℝ) T)) :
    (⨆ t : Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (Y t.1)) =
      ⨆ t : S88RatTime T, HRS.Whole.l2NormE (Y t.1) := by
  refine le_antisymm ?_ (iSup_le fun q => le_iSup_of_le ⟨q.1, q.2.1⟩ le_rfl)
  set R : ℝ≥0∞ := ⨆ t : S88RatTime T, HRS.Whole.l2NormE (Y t.1) with hR
  have hsq : ∀ x : ℝ, HRS.Whole.l2NormE (Y x) ^ 2 = ∑' α, ENNReal.ofReal (Y x α ^ 2) := by
    intro x
    unfold HRS.Whole.l2NormE
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  refine iSup_le fun t => ?_
  have htT := t.2
  -- the squared norm is at most `R^2`
  have hbound : ∑' α, ENNReal.ofReal (Y t.1 α ^ 2) ≤ R ^ 2 := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => ?_
    have hf : ContinuousOn (fun x : ℝ => ENNReal.ofReal (∑ α ∈ F, Y x α ^ 2)) (Set.Icc (0 : ℝ) T) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (continuousOn_finsetSum _ fun α _ => (hcont α).pow 2)
    have := ContinuousWithinAt.closure_le (s := {x : ℝ | x ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = x})
      (f := fun x : ℝ => ENNReal.ofReal (∑ α ∈ F, Y x α ^ 2)) (g := fun _ => R ^ 2)
      (s88_rat_closure T hT htT)
      ((hf t.1 htT).mono fun x hx => hx.1) continuousWithinAt_const (fun x hx => ?_)
    · rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => sq_nonneg _)] at this
      exact this
    · obtain ⟨hxI, hxq⟩ := hx
      have hxR : HRS.Whole.l2NormE (Y x) ≤ R := le_iSup (fun q : S88RatTime T =>
        HRS.Whole.l2NormE (Y q.1)) ⟨x, hxI, hxq⟩
      calc ENNReal.ofReal (∑ α ∈ F, Y x α ^ 2) = ∑ α ∈ F, ENNReal.ofReal (Y x α ^ 2) :=
            ENNReal.ofReal_sum_of_nonneg (fun α _ => sq_nonneg _)
        _ ≤ ∑' α, ENNReal.ofReal (Y x α ^ 2) := ENNReal.sum_le_tsum F
        _ = HRS.Whole.l2NormE (Y x) ^ 2 := (hsq x).symm
        _ ≤ R ^ 2 := pow_le_pow_left' hxR 2
  calc HRS.Whole.l2NormE (Y t.1) = (∑' α, ENNReal.ofReal (Y t.1 α ^ 2)) ^ (1 / 2 : ℝ) := rfl
    _ ≤ (R ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = R := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

end HRS.MS.S88Breakdown
