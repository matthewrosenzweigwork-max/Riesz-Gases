import HRS.MS.S82P2Mom

/-!
# S8.2 (S82P2): one-coordinate disintegration of the weak reference law, exponent algebra
Peeling coordinate `i` off `referenceLaw q h mu beta N (m+1) pins` produces the one-site tilt
`g` times `referenceExponent` for `m` coordinates with the extra pin `z = X i`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The exponent of the one peeled coordinate. -/
def s82p2_site {d p : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d) (z : Euc d) : ℝ :=
  beta * HRS.Whole.convMeasure q mu z + h N z - (beta / N) * ∑ j, q (z - pins j)

lemma s82p2_conv_measurable {d : ℕ} {q : Euc d → ℝ} (hq : Measurable q)
    (mu : Measure (Euc d)) [SFinite mu] : Measurable (HRS.Whole.convMeasure q mu) := by
  unfold HRS.Whole.convMeasure
  have : Measurable (fun p : Euc d × Euc d => q (p.1 - p.2)) :=
    hq.comp (measurable_fst.sub measurable_snd)
  exact this.stronglyMeasurable.integral_prod_right'.measurable

lemma s82p2_exponent_measurable {d p n : ℕ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    {mu : Measure (Euc d)} [SFinite mu] (hq : Measurable q) (beta : ℝ) (N : ℕ)
    (hh : Measurable (h N)) (pins : Fin p → Euc d) :
    Measurable (referenceExponent q h mu beta N pins : EucConfig d n → ℝ) := by
  unfold referenceExponent Phase2S82.pairSum
  have hc := s82p2_conv_measurable hq mu
  refine Measurable.sub (Measurable.sub ?_ ?_) ?_
  · exact Finset.measurable_sum _ fun i _ =>
      (measurable_const.mul (hc.comp (measurable_pi_apply i))).add (hh.comp (measurable_pi_apply i))
  · exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => hq.comp ((measurable_pi_apply i).sub (measurable_pi_apply j)))
  · exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => hq.comp ((measurable_pi_apply i).sub measurable_const))

lemma s82p2_sum_erase {m : ℕ} (f : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j : Fin m, f (i.succAbove j) := by
  have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have h2 := Fin.sum_univ_succAbove f i
  linarith

lemma s82p2_sum_erase_succAbove {m : ℕ} (f : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (j : Fin m) :
    ∑ l ∈ Finset.univ.erase (i.succAbove j), f l =
      f i + ∑ l ∈ Finset.univ.erase j, f (i.succAbove l) := by
  have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ (i.succAbove j))
  have h2 := Fin.sum_univ_succAbove f i
  have h3 := Finset.add_sum_erase Finset.univ (fun l => f (i.succAbove l)) (Finset.mem_univ j)
  linarith

lemma s82p2_pairSum_insertNth {d m : ℕ} {q : Euc d → ℝ} (hqe : ∀ z, q (-z) = q z)
    (i : Fin (m + 1)) (z : Euc d) (X' : Fin m → Euc d) :
    Phase2S82.pairSum (fun x y => q (x - y)) (i.insertNth z X' : EucConfig d (m + 1)) =
      2 * ∑ j, q (z - X' j) + Phase2S82.pairSum (fun x y => q (x - y)) X' := by
  have hsym : ∀ a b : Euc d, q (a - b) = q (b - a) := fun a b => by
    rw [← hqe (b - a), neg_sub]
  unfold Phase2S82.pairSum
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [s82p2_sum_erase (fun l => q (z - (i.insertNth z X' : EucConfig d (m + 1)) l)) i]
  simp only [Fin.insertNth_apply_succAbove]
  have : ∀ j : Fin m, ∑ l ∈ Finset.univ.erase (i.succAbove j),
      q (X' j - (i.insertNth z X' : EucConfig d (m + 1)) l) =
      q (X' j - z) + ∑ l ∈ Finset.univ.erase j, q (X' j - X' l) := by
    intro j
    rw [s82p2_sum_erase_succAbove (fun l => q (X' j - (i.insertNth z X' : EucConfig d (m + 1)) l)) i j]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [this, Finset.sum_add_distrib]
  have h2 : ∑ j, q (X' j - z) = ∑ j, q (z - X' j) := Finset.sum_congr rfl fun j _ => hsym _ _
  rw [h2]
  ring

lemma s82p2_exponent_insertNth {d p m : ℕ} {q : Euc d → ℝ} (hqe : ∀ z, q (-z) = q z)
    (h : ℕ → Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (i : Fin (m + 1)) (z : Euc d) (X' : Fin m → Euc d) :
    referenceExponent q h mu beta N pins (i.insertNth z X' : EucConfig d (m + 1)) =
      s82p2_site q h mu beta N pins z +
        referenceExponent q h mu beta N (Fin.cons z pins : Fin (p + 1) → Euc d) X' := by
  have hsym : ∀ a b : Euc d, q (a - b) = q (b - a) := fun a b => by
    rw [← hqe (b - a), neg_sub]
  unfold referenceExponent s82p2_site
  rw [s82p2_pairSum_insertNth hqe]
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove (fun k => ∑ j, q ((i.insertNth z X' : EucConfig d (m + 1)) k - pins j)) i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib]
  have h2 : ∀ j, q (X' j - z) = q (z - X' j) := fun j => hsym _ _
  simp only [h2]
  have h3 : (beta / (2 * N)) * (2 * ∑ j, q (z - X' j)) = (beta / N) * ∑ j, q (z - X' j) := by
    rcases eq_or_ne (N : ℝ) 0 with hN | hN
    · simp [hN]
    · field_simp
  rw [mul_add (beta / (2 * (N : ℝ))), h3]
  ring

end HRS.MS.S82P2
