import HRS.MS.SobEmbAux5

/-!
# SA1, Aux6: the sup-norm embedding `W^{m+j+1,a₀} ↪ C_b^m`

`sa1_ReachInf a₀ j`: `‖D^i f x‖ ≤ C_i Σ_{t ≤ j} ‖D^{i+t} f‖_{a₀}`.  From `Reach a₀ j q` with `q > d` and Morrey's inequality
(`sa1_morrey`), `ReachInf a₀ (j+1)` follows; `sa1_glue_inf` turns it into a bound of `HRS.cbNorm m f` by
`HRS.Whole.sobolevWNorm (m+j) a₀ f`.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open scoped ENNReal NNReal ContDiff

namespace HRS.SA1

variable {d : ℕ}

/-- `‖D^i f x‖ ≤ C_i Σ_{t ≤ j} ‖D^{i+t} f‖_{a₀}` for all smooth `f` and all points. -/
def sa1_ReachInf (d : ℕ) (a0 : ℝ) (j : ℕ) : Prop :=
  ∀ i : ℕ, ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f → ∀ x,
    ‖iteratedFDeriv ℝ i f x‖ₑ ≤ C * ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f

theorem sa1_reachInf_of_reach (hd : 1 ≤ d) {a0 q : ℝ} {j : ℕ} (hq : (d : ℝ) < q)
    (hR : sa1_Reach d a0 j q) : sa1_ReachInf d a0 (j + 1) := by
  intro i
  obtain ⟨K, hK⟩ := sa1_morrey (F := ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin d)) ℝ)
    hd hq
  obtain ⟨C0, hC0⟩ := hR i
  obtain ⟨C1, hC1⟩ := hR (i + 1)
  refine ⟨K * (C0 + C1), fun f hf x => ?_⟩
  have h1 := hK (iteratedFDeriv ℝ i f) ((sa1_smooth_iter hf i).of_le (by simp)) x
  rw [sa1_nrm_succ hf] at h1
  have hs0 : ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f ≤
      ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f :=
    Finset.sum_le_sum_of_subset (f := fun t => sa1_nrm (i + t) a0 f) (Finset.range_mono (Nat.le_succ _))
  have hs1 : ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + 1 + t) a0 f ≤
      ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f := by
    rw [Finset.sum_range_succ' (fun t => sa1_nrm (i + t) a0 f) (j + 1)]
    refine le_trans (le_of_eq ?_) le_self_add
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show i + 1 + t = i + (t + 1) by ring]
  have e0 := hC0 f hf
  have e1 := hC1 f hf
  calc ‖iteratedFDeriv ℝ i f x‖ₑ ≤ K * (sa1_nrm i q f + sa1_nrm (i + 1) q f) := h1
    _ ≤ K * (C0 * ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f +
          C1 * ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f) := by
        gcongr
        · exact e0.trans (by gcongr)
        · exact e1.trans (by gcongr)
    _ = ((K * (C0 + C1) : ℝ≥0) : ℝ≥0∞) * ∑ t ∈ Finset.range (j + 1 + 1), sa1_nrm (i + t) a0 f := by
        push_cast; ring

theorem sa1_glue_inf {a0 : ℝ} (ha0 : 0 < a0) {j : ℕ} (hR : sa1_ReachInf d a0 j) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ f →
      (∀ i ≤ m + j, Integrable (fun x => ‖iteratedFDeriv ℝ i f x‖ ^ a0)) →
      HRS.cbNorm m f ≤ C * HRS.Whole.sobolevWNorm (m + j) a0 f := by
  choose C hC using hR
  refine ⟨∑ i ∈ Finset.range (m + 1), (C i : ℝ), Finset.sum_nonneg fun i _ => (C i).2, fun f hf hint => ?_⟩
  have hfin : ∀ i ≤ m + j, sa1_nrm i a0 f ≠ ⊤ ∧ (sa1_nrm i a0 f).toReal = sa1_T i a0 f :=
    fun i hi => sa1_nrm_of_integrable hf ha0 (hint i hi)
  have hS : 0 ≤ HRS.Whole.sobolevWNorm (m + j) a0 f :=
    Finset.sum_nonneg fun i _ => sa1_T_nonneg i a0 f
  have hpt : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ (C i : ℝ) * HRS.Whole.sobolevWNorm (m + j) a0 f := by
    intro i him x
    have hsumfin : ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 fun t ht => lt_top_iff_ne_top.2
        (hfin (i + t) (by have := Finset.mem_range.1 ht; omega)).1).ne
    have hle := hC i f hf x
    have hne : (C i : ℝ≥0∞) * ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hsumfin
    have h2 : ‖iteratedFDeriv ℝ i f x‖ ≤ (C i : ℝ) * ∑ t ∈ Finset.range (j + 1), sa1_T (i + t) a0 f := by
      calc ‖iteratedFDeriv ℝ i f x‖ = (‖iteratedFDeriv ℝ i f x‖ₑ).toReal := (toReal_enorm _).symm
        _ ≤ ((C i : ℝ≥0∞) * ∑ t ∈ Finset.range (j + 1), sa1_nrm (i + t) a0 f).toReal :=
            ENNReal.toReal_mono hne hle
        _ = (C i : ℝ) * ∑ t ∈ Finset.range (j + 1), sa1_T (i + t) a0 f := by
            rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
              ENNReal.toReal_sum (fun t ht => (hfin (i + t) (by have := Finset.mem_range.1 ht; omega)).1)]
            congr 1
            refine Finset.sum_congr rfl fun t ht => ?_
            exact (hfin (i + t) (by have := Finset.mem_range.1 ht; omega)).2
    refine h2.trans ?_
    rw [sa1_sob_eq]
    exact mul_le_mul_of_nonneg_left (sa1_sum_shift (fun j => sa1_T j a0 f) (fun j => sa1_T_nonneg j a0 f) i j m him)
      (C i).2
  unfold HRS.cbNorm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have him : i ≤ m := by have := Finset.mem_range.1 hi; omega
  exact ciSup_le fun x => hpt i him x

end HRS.SA1
