import HRS.Commutator.Torus.TLOWVAux5
import HRS.Commutator.Torus.NRSTAux49

/-!
# T-LOWV / T-INHOM: the unrenormalised commutator estimate in the form `TlowvNRS`

`TlowvNRS d s` is the statement of `nrs_T` (`External.lean`).  It is proved here by the same argument as
`nrs_T_generic`/`nrs_T_exceptional`/`nrs_T` of `External.lean`, but from the `NRSTAux` files directly, so that
`Layer.lean` can use it for `low_velocity_T` and `inhomogeneous_T` without importing `External.lean`
(which imports `Layer.lean`).  This file is imported by `Layer.lean` only after `NRSTAux18` no longer imports `Layer.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

theorem tlowv_nrs_generic (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hgen : ¬ ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k) : TlowvNRS d s := by
  unfold TlowvNRS
  obtain ⟨CB, hCB0, hmul⟩ := nrstr_hmul hd hs0 hsd
  set α : ℝ := ((d : ℝ) - s) / 2 with hα
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hfl0 : (⌊α⌋₊ : ℝ) ≤ α := Nat.floor_le hα0
  have hfl1 : α < (⌊α⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one α
  have hα1 : 1 < α := by rw [hα]; linarith
  have hσ0 : 0 < α - ⌊α⌋₊ := by
    rcases hfl0.lt_or_eq with h1 | h1
    · linarith
    · exfalso
      apply hgen
      refine ⟨⌊α⌋₊, ?_, ?_⟩
      · have : (1 : ℝ) < ⌊α⌋₊ := by rw [h1]; exact hα1
        exact_mod_cast this
      · have : (d : ℝ) - s = 2 * ⌊α⌋₊ := by rw [h1, hα]; ring
        linarith
  have hσ1 : α - ⌊α⌋₊ < 1 := by linarith
  have hd1 : 1 ≤ d := by omega
  refine NRST.nrst_main hd hs0 hsd (C0 := (d : ℝ) + ((d : ℝ) + 2 * (α - ⌊α⌋₊) + 2) / 2) (CB := CB)
    (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; positivity) hCB0
    (fun V hVr L hL0 hLip h _ => ?_) hmul
  exact nrstr_hbase hd1 hσ0 hσ1 V hVr hL0 hLip h

theorem tlowv_nrs_exceptional (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (hexc : ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k) : TlowvNRS d s := by
  unfold TlowvNRS
  obtain ⟨CB, hCB0, hmul⟩ := nrstr_hmul hd hs0 hsd
  obtain ⟨k, hk2, hsk⟩ := hexc
  have hα : ((d : ℝ) - s) / 2 = (k : ℝ) := by rw [hsk]; ring
  refine NRST.nrst_main hd hs0 hsd (C0 := (d : ℝ) / 2) (CB := CB) (by positivity) hCB0
    (fun V hVr L hL0 hLip h _ => ?_) hmul
  rw [hα, Nat.floor_natCast, sub_self]
  exact NRST.base_exceptional V hVr hL0 hLip h

/-- The statement of `nrs_T`, as `TlowvNRS`. -/
theorem tlowv_nrs (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) : TlowvNRS d s := by
  by_cases h : ∃ k : ℕ, 2 ≤ k ∧ s = (d : ℝ) - 2 * k
  · exact tlowv_nrs_exceptional hd hs0 hsd h
  · exact tlowv_nrs_generic hd hs0 hsd h

end HRS.Commutator.TorusNote
