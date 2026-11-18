import HRS.Torus.Basic

/-!
# Packet SF2 `sf2_shell_card` (lattice shell counting)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Imports only the repo module `HRS.Torus.Basic` (vocabulary: `Torus`, `Euc`, `Lattice`, `NonzeroLattice`, `summable_jp_rpow`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS

variable {d : ℕ}

/-- **SF2** (size S, about 60 lines).  Lattice shell counting: for `t > d` there is `C` with
`#{k ≠ 0 : ⟨k⟩ ≤ R} ≤ C R^t` for all `R > 0` (the set is finite).
Route: `C = ∑' k, ⟨k⟩^{-t}`, finite by `HRS.summable_jp_rpow` (`HRS/Torus/Basic.lean:872`, with `m = t/2`); each `k` in the set has
`⟨k⟩^{-t} ≥ R^{-t}`, so `card · R^{-t} ≤ ∑ ⟨k⟩^{-t}` (`Summable.sum_le_tsum`, `Set.Finite` from `Summable.tendsto_cofinite_zero`
or `Set.Finite.of_summable_const`). -/
theorem sf2_shell_card (t : ℝ) (ht : (d : ℝ) < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      {k : NonzeroLattice d | Lattice.jp k.1 ≤ R}.Finite ∧
        (({k : NonzeroLattice d | Lattice.jp k.1 ≤ R}).ncard : ℝ) ≤ C * R ^ t := by
  have hs : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-t) := by
    have h := summable_jp_rpow (d := d) (t / 2) (by linarith)
    have e2 : -(2 * (t / 2)) = -t := by ring
    simpa only [e2] using h
  have hjp : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := by
    intro k
    unfold Lattice.jp
    exact Real.sqrt_pos.mpr (by positivity)
  refine ⟨∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-t),
    tsum_nonneg fun k => Real.rpow_nonneg (hjp k).le _, fun R hR => ?_⟩
  have hpos : 0 < R ^ (-t) := Real.rpow_pos_of_pos hR _
  have hfin : {k : NonzeroLattice d | Lattice.jp k.1 ≤ R}.Finite := by
    have hev := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
    refine (Filter.eventually_cofinite.mp hev).subset ?_
    intro k hk
    show ¬ (Lattice.jp k.1 ^ (-t) < R ^ (-t))
    rw [not_lt]
    exact Real.rpow_le_rpow_of_nonpos (hjp k) (show Lattice.jp k.1 ≤ R from hk) (by linarith)
  refine ⟨hfin, ?_⟩
  have hsum : ∑ _k ∈ hfin.toFinset, R ^ (-t) ≤ ∑ k ∈ hfin.toFinset, Lattice.jp k.1 ^ (-t) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Set.Finite.mem_toFinset] at hk
    exact Real.rpow_le_rpow_of_nonpos (hjp k) hk (by linarith)
  have hle : ∑ k ∈ hfin.toFinset, Lattice.jp k.1 ^ (-t) ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-t) :=
    hs.sum_le_tsum _ (fun k _ => Real.rpow_nonneg (hjp k).le _)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hRt : 0 < R ^ t := Real.rpow_pos_of_pos hR t
  have hR' : R ^ (-t) * R ^ t = 1 := by
    rw [Real.rpow_neg hR.le, inv_mul_cancel₀ hRt.ne']
  have h3 := le_trans hsum hle
  calc (hfin.toFinset.card : ℝ) = (hfin.toFinset.card : ℝ) * R ^ (-t) * R ^ t := by
        rw [mul_assoc, hR', mul_one]
    _ ≤ (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-t)) * R ^ t :=
        mul_le_mul_of_nonneg_right h3 hRt.le

end HRS.MH.FilteredP
