import HRS.MC.S7S7dAux11
import HRS.MC.S7S7dAux2

/-!
# Packet `s7_S7d_uniform_limits`, helper 12: the `L^1` tail of `W_N` beyond a finite set of modes, uniformly in `N`

`∫ min(2, ‖W_N - truncE K W_N‖) dQ_N ≤ Σ_k b_k - Σ_{k∈K} b_k`, `b_k = c0 <k>^{-r}` summable.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_tsum_indicator {ι : Type*} [DecidableEq ι] {b : ι → ℝ} (hb : Summable b) (K : Finset ι) :
    ∑' k, (if k ∈ K then 0 else b k) = (∑' k, b k) - ∑ k ∈ K, b k := by
  have h1 : (∑' k, (if k ∈ K then b k else 0)) = ∑ k ∈ K, b k := by
    rw [tsum_eq_sum (s := K) (fun k hk => by simp [hk])]
    exact Finset.sum_congr rfl fun k hk => by simp [hk]
  have hs1 : Summable (fun k => if k ∈ K then b k else 0) :=
    summable_of_ne_finset_zero (s := K) fun k hk => by simp [hk]
  have hs2 : Summable (fun k => if k ∈ K then 0 else b k) := by
    have := hb.sub hs1
    refine this.congr fun k => ?_
    by_cases hk : k ∈ K <;> simp [hk]
  have h2 : ∑' k, b k = ∑' k, (if k ∈ K then b k else 0) + ∑' k, (if k ∈ K then 0 else b k) := by
    rw [← hs1.tsum_add hs2]
    refine tsum_congr fun k => ?_
    by_cases hk : k ∈ K <;> simp [hk]
  linarith

theorem s7d_tail_enorm [DecidableEq (NonzeroLattice d)] (K : Finset (NonzeroLattice d)) (x : NegSobolev d r) :
    ‖x - truncE K x‖ₑ ≤ ∑' k : NonzeroLattice d, (if k ∈ K then 0 else ‖NegSobolev.coord x k‖ₑ) := by
  classical
  have h := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by simp)
    (show lp (fun _ : NonzeroLattice d => ℝ) 2 from x - truncE K x)
  refine h.enorm_le_of_bounded (g := fun k => if k ∈ K then 0 else ‖NegSobolev.coord x k‖ₑ)
    ENNReal.summable.hasSum fun k => ?_
  have hn := lp.norm_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num) k
    ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from x - truncE K x) k)
  rw [← ofReal_norm_eq_enorm, hn, ofReal_norm_eq_enorm]
  have hc : ((show lp (fun _ : NonzeroLattice d => ℝ) 2 from x - truncE K x) k) =
      NegSobolev.coord x k - NegSobolev.coord (truncE K x) k := rfl
  rw [hc, coord_truncE]
  by_cases hk : k ∈ K <;> simp [hk]

end HRS.MC.Sec7.S7d

end
