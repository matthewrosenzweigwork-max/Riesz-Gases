/-
# HRS.Equilibrium.L49Aux4 — Proposition 4.9, part 4: the compensated integral on `ℝ^d`

`l49_local_abstract`: the abstract form of `R:eq:compensated-integral`
`∫ H(λ g) ρ = (|S^{d-1}|/(2s)) ρ(x) λ² log(1/λ) + O(λ²)`, for any measurable `γ ≥ 0` with
`γ(w) = |w|^{-s} + O(1)` near `0` and bounded away from `0` in the cube.
-/
import HRS.Equilibrium.L49Aux3

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

open HRS.LocalDivAux

variable {d : ℕ}

theorem l49_rpow_facts {s t : ℝ} (hs1 : 1 ≤ s) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ t ^ (-s) ∧ 1 ≤ t * t ^ (-s) ∧ t ^ (-(2 * s)) = (t ^ (-s)) ^ 2 ∧
      t ^ (-(2 * s - 1)) = t * (t ^ (-s)) ^ 2 ∧ t ^ (-(3 * s)) = (t ^ (-s)) ^ 3 := by
  have hs0 : 0 < s := by linarith
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith), ?_, ?_, ?_, ?_⟩
  · have : t * t ^ (-s) = t ^ (1 - s) := by
      rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_one]
    rw [this]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    have : t * t ^ ((-s) * ((2 : ℕ) : ℝ)) = t ^ (1 + (-s) * ((2 : ℕ) : ℝ)) := by
      rw [Real.rpow_add ht0, Real.rpow_one]
    rw [this]; congr 1; push_cast; ring
  · rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
theorem l49_pt_inner {s t gam rw R Lam lam rl : ℝ} (hs1 : 1 ≤ s) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hlam0 : 0 < lam) (hg0 : 0 ≤ gam) (hgu : |gam - t ^ (-s)| ≤ R) (hR : 0 ≤ R)
    (hLam : 0 ≤ Lam) (hrw : 0 ≤ rw) (hrwL : rw ≤ Lam) :
    |rw * taylorH (lam * gam)| ≤ Lam * (1 + R) * lam * t ^ (-s) := by
  obtain ⟨hu1, -⟩ := l49_rpow_facts hs1 ht0 ht1
  have := l49_pointwise_inner hu1 hlam0 hg0 hgu hR hrw hrwL hLam
  calc _ ≤ _ := this
    _ = _ := by ring

set_option maxHeartbeats 800000 in
theorem l49_pt_outer {s t gam rw r0 R L Lam lam rl : ℝ} (hs1 : 1 ≤ s) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hrl0 : 0 < rl) (hrls : rl ^ s = lam) (hrt : rl < t)
    (hg0 : 0 ≤ gam) (hgu : |gam - t ^ (-s)| ≤ R) (hR : 0 ≤ R)
    (hL : 0 ≤ L) (hLam : 0 ≤ Lam)
    (hrw : 0 ≤ rw) (hrwL : rw ≤ Lam) (hr0 : 0 ≤ r0) (hr0L : r0 ≤ Lam)
    (hrr : |rw - r0| ≤ L * t) :
    |rw * taylorH (lam * gam) - r0 * (lam ^ 2 / 2) * t ^ (-(2 * s))| ≤
      (L * (1 + R ^ 2) + Lam * (4 * R ^ 3 + R + R ^ 2 / 2)) * lam ^ 2 * t ^ (-(2 * s - 1)) +
        4 * Lam * lam ^ 3 * t ^ (-(3 * s)) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨hu1, htu, e2, e21, e3⟩ := l49_rpow_facts hs1 ht0 ht1
  have hlu : lam * t ^ (-s) < 1 := by
    have h1 : t ^ (-s) < rl ^ (-s) := Real.rpow_lt_rpow_of_neg hrl0 hrt (by linarith)
    have h2 : rl ^ (-s) = lam⁻¹ := by rw [Real.rpow_neg hrl0.le, hrls]
    rw [h2] at h1
    have := mul_lt_mul_of_pos_left h1 hlam0
    rwa [mul_inv_cancel₀ hlam0.ne'] at this
  have key := l49_pointwise_near hu1 htu ht0 hlam0 hlam1 hg0 hgu hR hL hLam hrw hrwL hr0 hr0L hrr hlu
  rw [e2, e21, e3]
  calc _ = |rw * taylorH (lam * gam) - r0 * (lam ^ 2 * (t ^ (-s)) ^ 2 / 2)| := by ring_nf
    _ ≤ _ := key
    _ = _ := by ring

end L49

end HRS

end
