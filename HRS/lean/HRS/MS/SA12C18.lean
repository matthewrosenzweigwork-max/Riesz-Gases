import HRS.MS.SA12C17

/-!
# S.A.12(c), packet E7.04 (part 2): a product cutoff killing the nonzero lattice points

`Ξ_L(z) = ∏_i θ(z_i/L)` with `θ = 1` on `[-3/5,3/5]`, `θ = 0` off `(-4/5,4/5)`: smooth, compactly supported,
`≡ 1` on `{|z_i| ≤ 3L/5}`, and `≡ 0` near every nonzero lattice point `L k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

def sa12cTheta : ContDiffBump (0 : ℝ) where
  rIn := 3 / 5
  rOut := 4 / 5
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def sa12cXi (d : ℕ) (L : ℝ) (z : Euc d) : ℝ := ∏ i : Fin d, sa12cTheta (z i / L)

theorem sa12cXi_contDiff (L : ℝ) : ContDiff ℝ ∞ (sa12cXi d L) := by
  unfold sa12cXi
  refine contDiff_prod fun i _ => ?_
  have h1 : ContDiff ℝ ∞ fun z : Euc d => z i / L :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff).div_const L
  exact sa12cTheta.contDiff.comp h1

theorem sa12cXi_one {L : ℝ} (hL : 0 < L) {z : Euc d} (hz : ∀ i, |z i| ≤ 3 * L / 5) : sa12cXi d L z = 1 := by
  unfold sa12cXi
  refine Finset.prod_eq_one fun i _ => ?_
  apply sa12cTheta.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hL, div_le_iff₀ hL]
  have := hz i
  show |z i| ≤ 3 / 5 * L
  linarith

theorem sa12cXi_zero_of {L : ℝ} (hL : 0 < L) {z : Euc d} (i : Fin d) (hi : 4 * L / 5 ≤ |z i|) :
    sa12cXi d L z = 0 := by
  unfold sa12cXi
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  apply sa12cTheta.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hL, le_div_iff₀ hL]
  show 4 / 5 * L ≤ |z i|
  linarith

theorem sa12cXi_support {L : ℝ} (hL : 0 < L) {z : Euc d} (hz : sa12cXi d L z ≠ 0) :
    ∀ i, |z i| < 4 * L / 5 := by
  intro i
  by_contra h
  exact hz (sa12cXi_zero_of hL i (not_lt.1 h))

theorem sa12cXi_zero_near_lattice {L : ℝ} (hL : 0 < L) {k : Fin d → ℤ} (hk : k ≠ 0) :
    ∀ᶠ z in 𝓝 (L • latticePt k : Euc d), sa12cXi d L z = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  filter_upwards [Metric.ball_mem_nhds (L • latticePt k : Euc d) (by linarith : (0 : ℝ) < L / 5)] with z hz
  apply sa12cXi_zero_of hL i
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 : |(z - L • latticePt k) i| ≤ ‖z - L • latticePt k‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (z - L • latticePt k) i
  have h2 : (z - L • latticePt k) i = z i - L * (k i : ℝ) := by simp [latticePt]
  rw [h2] at h1
  have h3 : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
    exact_mod_cast this
  have h4 : L * |(k i : ℝ)| ≤ |L * (k i : ℝ)| := by
    rw [abs_mul, abs_of_pos hL]
  have h5 : |L * (k i : ℝ)| ≤ |z i| + |z i - L * (k i : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (L * (k i : ℝ)) (z i)
    have h6 := abs_sub_comm (L * (k i : ℝ)) (z i)
    nlinarith [abs_nonneg (z i), abs_nonneg (L * (k i : ℝ))]
  nlinarith

theorem sa12cXi_compact (L : ℝ) (hL : 0 < L) : HasCompactSupport (sa12cXi d L) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (d * L)) fun z hz => ?_
  by_contra hne
  apply hz
  have hc := sa12cXi_support hL hne
  rw [Metric.mem_closedBall, dist_zero_right]
  have hcoord : ∀ i, z i ^ 2 ≤ L ^ 2 := fun i => by
    have := hc i
    have h1 : |z i| ≤ L := by linarith
    exact sq_le_sq' (by linarith [abs_le.1 h1]) (abs_le.1 h1).2
  have hsq : ‖z‖ ^ 2 ≤ ((d : ℝ) * L) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    calc ∑ i, z i ^ 2 ≤ ∑ _i : Fin d, L ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = d * L ^ 2 := by simp
      _ ≤ ((d : ℝ) * L) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with h | h
          · subst h; simp
          · have : (1 : ℝ) ≤ d := by exact_mod_cast h
            nlinarith [sq_nonneg L]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq

end HRS.MH.AdjointRd.Phase2SA12C
