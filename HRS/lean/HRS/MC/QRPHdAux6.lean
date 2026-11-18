import HRS.MC.QRPHdAux2

/-!
# Packet HD, part 6: lattice sums of the squared differences `D(α,λ)² = ‖q α - q(α+λ)‖²`

* `hd_tailA`: for `L ≥ 2|λ|`, `L ≥ 1`: `∑_{|α|_∞ > L} D² ≤ C |λ|² L^{-(d-2s)}`.
* `hd_totalB`: `∑_α D² ≤ C |λ|^{1+2s}` (all `α`, including the singular ones).
-/

noncomputable section

open Finset
open scoped BigOperators

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ}

/-- `D(α,λ) = ‖q α - q (α+λ)‖`. -/
def hdD (d : ℕ) (s : ℝ) (lam α : Lattice d) : ℝ := ‖hdq d s α - hdq d s (α + lam)‖

open Classical in
/-- the tail summand: `D²` outside the cube `{|α|_∞ ≤ L}`. -/
def hdS1 (d : ℕ) (s : ℝ) (lam : Lattice d) (L : ℕ) (α : Lattice d) : ℝ :=
  if ∀ i, |α i| ≤ (L : ℤ) then 0 else hdD d s lam α ^ 2

theorem hdD_nonneg (s : ℝ) (lam α : Lattice d) : 0 ≤ hdD d s lam α := norm_nonneg _

theorem hd_enorm_ge_of_out {L : ℕ} {α : Lattice d} (h : ¬ ∀ i, |α i| ≤ (L : ℤ)) :
    (L : ℝ) ≤ Lattice.enorm α := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 : (L : ℝ) ≤ |(α i : ℝ)| := by
    have : ((L : ℤ) : ℝ) ≤ ((|α i| : ℤ) : ℝ) := by exact_mod_cast hi.le
    simpa using this
  have h6 : ‖(Lattice.toEuc α) i‖ ≤ ‖Lattice.toEuc α‖ := PiLp.norm_apply_le _ i
  have h7 : ‖(Lattice.toEuc α) i‖ = |(α i : ℝ)| := by simp [Lattice.toEuc]
  unfold Lattice.enorm
  linarith

/-- The squared bound for `α` far from the origin. -/
theorem hdD_sq_far {s : ℝ} (hs : s < d) {α lam : Lattice d} (hα : α ≠ 0)
    (h2 : 2 * Lattice.enorm lam ≤ Lattice.enorm α) :
    hdD d s lam α ^ 2 ≤ (|hdκ d s| * (1 + 3 * |s - (d : ℝ)|) * 2 ^ ((d : ℝ) - s)) ^ 2 *
      Lattice.enorm lam ^ 2 * Lattice.enorm α ^ (-(d : ℝ) - ((d : ℝ) - 2 * s)) := by
  have h := hdq_diff_le hs hα h2
  have hpos := hd_enorm_pos hα
  set C1 := |hdκ d s| * (1 + 3 * |s - (d : ℝ)|) * 2 ^ ((d : ℝ) - s) with hC1
  have hD0 := hdD_nonneg s lam α
  have hsq : hdD d s lam α ^ 2 ≤ (C1 * Lattice.enorm lam * Lattice.enorm α ^ (s - (d : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hD0 h 2
  refine hsq.trans (le_of_eq ?_)
  have e : Lattice.enorm α ^ (-(d : ℝ) - ((d : ℝ) - 2 * s)) =
      Lattice.enorm α ^ (s - (d : ℝ)) * Lattice.enorm α ^ (s - (d : ℝ)) := by
    rw [← Real.rpow_add hpos]; congr 1; ring
  rw [e]; ring

theorem hdq_sq_le {s : ℝ} (c : Lattice d) (hc : c ≠ 0) (hd1 : 1 ≤ d) :
    ‖hdq d s c‖ ^ 2 ≤ hdκ d s ^ 2 * Lattice.enorm c ^ (1 + 2 * s - (d : ℝ)) := by
  have hpos := hd_enorm_pos hc
  have hge := hd_enorm_ge_one hc
  rw [hdq_norm s hc, mul_pow, sq_abs]
  have e : (Lattice.enorm c ^ (s - (d : ℝ) + 1)) ^ 2 = Lattice.enorm c ^ (2 * (s - (d : ℝ) + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]; norm_num; ring_nf
  rw [e]
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hge (by linarith)) (sq_nonneg _)

end HRS.MC.QRSpec.Hd

end
