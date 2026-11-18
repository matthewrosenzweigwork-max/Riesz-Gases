import HRS.Whole.Adjoint

/-!
# MS-BILIP-V, part 1: the lattice `s ℤ^d`

Nearest lattice point, finiteness of lattice points in a ball, and a uniform cardinality bound for the lattice
points in a ball of fixed radius around an arbitrary centre.  Route: `BilipVPlan.md`.
-/

noncomputable section

open Set

namespace HRS.MS.BilipV

variable {d : ℕ}

/-- the lattice point `s k`, `k ∈ ℤ^d` -/
def bv_pt (s : ℝ) (k : Fin d → ℤ) : HRS.Euc d := s • HRS.Whole.latticePt k

theorem bv_pt_apply (s : ℝ) (k : Fin d → ℤ) (i : Fin d) : bv_pt s k i = s * (k i : ℝ) := by
  simp [bv_pt, HRS.Whole.latticePt]

theorem bv_pt_sub (s : ℝ) (a b : Fin d → ℤ) : bv_pt s a - bv_pt s b = bv_pt s (a - b) := by
  ext i
  simp [bv_pt_apply, mul_sub]

theorem bv_round (c x : ℝ) (hc : 0 < c) : |x - c * round (x / c)| ≤ c / 2 := by
  have h := abs_sub_round (x / c)
  have e : x - c * round (x / c) = c * (x / c - round (x / c)) := by
    rw [mul_sub, mul_div_cancel₀ _ hc.ne']
  rw [e, abs_mul, abs_of_pos hc]
  nlinarith

/-- every point is within `d s / 2` of a lattice point -/
theorem bv_approx {s : ℝ} (hs : 0 < s) (p : HRS.Euc d) :
    ∃ k : Fin d → ℤ, ‖p - bv_pt s k‖ ≤ d * s / 2 := by
  refine ⟨fun i => round (p i / s), ?_⟩
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hi : ∀ i, ‖(p - bv_pt s fun i => round (p i / s)) i‖ ^ 2 ≤ (s / 2) ^ 2 := by
    intro i
    have h1 : (p - bv_pt s fun i => round (p i / s)) i = p i - s * round (p i / s) := by
      simp [bv_pt_apply]
    rw [h1, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (bv_round s (p i) hs) 2
  calc ∑ i, ‖(p - bv_pt s fun i => round (p i / s)) i‖ ^ 2 ≤ ∑ _i : Fin d, (s / 2) ^ 2 :=
        Finset.sum_le_sum fun i _ => hi i
    _ = d * (s / 2) ^ 2 := by simp
    _ ≤ (d * s / 2) ^ 2 := by
        have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) d
        have : (d * s / 2) ^ 2 = (d : ℝ) ^ 2 * (s / 2) ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hd (sq_nonneg _)

/-- finitely many lattice points in a ball about `0` -/
theorem bv_finite {s : ℝ} (hs : 0 < s) (R : ℝ) :
    {k : Fin d → ℤ | ‖bv_pt s k‖ ≤ R}.Finite := by
  refine (Finset.finite_toSet (Fintype.piFinset fun _ : Fin d => Finset.Icc (-⌈R / s⌉) ⌈R / s⌉)).subset ?_
  intro k hk
  simp only [mem_setOf_eq] at hk
  simp only [Finset.coe_sort_coe, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : |s * (k i : ℝ)| ≤ R := by
    have := PiLp.norm_apply_le (bv_pt s k) i
    rw [bv_pt_apply, Real.norm_eq_abs] at this
    exact this.trans hk
  rw [abs_mul, abs_of_pos hs] at h1
  have h2 : |(k i : ℝ)| ≤ R / s := by rw [le_div_iff₀ hs]; linarith
  have h3 : |(k i : ℝ)| ≤ (⌈R / s⌉ : ℝ) := h2.trans (Int.le_ceil _)
  have h4 : |k i| ≤ ⌈R / s⌉ := by exact_mod_cast h3
  exact abs_le.1 h4

/-- uniform cardinality bound -/
theorem bv_net {s : ℝ} (hs : 0 < s) (R : ℝ) :
    ∃ N : ℕ, ∀ z : HRS.Euc d, ∃ K : Finset (Fin d → ℤ), K.card ≤ N ∧
      ∀ k : Fin d → ℤ, ‖z - bv_pt s k‖ ≤ R → k ∈ K := by
  classical
  set J := (bv_finite (d := d) hs (R + d * s / 2)).toFinset with hJ
  refine ⟨J.card, fun z => ?_⟩
  obtain ⟨k0, hk0⟩ := bv_approx hs z
  refine ⟨J.image fun j => k0 + j, Finset.card_image_le, fun k hk => ?_⟩
  refine Finset.mem_image.2 ⟨k - k0, ?_, by simp⟩
  rw [hJ, Set.Finite.mem_toFinset, mem_setOf_eq, ← bv_pt_sub]
  calc ‖bv_pt s k - bv_pt s k0‖ = ‖(z - bv_pt s k0) - (z - bv_pt s k)‖ := by congr 1; abel
    _ ≤ ‖z - bv_pt s k0‖ + ‖z - bv_pt s k‖ := norm_sub_le _ _
    _ ≤ R + d * s / 2 := by linarith

end HRS.MS.BilipV
