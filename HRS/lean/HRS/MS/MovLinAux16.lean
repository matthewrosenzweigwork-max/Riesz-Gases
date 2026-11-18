import HRS.MS.MovLinAux15

/-!
# MOV-LIN, part 7: duality on the scale (`j` is self-adjoint up to relabelling; a duality criterion for `Σ^σ`)

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

* `movlin_j_inner`: `⟨j_{r→0} z, b⟩ = ⟨z, j_{0→-r} b⟩` for the `ℓ²` pairings (`r ≥ 0`).
* `movlin_dual_crit`: `u ∈ Σ^0` lies in `Σ^σ` (`σ ≥ 0`) with norm `≤ M` as soon as `|⟨u,y⟩| ≤ M ‖j_{0→-σ} y‖` for all `y`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

section Dual

/-- The `ℓ²` pairing of two elements of (possibly different levels of) the scale. -/
def movlin_pr {r s : ℝ} (x : OscSpace d r) (y : OscSpace d s) : ℝ :=
  inner ℝ (show lp (fun _ : MultiIndex d => ℝ) 2 from x) (show lp (fun _ : MultiIndex d => ℝ) 2 from y)

lemma movlin_pr_eq {r s : ℝ} (x : OscSpace d r) (y : OscSpace d s) :
    movlin_pr x y = ∑' α : MultiIndex d, OscSpace.coord y α * OscSpace.coord x α := by
  unfold movlin_pr
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun α => ?_
  simp [OscSpace.coord]

lemma movlin_pr_abs_le {r s : ℝ} (x : OscSpace d r) (y : OscSpace d s) :
    |movlin_pr x y| ≤ ‖x‖ * ‖y‖ := by
  unfold movlin_pr
  exact abs_real_inner_le_norm _ _

lemma movlin_pr_smul_right {r s : ℝ} (a : ℝ) (x : OscSpace d r) (y : OscSpace d s) :
    movlin_pr x (a • y) = a * movlin_pr x y := by
  unfold movlin_pr
  exact inner_smul_right _ _ _

lemma movlin_j_inner {r : ℝ} (hr : 0 ≤ r) (z : OscSpace d r) (b : OscSpace d 0) :
    movlin_pr (mov2d_j hr z) b = movlin_pr z (mov2d_j (neg_nonpos.2 hr) b) := by
  rw [movlin_pr_eq, movlin_pr_eq]
  refine tsum_congr fun α => ?_
  rw [mov2d_j_coord hr, mov2d_j_coord (neg_nonpos.2 hr)]
  ring

/-- **Duality criterion.**  If `|⟨u,y⟩| ≤ M ‖j_{0→-σ} y‖` for all `y ∈ Σ^0` (`σ ≥ 0`), then `u = j z` with
`z ∈ Σ^σ`, `‖z‖ ≤ M`. -/
lemma movlin_dual_crit {σ : ℝ} (hσ : 0 ≤ σ) (u : OscSpace d 0) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ y : OscSpace d 0, |movlin_pr u y| ≤ M * ‖mov2d_j (neg_nonpos.2 hσ) y‖) :
    ∃ z : OscSpace d σ, mov2d_j hσ z = u ∧ ‖z‖ ≤ M := by
  classical
  -- finite test vectors
  have key : ∀ F : Finset (MultiIndex d),
      ∑ α ∈ F, oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2 ≤ M ^ 2 := by
    intro F
    set c : MultiIndex d →₀ ℝ := Finsupp.onFinset F
      (fun α => if α ∈ F then oscEigenvalue d α ^ σ * OscSpace.coord u α else 0)
      (fun α hα => by by_contra hn; exact hα (by simp [hn])) with hc
    set y : OscSpace d 0 := mov2d_e d 0 c with hy
    have hcoord : ∀ α, OscSpace.coord y α = if α ∈ F then oscEigenvalue d α ^ σ * OscSpace.coord u α else 0 := by
      intro α
      rw [hy, mov2d_coord_e, hc, Finsupp.onFinset_apply]
      simp
    have hpr : movlin_pr u y = ∑ α ∈ F, oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2 := by
      rw [movlin_pr_eq, tsum_eq_sum (s := F)]
      · refine Finset.sum_congr rfl fun α hα => ?_
        rw [hcoord, if_pos hα]; ring
      · intro α hα
        rw [hcoord, if_neg hα, zero_mul]
    have hn : ‖mov2d_j (neg_nonpos.2 hσ) y‖ ^ 2 =
        ∑ α ∈ F, oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2 := by
      rw [OscSpace.norm_eq_coord, Real.sq_sqrt (tsum_nonneg fun α => sq_nonneg _),
        tsum_eq_sum (s := F)]
      · refine Finset.sum_congr rfl fun α hα => ?_
        have hL := oscEv_pos (d := d) α
        have hP : (oscEigenvalue d α ^ ((-σ - 0) / 2)) ^ 2 * oscEigenvalue d α ^ σ = 1 := by
          rw [rpow_half_sq _ _ hL, ← Real.rpow_add hL]; simp
        rw [mov2d_j_coord, hcoord, if_pos hα]
        calc (oscEigenvalue d α ^ ((-σ - 0) / 2) * (oscEigenvalue d α ^ σ * OscSpace.coord u α)) ^ 2
            = ((oscEigenvalue d α ^ ((-σ - 0) / 2)) ^ 2 * oscEigenvalue d α ^ σ) *
              (oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2) := by ring
          _ = _ := by rw [hP]; ring
      · intro α hα
        have hL := oscEv_pos (d := d) α
        rw [mov2d_j_coord, hcoord, if_neg hα]; simp
    set SF := ∑ α ∈ F, oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2 with hSF
    set n := ‖mov2d_j (neg_nonpos.2 hσ) y‖ with hnn
    have hn0 : 0 ≤ n := norm_nonneg _
    have h1 : SF ≤ M * n := by
      have := h y
      rw [hpr] at this
      exact (le_abs_self _).trans this
    have h2 : n ≤ M := by
      by_contra hlt
      push_neg at hlt
      have : n * n ≤ M * n := by nlinarith
      nlinarith
    calc SF = n ^ 2 := hn.symm
      _ ≤ M ^ 2 := pow_le_pow_left₀ hn0 h2 2
  have hnn : ∀ α : MultiIndex d, 0 ≤ oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2 := fun α =>
    mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  have hsum := summable_of_sum_le hnn key
  have hmem : Memℓp (fun α : MultiIndex d => oscEigenvalue d α ^ (σ / 2) * OscSpace.coord u α) 2 := by
    rw [memℓp_two_iff]
    refine hsum.congr fun α => ?_
    rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
  set z : OscSpace d σ := (⟨fun α => oscEigenvalue d α ^ (σ / 2) * OscSpace.coord u α, hmem⟩ :
    lp (fun _ : MultiIndex d => ℝ) 2) with hz
  refine ⟨z, ?_, ?_⟩
  · apply lp.ext
    funext α
    change OscSpace.coord (mov2d_j hσ z) α = OscSpace.coord u α
    rw [mov2d_j_coord hσ]
    have : OscSpace.coord z α = oscEigenvalue d α ^ (σ / 2) * OscSpace.coord u α := rfl
    rw [this, ← mul_assoc, ← Real.rpow_add (oscEv_pos α)]
    have e : (0 - σ) / 2 + σ / 2 = 0 := by ring
    rw [e, Real.rpow_zero, one_mul]
  · have hz2 : ‖z‖ ^ 2 = ∑' α : MultiIndex d, oscEigenvalue d α ^ σ * OscSpace.coord u α ^ 2 := by
      rw [OscSpace.norm_eq_coord, Real.sq_sqrt (tsum_nonneg fun α => sq_nonneg _)]
      refine tsum_congr fun α => ?_
      have hcz : OscSpace.coord z α = oscEigenvalue d α ^ (σ / 2) * OscSpace.coord u α := rfl
      rw [hcz]
      rw [mul_pow, rpow_half_sq _ _ (oscEv_pos α)]
    have : ‖z‖ ^ 2 ≤ M ^ 2 := by
      rw [hz2]; exact Real.tsum_le_of_sum_le hnn key
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM two_ne_zero).1 this

end Dual

end HRS.MS.MovLin
