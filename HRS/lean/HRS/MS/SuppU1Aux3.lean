import HRS.MS.SuppU1Aux2

/-!
# U1 aux 3: symmetric compactly supported finite-rank approximation of a continuous symmetric kernel.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- reindexing a finite-rank symmetric kernel onto `Fin m`. -/
lemma u1_reindex {κ : Type} [Fintype κ] (c : κ → κ → ℝ) (u : κ → E → ℝ) :
    ∃ (m : ℕ) (c' : Fin m → Fin m → ℝ) (u' : Fin m → E → ℝ),
      ((∀ a b, c a b = c b a) → ∀ a b, c' a b = c' b a) ∧
      (∀ a, ∃ i, u' a = u i) ∧
      ∀ x y, ∑ a, ∑ b, c' a b * u' a x * u' b y = ∑ i, ∑ j, c i j * u i x * u j y := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun a b => c (e.symm a) (e.symm b), fun a => u (e.symm a), ?_, ?_, ?_⟩
  · intro h a b; exact h _ _
  · intro a; exact ⟨e.symm a, rfl⟩
  · intro x y
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e.symm]

lemma u1_finiteRank_of_continuous (G : E × E → ℝ) (hGc : Continuous G)
    (hGs : ∀ x y, G (x, y) = G (y, x)) (R η : ℝ) (hη : 0 < η)
    (hsupp : ∀ x y, G (x, y) ≠ 0 → ‖x‖ ≤ R ∧ ‖y‖ ≤ R) :
    ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → E → ℝ),
      (∀ a b, c a b = c b a) ∧ (∀ a, ContDiff ℝ ∞ (u a)) ∧ (∀ a, HasCompactSupport (u a)) ∧
      ∀ x y, |G (x, y) - ∑ a, ∑ b, c a b * u a x * u b y| ≤ η := by
  classical
  obtain ⟨ι, hι, F, H, hF, hH, hFH⟩ := u1_sw_approx G hGc (|R| + 2) η hη
  -- cutoff
  let χb : ContDiffBump (0 : E) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  let χ : E → ℝ := fun x => χb x
  have hχs : ContDiff ℝ ∞ χ := χb.contDiff
  have hχc : HasCompactSupport χ := χb.hasCompactSupport
  have hχ1 : ∀ x, ‖x‖ ≤ R → χ x = 1 := fun x hx =>
    χb.one_of_mem_closedBall (by simp only [mem_closedBall, dist_zero_right]; show ‖x‖ ≤ |R| + 1; linarith [le_abs_self R])
  have hχ0 : ∀ x, |R| + 2 < ‖x‖ → χ x = 0 := fun x hx =>
    χb.zero_of_le_dist (by rw [dist_zero_right]; show |R| + 2 ≤ ‖x‖; linarith)
  have hχn : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => ⟨χb.nonneg, χb.le_one⟩
  -- the cut-off finite-rank kernel `k₀`
  let k₀ : E → E → ℝ := fun x y => ∑ i, (χ x * F i x) * (χ y * H i y)
  have hk₀ : ∀ x y, |G (x, y) - k₀ x y| ≤ η := by
    intro x y
    have hk : k₀ x y = χ x * χ y * ∑ i, F i x * H i y := by
      simp only [k₀, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    by_cases hx : ‖x‖ ≤ R ∧ ‖y‖ ≤ R
    · rw [hk, hχ1 x hx.1, hχ1 y hx.2, one_mul, one_mul]
      have := hFH x y (by linarith [abs_nonneg R, le_abs_self R, hx.1]) (by linarith [abs_nonneg R, le_abs_self R, hx.2])
      exact this.le
    · have hG0 : G (x, y) = 0 := by
        by_contra h; exact hx (hsupp x y h)
      by_cases hbig : ‖x‖ ≤ |R| + 2 ∧ ‖y‖ ≤ |R| + 2
      · have := hFH x y hbig.1 hbig.2
        have this : |∑ i, F i x * H i y| < η := by simpa [hG0] using this
        rw [hG0, zero_sub, abs_neg, hk, abs_mul, abs_of_nonneg (mul_nonneg (hχn x).1 (hχn y).1)]
        calc χ x * χ y * |∑ i, F i x * H i y| ≤ 1 * 1 * η := by
              apply mul_le_mul _ this.le (abs_nonneg _) (by positivity)
              exact mul_le_mul (hχn x).2 (hχn y).2 (hχn y).1 zero_le_one
          _ = η := by ring
      · have : χ x = 0 ∨ χ y = 0 := by
          by_cases h1 : ‖x‖ ≤ |R| + 2
          · right; exact hχ0 y (by by_contra h; exact hbig ⟨h1, not_lt.mp h⟩)
          · left; exact hχ0 x (not_le.mp h1)
        have : k₀ x y = 0 := by
          rw [hk]; rcases this with h | h <;> simp [h]
        rw [this, hG0]; simpa using hη.le
  -- symmetrise and reindex
  let u : ι ⊕ ι → E → ℝ := Sum.elim (fun i x => χ x * F i x) (fun i x => χ x * H i x)
  let c : ι ⊕ ι → ι ⊕ ι → ℝ := fun a b => match a, b with
    | Sum.inl i, Sum.inr j => if i = j then 1 / 2 else 0
    | Sum.inr i, Sum.inl j => if i = j then 1 / 2 else 0
    | _, _ => 0
  have hcs : ∀ a b, c a b = c b a := by
    rintro (i | i) (j | j) <;> simp [c, eq_comm]
  have hsum : ∀ x y, ∑ a, ∑ b, c a b * u a x * u b y = (k₀ x y + k₀ y x) / 2 := by
    intro x y
    simp only [Fintype.sum_sum_type, c, u, Sum.elim_inl, Sum.elim_inr, k₀]
    simp
    rw [add_div, Finset.sum_div, Finset.sum_div]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨m, c', u', hc', hu', hsum'⟩ := u1_reindex c u
  refine ⟨m, c', u', hc' hcs, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨i, hi⟩ := hu' a
    rw [hi]
    rcases i with i | i
    · exact hχs.mul (hF i)
    · exact hχs.mul (hH i)
  · intro a
    obtain ⟨i, hi⟩ := hu' a
    rw [hi]
    rcases i with i | i
    · exact hχc.mul_right
    · exact hχc.mul_right
  · intro x y
    rw [hsum', hsum]
    have h1 := hk₀ x y
    have h2 := hk₀ y x
    rw [hGs x y] at h1
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [hGs x y, h1.1, h1.2, h2.1, h2.2]

end HRS.Whole.U1
