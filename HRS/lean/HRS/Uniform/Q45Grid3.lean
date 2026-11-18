import HRS.Uniform.Q45Grid2

/-!
# Q45: the blockwise bound and the Riemann-sum identification
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma synthVec_block {T : ℝ} {g κ d : ℕ} {b : Fin d → E} (S : EvolData H E) (k : ℕ) (x : H)
    (i : Fin (g + 1)) :
    synthVec (g := g) b (WithLp.toLp 2 fun j => inner ℝ (gridα S T g κ d b j k) x) i =
      if k < (i : ℕ) * κ then projB b (S.VE (unifPart T g i) (rr (g * κ) T k) (S.j x)) else 0 := by
  unfold synthVec projB
  simp only [gridα_inner]
  split_ifs
  · rfl
  · simp

/-- The blockwise bound `‖L(⟨α_{·,k}, x⟩)‖ ≤ C ‖x‖` of the synthesis map, with `C` the evolution bound. -/
lemma pathMap_block_bound {T : ℝ} (hT : 0 < T) {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) {d : ℕ}
    {b : Fin d → E} (hb : Orthonormal ℝ b) {K : ℝ} (S : EvolData H E) (hS : S.MaxHyp T K)
    (k : ℕ) (x : H) :
    ‖pathMap hT hg hb (WithLp.toLp 2 fun j => inner ℝ (gridα S T g κ d b j k) x)‖ ≤
      detConst T K * ‖x‖ := by
  rw [pathMap_apply]
  refine norm_hatPath_le hT hg _ (mul_nonneg (detConst_pos T K).le (norm_nonneg _)) fun i => ?_
  rw [synthVec_block]
  split_ifs with h
  · refine (norm_projB_le hb _).trans ?_
    have hk0 : 0 ≤ rr (g * κ) T k := unifPart_nonneg hT.le _ _
    exact hS.norm_le hT.le hk0 (rr_le_gridT hT hg hκ i h.le) (gridT_le hT hg i) x
  · simp only [norm_zero]
    exact mul_nonneg (detConst_pos T K).le (norm_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Riemann sum of a path along the partition `r_k = kT/(gκ)` up to `t_i = iT/g`. -/
def rsum (S : EvolData H E) (T : ℝ) (g κ : ℕ) (M : ℝ → Ω → H) (i : ℕ) (ω : Ω) : E :=
  ∑ k ∈ Finset.range (i * κ), S.VE (unifPart T g i) (rr (g * κ) T k)
    (S.j (M (rr (g * κ) T (k + 1)) ω - M (rr (g * κ) T k) ω))

/-- The initial coordinates `⟨b_a, V(t_i,0) j x₀⟩`. -/
def initCoord {T : ℝ} {g d : ℕ} (b : Fin d → E) (S : EvolData H E) (x : H) : ℝ^((g + 1) * d) :=
  WithLp.toLp 2 fun j => inner ℝ (b (finProdFinEquiv.symm j).2)
    (S.VE (unifPart T g (finProdFinEquiv.symm j).1) 0 (S.j x))

lemma pathMap_zeta {T : ℝ} (hT : 0 < T) {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) {d : ℕ} {b : Fin d → E}
    (hb : Orthonormal ℝ b) (S : EvolData H E) (x : H) (M : ℝ → Ω → H) (ω : Ω) :
    pathMap hT hg hb (initCoord (T := T) (g := g) b S x + zeta (gridα S T g κ d b) T (g * κ) M ω) =
      hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j x) + rsum S T g κ M i ω)) := by
  rw [pathMap_apply]
  congr 1
  funext i
  unfold synthVec projB
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [PiLp.add_apply, initCoord, zeta, Equiv.symm_apply_apply, inner_add_right]
  congr 1
  simp only [gridα_inner, rsum, inner_sum]
  have hi : (i : ℕ) * κ ≤ g * κ := Nat.mul_le_mul_right κ (Nat.lt_succ_iff.1 i.2)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (g * κ)) (fun k => k < (i : ℕ) * κ)]
  have h1 : Finset.filter (fun k => k < (i : ℕ) * κ) (Finset.range (g * κ)) = Finset.range (i * κ) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [h1]
  have h2 : ∑ k ∈ Finset.filter (fun k => ¬ k < (i : ℕ) * κ) (Finset.range (g * κ)),
      (if k < (i : ℕ) * κ then inner ℝ (b a) (S.VE (unifPart T g i) (rr (g * κ) T k)
        (S.j (M (rr (g * κ) T (k + 1)) ω - M (rr (g * κ) T k) ω))) else 0) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg (Finset.mem_filter.1 hk).2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [if_pos (Finset.mem_range.1 hk)]

end HRS.Uniform.Q45
