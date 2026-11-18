import HRS.Uniform.Q45Grid1
import HRS.Uniform.MaximalAux

/-!
# Q45: the grid block vectors and the identification with Riemann sums
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

/-- The block vector `α_{(i,a),k} = V(t_i, r_k)^* b_a` (zero if the block `k` lies beyond `t_i`). -/
def gridα (S : EvolData H E) (T : ℝ) (g κ d : ℕ) (b : Fin d → E) :
    Fin ((g + 1) * d) → ℕ → H :=
  fun j k => if k < ((finProdFinEquiv.symm j).1 : ℕ) * κ then
    pullbackVec S (unifPart T g (finProdFinEquiv.symm j).1) (rr (g * κ) T k)
      (innerSL ℝ (b (finProdFinEquiv.symm j).2)) else 0

lemma inner_pullbackVec (S : EvolData H E) (t r : ℝ) (ℓ : E →L[ℝ] ℝ) (x : H) :
    inner ℝ (pullbackVec S t r ℓ) x = ℓ (S.VE t r (S.j x)) := by
  unfold pullbackVec
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

lemma gridα_inner (S : EvolData H E) (T : ℝ) (g κ d : ℕ) (b : Fin d → E) (i : Fin (g + 1))
    (a : Fin d) (k : ℕ) (x : H) :
    inner ℝ (gridα S T g κ d b (finProdFinEquiv (i, a)) k) x =
      if k < (i : ℕ) * κ then inner ℝ (b a) (S.VE (unifPart T g i) (rr (g * κ) T k) (S.j x)) else 0 := by
  unfold gridα
  simp only [Equiv.symm_apply_apply]
  split_ifs
  · rw [inner_pullbackVec]; rfl
  · simp

/-- The grid time `t_i = iT/g` is at most `T` for `i ≤ g`. -/
lemma gridT_le {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) (i : Fin (g + 1)) :
    unifPart T g i ≤ T := unifPart_le hT.le (Nat.lt_succ_iff.1 i.2)

lemma rr_le_gridT {T : ℝ} (hT : 0 < T) {g κ : ℕ} (hg : 1 ≤ g) (hκ : 1 ≤ κ) (i : ℕ) {k : ℕ}
    (hk : k ≤ i * κ) : rr (g * κ) T k ≤ unifPart T g i := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have hκ' : (0 : ℝ) < κ := by exact_mod_cast hκ
  unfold rr unifPart
  push_cast
  rw [div_le_div_iff₀ (by positivity) hg']
  have : (k : ℝ) ≤ i * κ := by exact_mod_cast hk
  nlinarith [mul_le_mul_of_nonneg_right this hT.le]

end HRS.Uniform.Q45
