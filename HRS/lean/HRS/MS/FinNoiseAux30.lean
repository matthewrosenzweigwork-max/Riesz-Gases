import HRS.MS.FinNoiseAux29
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# S8.6 `finite_noise`: block operators into `ℓ²(J; G)` and the root bound for a sum of blocks (S86)

`s86_blockLin M c`: the operator `x ↦ (M_j x)_j ∈ ℓ²(J; G)` for bounded blocks `M_j` with `‖M_j x‖ ≤ c_j ‖x‖`,
`∑ c_j² < ∞`.  `s86_block_root`: if `S, S'` are symmetric nonnegative with `⟨S x, S y⟩ = ∑_j ⟨M_j x, M_j y⟩` and
`⟨S' x, S' y⟩ = ∑_j ⟨M'_j x, M'_j y⟩`, then `‖S - S'‖²_HS ≤ 2 ‖(M_j - M'_j)_j‖²_HS` (Araki-Yamagami through `ℓ²(J; G)`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K G J : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem s86_block_mem (M : J → K →L[ℝ] G) (c : J → ℝ) (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖)
    (hcs : Summable fun j => c j ^ 2) (x : K) : Memℓp (fun j => M j x) 2 := by
  refine memℓp_gen ?_
  have : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [this]
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hcs.mul_right (‖x‖ ^ 2))
  rw [Real.rpow_two]
  calc ‖M j x‖ ^ 2 ≤ (c j * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc j x) 2
    _ = c j ^ 2 * ‖x‖ ^ 2 := by ring

/-- The block operator. -/
def blockLin (M : J → K →L[ℝ] G) (c : J → ℝ) (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖)
    (hcs : Summable fun j => c j ^ 2) : K →L[ℝ] lp (fun _ : J => G) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun j => M j x, s86_block_mem M c hc hcs x⟩
      map_add' := fun x y => by ext j; simp; rfl
      map_smul' := fun a x => by ext j; simp }
    (Real.sqrt (∑' j, c j ^ 2)) (fun x => by
      set f : lp (fun _ : J => G) 2 := ⟨fun j => M j x, s86_block_mem M c hc hcs x⟩ with hf
      have h2 : ‖f‖ ^ 2 = ∑' j, ‖M j x‖ ^ 2 := by
        have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
        have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        rw [e2] at this
        simpa [Real.rpow_two, hf] using this
      have h3 : ∑' j, ‖M j x‖ ^ 2 ≤ (∑' j, c j ^ 2) * ‖x‖ ^ 2 := by
        rw [← tsum_mul_right]
        refine Summable.tsum_le_tsum (fun j => ?_) ?_ (hcs.mul_right _)
        · calc ‖M j x‖ ^ 2 ≤ (c j * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc j x) 2
            _ = c j ^ 2 * ‖x‖ ^ 2 := by ring
        · exact (memℓp_gen_iff (by norm_num)).1 (s86_block_mem M c hc hcs x) |> fun h => by
            simpa [Real.rpow_two] using h
      have : ‖f‖ ≤ Real.sqrt (∑' j, c j ^ 2) * ‖x‖ := by
        rw [← Real.sqrt_sq (norm_nonneg f), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul
          (tsum_nonneg fun j => sq_nonneg _)]
        exact Real.sqrt_le_sqrt (by rw [h2]; exact h3)
      exact this)

theorem blockLin_apply (M : J → K →L[ℝ] G) (c : J → ℝ) (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖)
    (hcs : Summable fun j => c j ^ 2) (x : K) (j : J) : blockLin M c hc hcs x j = M j x := rfl

theorem blockLin_norm_sq (M : J → K →L[ℝ] G) (c : J → ℝ) (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖)
    (hcs : Summable fun j => c j ^ 2) (x : K) :
    ‖blockLin M c hc hcs x‖ ^ 2 = ∑' j, ‖M j x‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (blockLin M c hc hcs x)
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [e2] at this
  simpa [Real.rpow_two, blockLin_apply] using this

theorem blockLin_sub_norm_sq (M M' : J → K →L[ℝ] G) (c c' : J → ℝ)
    (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖) (hcs : Summable fun j => c j ^ 2)
    (hc' : ∀ j x, ‖M' j x‖ ≤ c' j * ‖x‖) (hcs' : Summable fun j => c' j ^ 2) (x : K) :
    ‖(blockLin M c hc hcs - blockLin M' c' hc' hcs') x‖ ^ 2 = ∑' j, ‖M j x - M' j x‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ((blockLin M c hc hcs - blockLin M' c' hc' hcs') x)
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [e2] at this
  simpa [Real.rpow_two, blockLin_apply] using this

theorem blockLin_inner (M : J → K →L[ℝ] G) (c : J → ℝ) (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖)
    (hcs : Summable fun j => c j ^ 2) (x y : K) :
    inner ℝ (blockLin M c hc hcs x) (blockLin M c hc hcs y) = ∑' j, inner ℝ (M j x) (M j y) := by
  rw [lp.inner_eq_tsum]
  rfl

end HRS.MS.FinNoise
