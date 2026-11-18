import HRS.MS.FinNoiseAux30

/-!
# S8.6 `finite_noise`: symmetric roots of a sum of blocks (S86)

`s86_block_root`: if `S, S'` are symmetric nonnegative with `⟨S x, S y⟩ = ∑_j ⟨M_j x, M_j y⟩`,
`⟨S' x, S' y⟩ = ∑_j ⟨M'_j x, M'_j y⟩` (blocks bounded with square-summable constants and Hilbert-Schmidt as a family),
then `∑_k ‖(S - S') e_k‖² ≤ 2 ∑_k ∑_j ‖(M_j - M'_j) e_k‖²`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS

variable {K G J : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ K)

theorem s86_block_root (M M' : J → K →L[ℝ] G) (c c' : J → ℝ)
    (hc : ∀ j x, ‖M j x‖ ≤ c j * ‖x‖) (hcs : Summable fun j => c j ^ 2)
    (hc' : ∀ j x, ‖M' j x‖ ≤ c' j * ‖x‖) (hcs' : Summable fun j => c' j ^ 2)
    (hMs : Summable fun k => ∑' j, ‖M j (e k)‖ ^ 2)
    (hM's : Summable fun k => ∑' j, ‖M' j (e k)‖ ^ 2)
    (S S' : K →L[ℝ] K)
    (hS : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y)) (hS0 : ∀ x, 0 ≤ inner ℝ (S x) x)
    (hS' : ∀ x y, inner ℝ (S' x) y = inner ℝ x (S' y)) (hS'0 : ∀ x, 0 ≤ inner ℝ (S' x) x)
    (hSM : ∀ x y, inner ℝ (S x) (S y) = ∑' j, inner ℝ (M j x) (M j y))
    (hS'M : ∀ x y, inner ℝ (S' x) (S' y) = ∑' j, inner ℝ (M' j x) (M' j y)) :
    Summable (fun k => ‖(S - S') (e k)‖ ^ 2) ∧
    ∑' k, ‖(S - S') (e k)‖ ^ 2 ≤
      2 * ∑' k, ∑' j, ‖M j (e k) - M' j (e k)‖ ^ 2 := by
  set X := blockLin M c hc hcs with hX
  set Y := blockLin M' c' hc' hcs' with hY
  have hXs : Summable fun k => ‖X (e k)‖ ^ 2 := by
    refine hMs.congr fun k => ?_
    rw [hX, blockLin_norm_sq]
  have hYs : Summable fun k => ‖Y (e k)‖ ^ 2 := by
    refine hM's.congr fun k => ?_
    rw [hY, blockLin_norm_sq]
  obtain ⟨h1, h2, h3⟩ := s86_araki_yamagami e X Y S S' hS hS0 hS' hS'0
    (fun x y => by rw [hSM, hX, blockLin_inner]) (fun x y => by rw [hS'M, hY, blockLin_inner]) hXs hYs
  refine ⟨h1, h3.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
  refine tsum_congr fun k => ?_
  rw [hX, hY, blockLin_sub_norm_sq]

end HRS.MS.FinNoise
