import HRS.MS.R2InterpAux3

/-!
# S11.1 X2, packet H02 (part 1): a path-space quadratic bound for positive semidefinite matrices

For a positive semidefinite symmetric matrix `K` on the grid-and-Hermite index set `idx = {0..2^L} × A` and a bounded
bilinear form `M` on the path space: `|∑_{p,q} K_{pq} M(b_p,b_q)| ≤ 2 ∑_α K_{(0,α)(0,α)} + 2N ∑_j ∑_α D_K(j,α)` with
`N = 2^L` and `D_K` the quadratic form of `K` on the increments `e_{j+1,α} - e_{j,α}` (finite-dimensional Cholesky factor
and the discrete Sobolev inequality for piecewise linear interpolation; no sum of the form `max_i`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole HRS.MS.R2Interp

section Bilinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem s111x2_upd0 (x y z : X) : (Function.update ![x, y] 0 z : Fin 2 → X) = ![z, y] := by
  ext i; fin_cases i <;> simp

theorem s111x2_upd1 (x y z : X) : (Function.update ![x, y] 1 z : Fin 2 → X) = ![x, z] := by
  ext i; fin_cases i <;> simp

/-- Expansion of a bilinear form on finite combinations. -/
theorem s111x2_bil_expand (M : X [×2]→L[ℝ] ℝ) {ι : Type*} (s : Finset ι) (b : ι → X) (c c' : ι → ℝ) :
    M ![∑ p ∈ s, c p • b p, ∑ q ∈ s, c' q • b q] = ∑ p ∈ s, ∑ q ∈ s, c p * c' q * M ![b p, b q] := by
  let Bl : X →ₗ[ℝ] X →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => M ![x, y])
    (fun x x' y => by
      have := M.toMultilinearMap.map_update_add ![x, y] 0 x x'
      simpa [s111x2_upd0] using this)
    (fun c x y => by
      have := M.toMultilinearMap.map_update_smul ![x, y] 0 c x
      simpa [s111x2_upd0] using this)
    (fun x y y' => by
      have := M.toMultilinearMap.map_update_add ![x, y] 1 y y'
      simpa [s111x2_upd1] using this)
    (fun c x y => by
      have := M.toMultilinearMap.map_update_smul ![x, y] 1 c y
      simpa [s111x2_upd1] using this)
  have hB : ∀ x y, M ![x, y] = Bl x y := fun x y => rfl
  rw [hB]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hB]
  ring

theorem s111x2_bil_le (M : X [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) (x : X) : |M ![x, x]| ≤ ‖x‖ ^ 2 := by
  have := M.le_opNorm ![x, x]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [Real.norm_eq_abs] at this
  calc |M ![x, x]| ≤ ‖M‖ * (‖x‖ * ‖x‖) := this
    _ ≤ 1 * (‖x‖ * ‖x‖) := mul_le_mul_of_nonneg_right hM (by positivity)
    _ = ‖x‖ ^ 2 := by ring

/-- Cholesky-type decomposition of a positive semidefinite symmetric kernel on a finite set. -/
theorem s111x2_quad_decomp (M : X [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (b : ι → X) (K : ι → ι → ℝ) (hsymm : ∀ p ∈ s, ∀ q ∈ s, K p q = K q p)
    (hpsd : ∀ c : ι → ℝ, 0 ≤ ∑ p ∈ s, ∑ q ∈ s, c p * c q * K p q) :
    ∃ (m : ℕ) (v : Fin m → ι → ℝ), (∀ p ∈ s, ∀ q ∈ s, K p q = ∑ k, v k p * v k q) ∧
      |∑ p ∈ s, ∑ q ∈ s, K p q * M ![b p, b q]| ≤ ∑ k, ‖∑ p ∈ s, v k p • b p‖ ^ 2 := by
  classical
  let K' : Matrix s s ℝ := fun p q => K p q
  have hpsd' : K'.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
    · ext p q
      simp only [Matrix.conjTranspose_apply, K', star_trivial]
      exact hsymm q.1 q.2 p.1 p.2
    · have := hpsd (fun p => if h : p ∈ s then x ⟨p, h⟩ else 0)
      simp only [dotProduct, Matrix.mulVec, K']
      simp only [star_trivial]
      convert this using 1
      rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Finset.mul_sum]
      rw [← Finset.sum_coe_sort s]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp [p.2, q.2]
      ring
  obtain ⟨m, v', hv'⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hpsd'
  let v : Fin m → ι → ℝ := fun k p => if h : p ∈ s then v' k ⟨p, h⟩ else 0
  have hK : ∀ p ∈ s, ∀ q ∈ s, K p q = ∑ k, v k p * v k q := by
    intro p hp q hq
    have := congrFun (congrFun hv' ⟨p, hp⟩) ⟨q, hq⟩
    simp only [K'] at this
    rw [this]
    simp [v, hp, hq, Matrix.sum_apply, Matrix.vecMulVec_apply]
  refine ⟨m, v, hK, ?_⟩
  have e : ∑ p ∈ s, ∑ q ∈ s, K p q * M ![b p, b q] =
      ∑ k, M ![∑ p ∈ s, v k p • b p, ∑ q ∈ s, v k q • b q] := by
    simp_rw [s111x2_bil_expand M s b]
    calc ∑ p ∈ s, ∑ q ∈ s, K p q * M ![b p, b q]
        = ∑ p ∈ s, ∑ q ∈ s, ∑ k, v k p * v k q * M ![b p, b q] :=
          Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
            rw [hK p hp q hq, Finset.sum_mul]
      _ = ∑ p ∈ s, ∑ k, ∑ q ∈ s, v k p * v k q * M ![b p, b q] :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ k, ∑ p ∈ s, ∑ q ∈ s, v k p * v k q * M ![b p, b q] := Finset.sum_comm
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  exact s111x2_bil_le M hM _

end Bilinear

end HRS.MS.S111X2
