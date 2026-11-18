import HRS.MS.CritForceDefs
import HRS.MS.WadAux50
import HRS.MS.OrbFeatAux1
import HRS.MP.RdInit

/-!
# S8.2 core X1, part 1: elementary tools for the weighted feature estimate

* `s82_norm_mf_le`: the operator norm of a continuous multilinear form on `ℝ^d` is at most `d^i` times
  the largest value on coordinate tuples (conversion between `partialDeriv` and `iteratedFDeriv` norms).
* `s82_iteratedFDeriv_add_const`: derivatives of order `≥ 1` ignore additive constants.
* `s82_hermite_bound`: sup bound for the derivatives of the Hermite feature `φ_α = λ_α^{-m/2} h_α`
  with the explicit power `λ_α^{(⌊i+d/2⌋+1-m)/2}`, uniformly in `m` and `α`; and its weighted decay
  version (`MemCM`, `MemCMj` of `φ_α`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82BD

open HRS HRS.Whole HRS.MP.RdInit

variable {d : ℕ}

theorem s82_vec_expand (x : Euc d) :
    x = ∑ k, x k • (EuclideanSpace.single k (1 : ℝ) : Euc d) := by
  ext j
  simp [Pi.single_apply]

theorem s82_norm_mf_le {i : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ idx : Fin i → Fin d, |L (mri_e idx)| ≤ B) :
    ‖L‖ ≤ (d : ℝ) ^ i * B := by
  classical
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = fun l => ∑ k, v l k • (EuclideanSpace.single k (1 : ℝ) : Euc d) := by
    funext l; exact s82_vec_expand (v l)
  have h1 : L v = ∑ r : Fin i → Fin d, (∏ l, v l (r l)) * L (mri_e r) := by
    have hh := MultilinearMap.map_sum L.toMultilinearMap
      (fun l (k : Fin d) => (v l k) • (EuclideanSpace.single k (1 : ℝ) : Euc d))
    have hLv : L v = L.toMultilinearMap
        (fun l => ∑ k, v l k • (EuclideanSpace.single k (1 : ℝ) : Euc d)) := by
      conv_lhs => rw [hv]
      rfl
    rw [hLv, hh]
    refine Finset.sum_congr rfl fun r _ => ?_
    have := L.toMultilinearMap.map_smul_univ (fun l => v l (r l))
      (fun l => (EuclideanSpace.single (r l) (1 : ℝ) : Euc d))
    have e : mri_e r = fun l => (EuclideanSpace.single (r l) (1 : ℝ) : Euc d) := rfl
    rw [e]
    simpa using this
  rw [h1, Real.norm_eq_abs]
  calc |∑ r : Fin i → Fin d, (∏ l, v l (r l)) * L (mri_e r)|
      ≤ ∑ r : Fin i → Fin d, |(∏ l, v l (r l)) * L (mri_e r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin i → Fin d, (∏ l, |v l (r l)|) * B := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [abs_mul, Finset.abs_prod]
        exact mul_le_mul_of_nonneg_left (hB r) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    _ = (∏ l : Fin i, ∑ k : Fin d, |v l k|) * B := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.prod_univ_sum]
        rfl
    _ ≤ (∏ l : Fin i, ((d : ℝ) * ‖v l‖)) * B := by
        have h0 : ∀ l ∈ (Finset.univ : Finset (Fin i)), 0 ≤ ∑ k : Fin d, |v l k| :=
          fun l _ => Finset.sum_nonneg fun k _ => abs_nonneg _
        refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ h0 fun l _ => ?_) hB0
        calc ∑ k : Fin d, |v l k| ≤ ∑ k : Fin d, ‖v l‖ :=
              Finset.sum_le_sum fun k _ => by
                simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (v l) k
          _ = (d : ℝ) * ‖v l‖ := by simp
    _ = (d : ℝ) ^ i * B * ∏ l, ‖v l‖ := by
        rw [Finset.prod_mul_distrib]; simp; ring

/-- Coordinate-tuple bound ⇒ `iteratedFDeriv` norm bound. -/
theorem s82_iter_norm_le (i : ℕ) (g : Euc d → ℝ) (x : Euc d) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ idx : Fin i → Fin d, |partialDeriv idx g x| ≤ B) :
    ‖iteratedFDeriv ℝ i g x‖ ≤ (d : ℝ) ^ i * B :=
  s82_norm_mf_le _ B hB0 fun idx => hB idx

theorem s82_iteratedFDeriv_add_const {g : Euc d → ℝ} (c : ℝ) {i : ℕ} (hi : 1 ≤ i) (x : Euc d) :
    iteratedFDeriv ℝ i (fun y => g y + c) x = iteratedFDeriv ℝ i g x := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hf : fderiv ℝ (fun y => g y + c) = fderiv ℝ g := by
    funext y; exact fderiv_add_const c
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, hf]

end HRS.MS.S82BD
