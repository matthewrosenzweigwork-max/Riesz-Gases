import HRS.MS.QsfOsc4

/-!
# S4.5 oscillator clause, part 5: the isometry `B_m ≃ ℓ²(ℕ)` given by an enumeration of the multi-indices
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

theorem s45_memℓp_comp {ι κ : Type*} (e : ι ≃ κ) {f : κ → ℝ} (hf : Memℓp f 2) :
    Memℓp (fun i => f (e i)) 2 := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hf ⊢
  exact (Equiv.summable_iff e (f := fun k => ‖f k‖ ^ (2 : ENNReal).toReal)).2 hf

/-- Reindexing of `ℓ²` along an equivalence. -/
def s45_reindex {ι κ : Type*} (e : ι ≃ κ) :
    lp (fun _ : κ => ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : ι => ℝ) 2 where
  toFun u := ⟨fun i => u (e i), s45_memℓp_comp e (lp.memℓp u)⟩
  invFun v := ⟨fun k => v (e.symm k), s45_memℓp_comp e.symm (lp.memℓp v)⟩
  map_add' u v := by ext i; rfl
  map_smul' c u := by ext i; rfl
  left_inv u := by ext k; simp
  right_inv v := by ext i; simp
  norm_map' u := by
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
    congr 1
    exact Equiv.tsum_eq e (fun k => ‖u k‖ ^ (2 : ENNReal).toReal)

theorem s45_reindex_apply {ι κ : Type*} (e : ι ≃ κ) (u : lp (fun _ : κ => ℝ) 2) (i : ι) :
    (s45_reindex e u : lp (fun _ : ι => ℝ) 2) i = u (e i) := rfl

end S45

end
