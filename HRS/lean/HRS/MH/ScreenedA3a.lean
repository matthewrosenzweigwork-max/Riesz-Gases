import HRS.MH.ScreenedDefs
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Packet A3a of `B:lem:screened` (S.B.4): `∑_{z ∈ ℤ^d} ⟨z⟩^{-(d+3)} < ∞`.

The standard lattice `ℤ^d ⊂ ℝ^d` is a `ℤ`-lattice of rank `d`; `ZLattice.summable_norm_rpow` gives
convergence of `∑ ‖z‖^r` for `r < -d`, and `⟨x⟩^{-(d+3)} ≤ ‖x‖^{-(d+3)}` off the origin.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- The `ℤ`-span of the standard basis of `ℝ^d` (the lattice `ℤ^d`). -/
abbrev a3a_L (d : ℕ) : Submodule ℤ (Euc d) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

lemma a3a_rank (d : ℕ) : Module.finrank ℤ (a3a_L d) = d := by
  rw [ZLattice.rank ℝ (a3a_L d)]
  simp

lemma a3a_latticePt_mem (d : ℕ) (z : Fin d → ℤ) : latticePt z ∈ a3a_L d := by
  have h : latticePt z = ∑ i, z i • (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i := by
    ext i
    simp [latticePt, Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma a3a_summable_aux {d : ℕ} (r : ℝ) (g : (Fin d → ℤ) → a3a_L d) (hg : Function.Injective g)
    (hval : ∀ z, ((g z : a3a_L d) : Euc d) = latticePt z)
    (hS : Summable (fun z : a3a_L d => ‖(z : Euc d)‖ ^ r)) :
    Summable (fun z : Fin d → ℤ => ‖latticePt z‖ ^ r) :=
  (hS.comp_injective hg).congr fun z => by simp only [Function.comp_apply, hval]

lemma a3a_summable (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable (fun z : Fin d → ℤ => ‖latticePt z‖ ^ r) := by
  have hr' : r < -(Module.finrank ℤ (a3a_L d) : ℝ) := by
    rw [a3a_rank]; exact hr
  have hS := ZLattice.summable_norm_rpow (a3a_L d) r hr'
  have hφ : Function.Injective (fun z : Fin d → ℤ => (⟨latticePt z, a3a_latticePt_mem d z⟩ : a3a_L d)) := by
    intro z z' h
    have h2 : latticePt z = latticePt z' := congrArg Subtype.val h
    funext i
    have := congrArg (fun x : Euc d => x i) h2
    simpa [latticePt] using this
  exact a3a_summable_aux r _ hφ (fun z => rfl) hS

lemma a3a_latticePt_ne (d : ℕ) {z : Fin d → ℤ} (hz : z ≠ 0) : latticePt z ≠ 0 := by
  intro h
  apply hz
  funext i
  have := congrArg (fun x : Euc d => x i) h
  simpa [latticePt] using this

lemma a3a_bound (d : ℕ) (z : Fin d → ℤ) :
    cellWeight d z ≤ ‖latticePt z‖ ^ (-((d : ℝ) + 3)) + (if z = 0 then (1 : ℝ) else 0) := by
  by_cases hz : z = 0
  · subst hz
    have hl0 : latticePt (0 : Fin d → ℤ) = 0 := by
      ext i; simp [latticePt]
    have h0 : cellWeight d 0 = 1 := by
      unfold cellWeight jbracket
      rw [hl0]
      simp
    rw [h0, if_pos rfl]
    have := Real.rpow_nonneg (norm_nonneg (latticePt (0 : Fin d → ℤ))) (-((d : ℝ) + 3))
    linarith
  · rw [if_neg hz, add_zero]
    have hx : 0 < ‖latticePt z‖ := norm_pos_iff.mpr (a3a_latticePt_ne d hz)
    have hle : ‖latticePt z‖ ≤ jbracket (latticePt z) := by
      unfold jbracket
      calc ‖latticePt z‖ = Real.sqrt (‖latticePt z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (1 + ‖latticePt z‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)
    unfold cellWeight
    exact Real.rpow_le_rpow_of_nonpos hx hle (by linarith)

theorem cellWeight_tsum_lt_top_proof (hd : 1 ≤ d) : ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) < ⊤ := by
  have hnn : ∀ z, 0 ≤ cellWeight d z := fun z => by
    unfold cellWeight jbracket
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hsum : Summable (fun z : Fin d → ℤ =>
      ‖latticePt z‖ ^ (-((d : ℝ) + 3)) + (if z = 0 then (1 : ℝ) else 0)) :=
    (a3a_summable d _ (by linarith)).add (hasSum_ite_eq (0 : Fin d → ℤ) (1 : ℝ)).summable
  have hs : Summable (fun z => cellWeight d z) :=
    Summable.of_nonneg_of_le hnn (a3a_bound d) hsum
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs]
  exact ENNReal.ofReal_lt_top

end HRS.MH.Screened
