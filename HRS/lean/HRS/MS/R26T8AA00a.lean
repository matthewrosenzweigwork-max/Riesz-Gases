import HRS.MS.S82P2Local
import HRS.MS.R26T8AP10a16
import HRS.MS.R26T8AP11f9

/-!
# S8.2 T8A A00 (part a): Hessian of the `x`-slice of a pair function
If `Q̃ = uncurry Q` is `C^2` off the diagonal then `‖iteratedFDeriv ℝ 2 (fun w => Q w y) w‖ ≤ ‖iteratedFDeriv ℝ 2 (uncurry Q) (w,y)‖`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_a00_slice_hess {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2}) {w y : Euc d} (hwy : w ≠ y) :
    ‖iteratedFDeriv ℝ 2 (fun w' => Q w' y) w‖ ≤ ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (w, y)‖ := by
  set U : Set (Euc d × Euc d) := {p | p.1 ≠ p.2} with hU
  have hUo : IsOpen U := isOpen_ne_fun continuous_fst continuous_snd
  set L : Euc d →L[ℝ] Euc d × Euc d := ContinuousLinearMap.inl ℝ (Euc d) (Euc d) with hL
  set fh : Euc d × Euc d → ℝ := fun p => Function.uncurry Q (p + (0, y)) with hfh
  set s : Set (Euc d × Euc d) := (fun p => p + ((0 : Euc d), y)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_id.add continuous_const)
  have hfhc : ContDiffOn ℝ 2 fh s :=
    hQ.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  have hLs : IsOpen (L ⁻¹' s) := hso.preimage L.continuous
  have hmem : L w ∈ s := by
    show L w + ((0 : Euc d), y) ∈ U
    simp [hL, hU, hwy]
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (i := 2) (n := 2) L hfhc
    hso.uniqueDiffOn hLs.uniqueDiffOn hmem le_rfl
  have hcomp : (fh ∘ L) = fun w' => Q w' y := by
    funext w'; simp [hfh, hL, Function.uncurry]
  rw [hcomp] at key
  have hwmem : w ∈ L ⁻¹' s := hmem
  rw [iteratedFDerivWithin_of_isOpen 2 hLs hwmem] at key
  rw [key]
  have hw1 : iteratedFDerivWithin ℝ 2 fh s (L w) = iteratedFDeriv ℝ 2 fh (L w) :=
    iteratedFDerivWithin_of_isOpen 2 hso hmem
  rw [hw1]
  have hshift : iteratedFDeriv ℝ 2 fh (L w) = iteratedFDeriv ℝ 2 (Function.uncurry Q) (L w + ((0 : Euc d), y)) :=
    iteratedFDeriv_comp_add_right 2 ((0 : Euc d), y) (L w)
  rw [hshift]
  have hpt : L w + ((0 : Euc d), y) = (w, y) := by simp [hL]
  rw [hpt]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp [hL]
  have : ∏ _i : Fin 2, ‖L‖ ≤ 1 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hLn
  calc _ ≤ ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (w, y)‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

end HRS.MS.R26T8A
