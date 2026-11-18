import HRS.Energy.FeatureMap

/-!
# Relocated proofs for `HRS/Energy/FeatureMap.lean`, part 1

* `isSpectralSymbol_negSpectralCoeff_proof`: the negative-exponent symbol is a spectral symbol.
* `fm1_tsum_pair`: a series over `ℤ^d` of an even summable function vanishing at `0` is twice the
  series over the positive half-lattice (`Lattice.IsPosHalf`).
* `fm1_summable_pos`: a bounded modulation of the coefficients is summable over the positive half.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MH.FeatureMap

open HRS

variable {d : ℕ}

theorem fm1_enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm Lattice.toEuc
  rw [← norm_neg]
  congr 1
  ext i
  simp

theorem fm1_negSpectralCoeff_neg (s c : ℝ) (k : Lattice d) :
    negSpectralCoeff d s c (-k) = negSpectralCoeff d s c k := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    unfold negSpectralCoeff
    rw [if_neg hk, if_neg hk', fm1_enorm_neg]

theorem isSpectralSymbol_negSpectralCoeff_proof : type_of% @HRS.isSpectralSymbol_negSpectralCoeff := by
  intro d s c hs hc
  exact ⟨fun k => negSpectralCoeff_nonneg d s hc.le k, summable_negSpectralCoeff d hs c,
    fun k => fm1_negSpectralCoeff_neg s c k, by simp [negSpectralCoeff]⟩

/-- Pairing: a series over `ℤ^d` of an even summable `h` with `h 0 = 0` is twice the series over the
lexicographically positive half. -/
theorem fm1_tsum_pair (h : Lattice d → ℝ) (hs : Summable h) (h0 : h 0 = 0)
    (hev : ∀ k, h (-k) = h k) :
    ∑' k, h k = 2 * ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, h k := by
  have hz : ¬ Lattice.IsPosHalf (0 : Lattice d) := fun h' => lt_irrefl _ h'
  have hφs : Summable ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) := hs.indicator _
  have hφn : Summable (fun k => ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) (-k)) :=
    (Equiv.summable_iff (Equiv.neg (Lattice d))).mpr hφs
  have key : ∀ k, ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) k +
      ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) (-k) = h k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [Set.indicator_apply, hz, h0]
    · by_cases hp : Lattice.IsPosHalf k
      · have hn : ¬ Lattice.IsPosHalf (-k) := fun h' => ((Torus.isPosHalf_neg k hk).1 h') hp
        simp [Set.indicator_apply, hp, hn]
      · have hn : Lattice.IsPosHalf (-k) := (Torus.isPosHalf_neg k hk).2 hp
        simp [Set.indicator_apply, hp, hn, hev]
  have hsplit : ∑' k, h k = ∑' k, ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) k +
      ∑' k, ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) (-k) := by
    rw [show (∑' k, h k) = ∑' k, (({k : Lattice d | Lattice.IsPosHalf k}.indicator h) k +
        ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) (-k)) from
      tsum_congr fun k => (key k).symm]
    exact Summable.tsum_add hφs hφn
  have hneg : ∑' k, ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) (-k) =
      ∑' k, ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) k :=
    Equiv.tsum_eq (Equiv.neg (Lattice d)) _
  have hsub : ∑' k : {k : Lattice d // Lattice.IsPosHalf k}, h k =
      ∑' k, ({k : Lattice d | Lattice.IsPosHalf k}.indicator h) k :=
    tsum_subtype {k : Lattice d | Lattice.IsPosHalf k} h
  rw [hsub, hsplit, hneg]
  ring

/-- A bounded modulation of a nonnegative summable family is summable over the positive half. -/
theorem fm1_summable_pos {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (f : Lattice d → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    Summable fun k : {k : Lattice d // Lattice.IsPosHalf k} => a k.1 * f k.1 := by
  refine Summable.of_norm_bounded (has.comp_injective Subtype.val_injective) fun k => ?_
  show ‖a k.1 * f k.1‖ ≤ a k.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k.1)]
  exact mul_le_of_le_one_right (ha0 k.1) (hf k.1)

end HRS.MH.FeatureMap
