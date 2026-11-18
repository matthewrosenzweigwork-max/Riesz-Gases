import HRS.MS.WadAux85

/-!
# S8.3, packet S8E-4, part 2: first-order weighted norms

`s8e_opnorm_le_partials`: `‖L‖ ≤ d B` if `|L e_i| ≤ B`.  `s8e_wsup1_bounds`: finiteness of `weightedSupE 1 (-M) f` gives
`|f| ≤ Φ⟨·⟩^M` and `‖Df‖ ≤ d Φ ⟨·⟩^M`; `s8e_memCM_of_j`: `C_M^1 ⊆ C_M`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_opnorm_le_partials (L : Euc d →L[ℝ] ℝ) {B : ℝ}
    (hB : ∀ i : Fin d, |L (EuclideanSpace.single i (1 : ℝ))| ≤ B) : ‖L‖ ≤ d * B := by
  have hB0 : 0 ≤ B ∨ d = 0 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact Or.inr h
    · exact Or.inl ((abs_nonneg _).trans (hB ⟨0, h⟩))
  have hdB : 0 ≤ (d : ℝ) * B := by
    rcases hB0 with h | h
    · positivity
    · subst h; simp
  refine ContinuousLinearMap.opNorm_le_bound _ hdB fun v => ?_
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' v
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left] using this.symm
  have hLv : L v = ∑ i, v i * L (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  rw [Real.norm_eq_abs, hLv]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |v i * L (EuclideanSpace.single i (1 : ℝ))| ≤ ∑ _i : Fin d, ‖v‖ * B := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using PiLp.norm_apply_le v i) (hB i) (abs_nonneg _) (norm_nonneg _)
    _ = d * B * ‖v‖ := by simp; ring

theorem s8e_wsup1_bounds {M : ℝ} {f : Euc d → ℝ} (h : weightedSupE 1 (-M) f ≠ ⊤) :
    (∀ x, |f x| ≤ (weightedSupE 1 (-M) f).toReal * jbracket x ^ M) ∧
      ∀ x, ‖fderiv ℝ f x‖ ≤ d * (weightedSupE 1 (-M) f).toReal * jbracket x ^ M := by
  have hle := (s83_wsup_le_iff (M := M) (K := (weightedSupE 1 (-M) f).toReal) ENNReal.toReal_nonneg 1 f).1
    (by rw [ENNReal.ofReal_toReal h])
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := hle 0 (by norm_num) (fun i => i.elim0) x
    simpa [partialDeriv] using this
  · refine (s8e_opnorm_le_partials (fderiv ℝ f x) (B := (weightedSupE 1 (-M) f).toReal * jbracket x ^ M)
      fun i => ?_).trans (le_of_eq (by ring))
    have := hle 1 le_rfl (fun _ => i) x
    simpa [partialDeriv, iteratedFDeriv_one_apply] using this

theorem s8e_memCM_of_j {M : ℝ} {f : Euc d → ℝ} (hf : MemCMj M 1 f) : MemCM M f := by
  refine ⟨hf.1.continuous, ?_⟩
  have := hf.2 0 (by norm_num) (fun i => i.elim0)
  simpa [partialDeriv] using this

end HRS.MS.Wad
