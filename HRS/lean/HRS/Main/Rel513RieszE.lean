import HRS.Main.Rel513RieszD

/-!
# HRS.Main.Rel513RieszE -- packet rel513, part 5: generic probability lemmas for `stationary_remainder_L2`

* `rel513_eLpNorm_sq_centered`: `‖c (Y - E Y)‖²_{L²(P)} = c² Var(Y)` (in `ℝ≥0∞`);
* `rel513_le_of_sq_le`: `x² ≤ ofReal(a²) → x ≤ ofReal a`;
* `rel513_map_coord`, `rel513_integral_stat`: for an exchangeable law the mean of `N⁻¹ ∑ f(X_i)` is
  `∫ f d(first marginal)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

theorem rel513_le_of_sq_le {x : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a) (h : x ^ 2 ≤ ENNReal.ofReal (a ^ 2)) :
    x ≤ ENNReal.ofReal a := by
  rw [ENNReal.ofReal_pow ha] at h
  by_contra hc
  exact absurd h (not_le.2 ((ENNReal.pow_lt_pow_left_iff (by norm_num)).2 (not_le.1 hc)))

theorem rel513_eLpNorm_sq_centered {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (hY : AEStronglyMeasurable Y P) (c : ℝ) :
    (eLpNorm (fun ω => c * (Y ω - ∫ ω', Y ω' ∂P)) 2 P) ^ 2 =
      ENNReal.ofReal (c ^ 2) * evariance Y P := by
  have hm : AEStronglyMeasurable (fun ω => c * (Y ω - ∫ ω', Y ω' ∂P)) P :=
    (hY.sub aestronglyMeasurable_const).const_mul c
  rw [← Quad.lintegral_enorm_sq_eq_eLpNorm_sq hm]
  unfold evariance
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  simp only [enorm_mul, mul_pow]
  congr 1
  rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem rel513_map_coord {N : ℕ} (hN : 0 < N) {Q : Measure (Config d N)} (hQ : IsExchangeable Q)
    (i : Fin N) :
    Q.map (fun X : Config d N => X i) = firstMarginal Q := by
  unfold firstMarginal
  rw [dif_pos hN]
  have h := hQ (Equiv.swap (⟨0, hN⟩ : Fin N) i)
  have hm : Measurable (fun X : Config d N => X ∘ (Equiv.swap (⟨0, hN⟩ : Fin N) i)) :=
    (permMeasEquiv _).measurable
  have h1 : Q.map (fun X : Config d N => X ⟨0, hN⟩) =
      (Q.map (fun X : Config d N => X ∘ (Equiv.swap (⟨0, hN⟩ : Fin N) i))).map
        (fun X : Config d N => X ⟨0, hN⟩) := by rw [h]
  rw [Measure.map_map (measurable_pi_apply _) hm] at h1
  rw [h1]
  congr 1

theorem rel513_integral_stat {N : ℕ} (hN : 0 < N) {Q : Measure (Config d N)}
    [IsProbabilityMeasure Q] (hQ : IsExchangeable Q) {f : Torus d → ℝ} (hf : Measurable f)
    (hint : Integrable f (firstMarginal Q)) :
    ∫ X, (N : ℝ)⁻¹ * ∑ i, f (X i) ∂Q = ∫ x, f x ∂(firstMarginal Q) := by
  have hi : ∀ i : Fin N, Integrable (fun X : Config d N => f (X i)) Q := by
    intro i
    have h := rel513_map_coord hN hQ i
    have : Integrable f (Q.map (fun X : Config d N => X i)) := by rw [h]; exact hint
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 this
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
  have : ∀ i : Fin N, ∫ X, f (X i) ∂Q = ∫ x, f x ∂(firstMarginal Q) := by
    intro i
    rw [← rel513_map_coord hN hQ i, integral_map (measurable_pi_apply i).aemeasurable
      hf.aestronglyMeasurable]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end HRS.Main

end
