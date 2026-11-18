import HRS.Commutator.Whole.ApproxAux

/-!
# Density approximation (packet CMX-APPROX, helpers, part 2)

Helpers carry the prefix `cmxSA_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Dominated convergence for the pair functional. -/
lemma cmxSA_pairGen_tendsto {N : ℕ} (k : Euc d → Euc d → ℝ)
    (hk : Measurable (fun q : Euc d × Euc d => k q.1 q.2)) (X : Fin N → Euc d)
    (ρ : Euc d → ℝ) (h₁ : ∀ i, Integrable (fun y => k (X i) y * ρ y))
    (H : Integrable (fun q : Euc d × Euc d => k q.1 q.2 * ρ q.1 * ρ q.2))
    (ρm : ℕ → Euc d → ℝ) (hmeas : ∀ m, Measurable (ρm m))
    (hpt : ∀ x, Tendsto (fun m => ρm m x) atTop (𝓝 (ρ x)))
    (hdom : ∀ᶠ m in atTop, ∀ x, |ρm m x| ≤ 2 * |ρ x|) :
    Tendsto (fun m => pairGen k X (ρm m)) atTop (𝓝 (pairGen k X ρ)) := by
  unfold pairGen
  have hk1 : ∀ a, Measurable (fun y => k a y) := fun a =>
    hk.comp (measurable_const.prodMk measurable_id)
  have t1 : ∀ i : Fin N, Tendsto (fun m => ∫ y, k (X i) y * ρm m y) atTop
      (𝓝 (∫ y, k (X i) y * ρ y)) := by
    intro i
    refine tendsto_integral_filter_of_dominated_convergence (fun y => 2 * ‖k (X i) y * ρ y‖)
      (Filter.Eventually.of_forall fun m => ((hk1 _).mul (hmeas m)).aestronglyMeasurable) ?_
      ((h₁ i).norm.const_mul 2) (Filter.Eventually.of_forall fun y => ?_)
    · filter_upwards [hdom] with m hm
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [norm_mul, Real.norm_eq_abs]
      calc |k (X i) y| * |ρm m y| ≤ |k (X i) y| * (2 * |ρ y|) := by gcongr; exact hm y
        _ = _ := by ring
    · exact ((hpt y).const_mul _)
  have t2 : Tendsto (fun m => ∫ x, ∫ y, k x y * ρm m x * ρm m y) atTop
      (𝓝 (∫ x, ∫ y, k x y * ρ x * ρ y)) := by
    have hG : ∀ m, Measurable (fun q : Euc d × Euc d => k q.1 q.2 * ρm m q.1 * ρm m q.2) :=
      fun m => (hk.mul ((hmeas m).comp measurable_fst)).mul ((hmeas m).comp measurable_snd)
    have hbd : ∀ᶠ m in atTop, ∀ q : Euc d × Euc d,
        ‖k q.1 q.2 * ρm m q.1 * ρm m q.2‖ ≤ 4 * ‖k q.1 q.2 * ρ q.1 * ρ q.2‖ := by
      filter_upwards [hdom] with m hm q
      simp only [norm_mul, Real.norm_eq_abs]
      have a1 := hm q.1
      have a2 := hm q.2
      calc |k q.1 q.2| * |ρm m q.1| * |ρm m q.2|
          ≤ |k q.1 q.2| * (2 * |ρ q.1|) * (2 * |ρ q.2|) := by gcongr
        _ = _ := by ring
    have hint : ∀ᶠ m in atTop, Integrable (fun q : Euc d × Euc d =>
        k q.1 q.2 * ρm m q.1 * ρm m q.2) := by
      filter_upwards [hbd] with m hm
      exact Integrable.mono' (H.norm.const_mul 4) (hG m).aestronglyMeasurable
        (Filter.Eventually.of_forall hm)
    have hlim : Tendsto (fun m => ∫ q : Euc d × Euc d, k q.1 q.2 * ρm m q.1 * ρm m q.2) atTop
        (𝓝 (∫ q : Euc d × Euc d, k q.1 q.2 * ρ q.1 * ρ q.2)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun q => 4 * ‖k q.1 q.2 * ρ q.1 * ρ q.2‖)
        (Filter.Eventually.of_forall fun m => (hG m).aestronglyMeasurable)
        (by filter_upwards [hbd] with m hm; exact Filter.Eventually.of_forall hm)
        (H.norm.const_mul 4) (Filter.Eventually.of_forall fun q => ?_)
      exact ((tendsto_const_nhds.mul (hpt q.1)).mul (hpt q.2))
    have e1 : ∫ q : Euc d × Euc d, k q.1 q.2 * ρ q.1 * ρ q.2 =
        ∫ x, ∫ y, k x y * ρ x * ρ y := by
      rw [Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using H)]
    rw [← e1]
    refine hlim.congr' ?_
    filter_upwards [hint] with m hm
    rw [Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hm)]
  refine ((tendsto_const_nhds.sub ((tendsto_finsetSum _ fun i _ => t1 i).const_mul _))).add t2

end HRS.Commutator.Whole
