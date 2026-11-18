import HRS.Main.A8PAux38

/-!
# Packet A8P, part 39: the `ι`-indexed smooth and Wasserstein bounds
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

theorem a8p_smoothDist_relabel (e : ι ≃ Fin q) (μ ν : Measure (EuclideanSpace ℝ (Fin q)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    smoothDist 2 (μ.map (a8pV e)) (ν.map (a8pV e)) ≤ smoothDist 2 μ ν := by
  have h := smoothDist_map_clm_le (a8pV e) 2 μ ν
  have h1 : max 1 (‖a8pV e‖ ^ 2) = 1 := by
    refine max_eq_left ?_
    exact pow_le_one₀ (norm_nonneg _) (a8pV_opNorm_le e)
  rw [h1, one_mul] at h
  exact h

theorem a8p_wass_relabel (e : ι ≃ Fin q) (p : ℝ) (hp : 1 ≤ p) (μ ν : Measure (EuclideanSpace ℝ (Fin q)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinE p (μ.map (a8pV e)) (ν.map (a8pV e)) ≤ wassersteinE p μ ν := by
  have h := wassersteinE_map_clm_le (a8pV e) p hp μ ν
  refine h.trans ?_
  have : ENNReal.ofReal ‖a8pV e‖ ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (a8pV_opNorm_le e)
  calc ENNReal.ofReal ‖a8pV e‖ * wassersteinE p μ ν ≤ 1 * wassersteinE p μ ν :=
        mul_le_mul_of_nonneg_right this (zero_le)
    _ = _ := one_mul _

end HRS.Main.A8P
