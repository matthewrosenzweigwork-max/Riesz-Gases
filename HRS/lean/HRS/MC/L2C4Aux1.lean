import HRS.MC.L2C3
import HRS.MC.L2C1

/-!
# Packet L2C-4, helper 1: weighted gradient energy and the centering bound

* `l2c4_cov_le`: for a density path bounded by `M` on `[0,t]` the noise covariance is at most `2qM` times the
  unweighted integrated gradient energy (smooth integrand, so all integrals are of continuous functions).
* `l2c4_Q_bound`: `‖Q_β φ‖²_{L²} ≤ C ‖φ‖²_{L²}` for continuous `φ`, with `C = 2 + 2Λ₀` depending on `sup ρ_β`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C4

variable {d : ℕ}

theorem l2c4_integrable_of_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The noise covariance is bounded by `2qM` times the unweighted integrated gradient energy. -/
theorem l2c4_cov_le (D : DynData d) (ρ : ℝ → Torus d → ℝ) {q t M : ℝ} (φ : Torus d → ℝ) (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, 0 ≤ ρ r x ∧ ρ r x ≤ M)
    (hc : ∀ r ∈ Set.Icc (0 : ℝ) t, Continuous fun x => ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2)
    (hI : ContinuousOn (fun r => ∫ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2) (Set.Icc 0 t)) :
    noiseCovariance D ρ q t φ φ ≤
      2 * q * M * ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2 := by
  unfold noiseCovariance
  have hM : ∀ r ∈ Set.Icc (0 : ℝ) t, 0 ≤ M := fun r hr => (hρ r hr 0).1.trans (hρ r hr 0).2
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ∫ x, inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) * ρ r x ≤
        M * ∫ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2 := by
    intro r hr
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
      ((l2c4_integrable_of_cont (hc r hr)).const_mul M) (Filter.Eventually.of_forall fun x => ?_)
    · simp only [Pi.zero_apply]
      exact mul_nonneg real_inner_self_nonneg (hρ r hr x).1
    · simp only [real_inner_self_eq_norm_sq]
      exact mul_comm M _ ▸ mul_le_mul_of_nonneg_left (hρ r hr x).2 (sq_nonneg _)
  have hnn : ∀ r ∈ Set.Icc (0 : ℝ) t,
      0 ≤ ∫ x, inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) * ρ r x :=
    fun r hr => integral_nonneg fun x => mul_nonneg real_inner_self_nonneg (hρ r hr x).1
  have hint : IntegrableOn (fun r => M * ∫ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2) (Set.Icc 0 t) :=
    (hI.integrableOn_Icc).const_mul M
  have hle : ∫ r in Set.Icc (0 : ℝ) t,
      ∫ x, inner ℝ (Torus.grad (propagator D ρ r t φ) x) (Torus.grad (propagator D ρ r t φ) x) * ρ r x ≤
      ∫ r in Set.Icc (0 : ℝ) t, M * ∫ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2 := by
    refine integral_mono_of_nonneg ?_ hint ?_
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hnn)
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hle
  calc _ ≤ 2 * q * (M * ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ‖Torus.grad (propagator D ρ r t φ) x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-- `‖Q_β φ‖²_{L²} ≤ (2 + 2Λ₀) ‖φ‖²_{L²}` for continuous `φ` and a continuous probability density `ρ ≤ Λ₀`. -/
theorem l2c4_Q_bound {ρ : Torus d → ℝ} (hprob : IsProbDensity ρ) (hρc : Continuous ρ) {Λ₀ : ℝ}
    (hup : ∀ x, ρ x ≤ Λ₀) {φ : Torus d → ℝ} (hφ : Continuous φ) :
    PDE.l2NormSq (projMean (withDensityReal ρ) φ) ≤ (2 + 2 * Λ₀) * PDE.l2NormSq φ := by
  have : IsProbabilityMeasure (withDensityReal ρ) := HRS.PDE.MFSemigroup.isProb_withDensityReal hprob
  set m : ℝ := ∫ x, φ x ∂(withDensityReal ρ) with hm
  have hΛ : 0 ≤ Λ₀ := (hprob.nonneg 0).trans (hup 0)
  have hA : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  -- `m² ≤ ∫ φ² dμ ≤ Λ₀ ∫ φ²`
  have hjensen : m ^ 2 ≤ ∫ x, φ x ^ 2 ∂(withDensityReal ρ) := by
    have := (Even.convexOn_pow (n := 2) even_two).map_integral_le (μ := withDensityReal ρ) (f := φ)
      (continuousOn_pow 2) isClosed_univ (Filter.Eventually.of_forall fun x => Set.mem_univ _)
      (hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((hφ.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    simpa [hm] using this
  have hμ : ∫ x, φ x ^ 2 ∂(withDensityReal ρ) ≤ Λ₀ * ∫ x, φ x ^ 2 := by
    rw [HRS.PDE.MFPairing.integral_withDensityReal hρc.measurable hprob.nonneg, ← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
      ((l2c4_integrable_of_cont (hφ.pow 2)).const_mul Λ₀) (Filter.Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (hprob.nonneg x) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right (hup x) (sq_nonneg _)
  have hQ : ∫ x, (projMean (withDensityReal ρ) φ x) ^ 2 ≤ ∫ x, (2 * φ x ^ 2 + 2 * m ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · exact l2c4_integrable_of_cont (((hφ.pow 2).const_mul 2).add continuous_const)
    · simp only [projMean, pair]
      rw [← hm]
      nlinarith [sq_nonneg (φ x + m)]
  have hint : ∫ x, (2 * φ x ^ 2 + 2 * m ^ 2) = 2 * (∫ x, φ x ^ 2) + 2 * m ^ 2 := by
    have h := integral_add (μ := (volume : Measure (Torus d))) (f := fun x => 2 * φ x ^ 2)
      (g := fun _ => 2 * m ^ 2) ((l2c4_integrable_of_cont (hφ.pow 2)).const_mul 2) (integrable_const _)
    rw [h, integral_const_mul]
    simp
  unfold PDE.l2NormSq
  nlinarith [hQ, hint, hjensen, hμ]

end HRS.MC.L2C4
