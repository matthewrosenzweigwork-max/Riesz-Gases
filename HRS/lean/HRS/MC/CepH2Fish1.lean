import HRS.MC.CepH2Ent3

/-!
# CEPH2, Fisher information test fields: the integrand `g_ζ` is continuous, periodic and bounded
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The integrand of the `ζ`-functional in `cep_cylFisher`. -/
def h2_fint (θ : ℝ) (U : Ch N → ℝ) (ζ : Ch N → Ch N) (z : Ch N) : ℝ :=
  -2 * ∑ k : Fin N, fderiv ℝ (fun w => ζ w k) z (EuclideanSpace.single k 1)
    + 2 * θ⁻¹ * inner ℝ (gradient U z) (ζ z) - ‖ζ z‖ ^ 2

theorem h2_zeta_far {ζ : Ch N → Ch N} (hR : ∃ R : ℝ, ∀ z, R ≤ Metric.infDist z (cep_Alcove N) → ζ z = 0) :
    ∃ R' : ℝ, ∀ z, R' < ‖h2_perp z‖ → ζ z = 0 := by
  obtain ⟨R, hR⟩ := hR
  refine ⟨R + Real.sqrt N, fun z hz => hR z ?_⟩
  have := h2_infDist_ge z
  linarith

section
variable {ζ : Ch N → Ch N}

theorem h2_zk_contDiff (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (k : Fin N) :
    ContDiff ℝ 1 (fun w => ζ w k) := by
  have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ζ w k) := ContDiff.comp (g := fun x : Ch N => x k) (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff hζ
  exact this.of_le (by exact_mod_cast le_top)

theorem h2_zk_periodic (hper : ∀ z, ζ (z + cep_diag N) = ζ z) (k : Fin N) (z : Ch N) :
    (fun w => ζ w k) (z + cep_diag N) = (fun w => ζ w k) z := by
  simp only [hper]

theorem h2_zk_far {R : ℝ} (hfar : ∀ z, R < ‖h2_perp z‖ → ζ z = 0) (k : Fin N) :
    ∀ z, R < ‖h2_perp z‖ → (fun w => ζ w k) z = 0 := fun z hz => by
  simp only [hfar z hz]; rfl

theorem h2_fint_continuous {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (θ : ℝ)
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) : Continuous (h2_fint θ U ζ) := by
  unfold h2_fint
  have hζc : Continuous ζ := hζ.continuous
  have hd : ∀ k : Fin N, Continuous fun z => fderiv ℝ (fun w => ζ w k) z (EuclideanSpace.single k 1) :=
    fun k => ((h2_zk_contDiff hζ k).continuous_fderiv (by simp)).clm_apply continuous_const
  refine ((continuous_const.mul (continuous_finsetSum _ fun k _ => hd k)).add
    (continuous_const.mul ((h2_continuous_gradient hU).inner hζc))).sub (hζc.norm.pow 2)

theorem h2_fint_periodic {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) (θ : ℝ)
    (hper : ∀ z, ζ (z + cep_diag N) = ζ z) (z : Ch N) :
    h2_fint θ U ζ (z + cep_diag N) = h2_fint θ U ζ z := by
  unfold h2_fint
  rw [hper z, h2_gradient_periodic hUper z]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h2_fderiv_periodic (h2_zk_periodic hper k) z]

theorem h2_fint_far {U : Ch N → ℝ} (θ : ℝ) {R : ℝ} (hfar : ∀ z, R < ‖h2_perp z‖ → ζ z = 0) {z : Ch N}
    (hz : R < ‖h2_perp z‖) : h2_fint θ U ζ z = 0 := by
  unfold h2_fint
  rw [hfar z hz]
  have : ∀ k : Fin N, fderiv ℝ (fun w => ζ w k) z = 0 := fun k =>
    h2_fderiv_eq_zero_of_far (h2_zk_far hfar k) hz
  simp [this]

theorem h2_fint_bdd {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) (θ : ℝ)
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) (hper : ∀ z, ζ (z + cep_diag N) = ζ z) {R : ℝ}
    (hfar : ∀ z, R < ‖h2_perp z‖ → ζ z = 0) : ∃ C : ℝ, ∀ z, |h2_fint θ U ζ z| ≤ C := by
  obtain ⟨C, hC⟩ := h2_bdd_tube (h2_fint_continuous hU θ hζ) (h2_fint_periodic hUper θ hper) R
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : ‖h2_perp z‖ ≤ R
  · exact (by simpa using hC z hz : |h2_fint θ U ζ z| ≤ C).trans (le_max_left _ _)
  · rw [h2_fint_far θ hfar (not_le.1 hz), abs_zero]
    exact le_max_right _ _

end

end HRS.MC.CepH2
