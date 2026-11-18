import HRS.MD.EQLZCap8
import HRS.Equilibrium.Q84dAuxD
import HRS.Appendix.B15Aux2

/-!
# EQ-LZ packet CAP, helper 9: the Gibbs law on the big torus

For the canonical Gibbs law `μ` (`d ≥ 2`, smooth `V`, `H` bounded below): `μ` is a probability measure, `μ ≪ volume`,
`μ ≤ c₀ volume`; the image `ν = μ.map (d1_configEquiv)` on `𝕋^{Nd}` satisfies `ν ≤ c₀ volume` and `ν (badSet) = 0`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology

namespace HRS.MD.EQLZ.Cap

variable {d N : ℕ}

theorem gibbs_density_le {g V : Torus d → ℝ} {β c : ℝ} (hgm : Measurable g) (hVm : Measurable V)
    (hlow : ∀ X : Config d N, -c ≤ canonicalHamiltonian g V X) (hβ : 0 < β) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧
      canonicalGibbs g V N β ≤ ENNReal.ofReal c0 • (volume : Measure (Config d N)) := by
  have hZ := Q84d.q84d_Z_pos hgm hVm hlow hβ.le
  set Z := canonicalPartition g V N β with hZdef
  refine ⟨Z⁻¹ * Real.exp (β * c), by positivity, ?_⟩
  refine Measure.le_iff.2 fun s hs => ?_
  unfold canonicalGibbs
  rw [Measure.smul_apply, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 : ∫⁻ x in s, ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V x)) ≤
      ENNReal.ofReal (Real.exp (β * c)) * volume s := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono measurable_const fun x _ => ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith [hlow x]
  calc (ENNReal.ofReal Z)⁻¹ * ∫⁻ x in s, ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V x))
      ≤ (ENNReal.ofReal Z)⁻¹ * (ENNReal.ofReal (Real.exp (β * c)) * volume s) :=
        mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (Z⁻¹ * Real.exp (β * c)) * volume s := by
        rw [← mul_assoc, ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), ENNReal.ofReal_inv_of_pos hZ]

theorem map_le_of_le {μ : Measure (Config d N)} {c0 : ℝ}
    (h : μ ≤ ENNReal.ofReal c0 • (volume : Measure (Config d N))) :
    μ.map (d1_configEquiv d N) ≤ ENNReal.ofReal c0 • (volume : Measure (Torus (N * d))) := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.map_apply (d1_configEquiv d N).measurable hs]
  refine (Measure.le_iff'.1 h _).trans (le_of_eq ?_)
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    (d1_configEquiv_measurePreserving d N).measure_preimage hs.nullMeasurableSet]

theorem map_badSet_null {μ : Measure (Config d N)} (hac : μ ≪ volume) (hd : 1 ≤ d) :
    μ.map (d1_configEquiv d N) (badSet d N) = 0 := by
  rw [Measure.map_apply (d1_configEquiv d N).measurable (isClosed_badSet d N).measurableSet]
  have : (d1_configEquiv d N) ⁻¹' badSet d N = collisionSet d N := by
    ext X; simp [badSet]
  rw [this]
  exact hac (b15_volume_collisionSet hd)

/-- The facts about the Gibbs law needed for the core theorem. -/
theorem gibbs_facts (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {V : Torus d → ℝ}
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) ∧
    canonicalGibbs (periodicRiesz d s) V N β ≪ (volume : Measure (Config d N)) ∧
    ∃ c0 : ℝ, 0 ≤ c0 ∧ canonicalGibbs (periodicRiesz d s) V N β ≤
      ENNReal.ofReal c0 • (volume : Measure (Config d N)) := by
  have hgm : Measurable (periodicRiesz d s : Torus d → ℝ) :=
    CoercAux.measurable_periodicRiesz_one (by omega) hs0 hsd
  have hVc : Continuous V := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).continuous
  obtain ⟨B, hB⟩ := periodicRiesz_ge hd hs0 hsd
  obtain ⟨Vm, hVm⟩ := b15_bounded_of_continuous hVc
  have hlow : ∀ X : Config d N, -((N : ℝ) * Vm + N * max B 0) ≤
      canonicalHamiltonian (periodicRiesz d s) V X := fun X =>
    b15_hamiltonian_lower (le_max_right B 0)
      (fun z => (neg_le_neg (le_max_left _ _)).trans (hB z)) hVm X
  exact ⟨Q84d.q84d_gibbs_isProb hgm hVc.measurable hlow hβ.le, Q84d.q84d_gibbs_ac,
    gibbs_density_le hgm hVc.measurable hlow hβ⟩

end HRS.MD.EQLZ.Cap
