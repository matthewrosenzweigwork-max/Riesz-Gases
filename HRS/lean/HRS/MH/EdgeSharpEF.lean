import HRS.MH.EdgeSharpDefs
import HRS.Main.HeadlineEdgeworth
import HRS.Main.Q42Aux1
import HRS.PDE.TorusFPSpec

/-!
# EdgeSharp packets H0, K1, E1, F1 (statement-verbatim copies of `HRS/MH/EdgeSharpSpec.lean`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS HRS.Main

variable {d : ℕ}

/-! ### Helpers (smoothness on the torus) -/

private lemma isSmooth_const_mul_fn (c : ℝ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Torus.IsSmooth (fun x => c * f x) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact contDiff_const.mul hf

private lemma isSmooth_add_fn {f g : Torus d → ℝ} (hf : Torus.IsSmooth f) (hg : Torus.IsSmooth g) :
    Torus.IsSmooth (fun x => f x + g x) := by
  unfold Torus.IsSmooth Torus.IsCk at *
  exact hf.add hg

private lemma isSmooth_cosTest_fn (k : Lattice d) : Torus.IsSmooth (PDE.cosTest k) := by
  unfold PDE.cosTest
  exact isSmooth_const_mul_fn _ (HRS.d1_isSmooth_cosMode k)

/-! ### Group H0: smoothness of the explicit functions -/

/-- [H0] `φ₀` and the densities `χ^r` are smooth (finite combinations of `Torus.cosMode`, smooth by `HRS.d1_isSmooth_cosMode`,
`HRS/PDE/TorusFPSpec.lean:174`; `ContDiff.add`, `ContDiff.const_smul`, `Real.sqrt` constant). -/
theorem phi0_isSmooth (k : Lattice d) (b : ℝ) : Torus.IsSmooth (phi0 k b) := by
  unfold phi0
  exact isSmooth_add_fn (isSmooth_cosTest_fn k) (isSmooth_const_mul_fn b (isSmooth_cosTest_fn _))

theorem crossDensity_isSmooth (s β : ℝ) (k : Lattice d) (b r : ℝ) :
    Torus.IsSmooth (crossDensity d s β k b r) := by
  unfold crossDensity
  exact isSmooth_add_fn (isSmooth_const_mul_fn _ (isSmooth_cosTest_fn k))
    (isSmooth_const_mul_fn _ (isSmooth_cosTest_fn _))

/-! ### Group K: the cubic coefficient at `t = (0,0,0)` -/

private lemma setIntegral_Icc_self_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) : ∫ r in Set.Icc (0 : ℝ) 0, F r = 0 := by
  rw [Set.Icc_self]
  exact setIntegral_measure_zero F (by simp)

/-- [K1] At `t = 0` both time integrals in `cubicKappa` are over `Set.Icc 0 0 = {0}` (a null set) and vanish; only `μ°(r₀³)` remains.  Route:
`Set.Icc_self`, `Measure.restrict_singleton`/`setIntegral_measure_zero`, `Real.volume_singleton`, `cyc3` unfolded, `simp`. -/
theorem cubicKappa_zero_times (D : DynData d) (ρ : ℝ → Torus d → ℝ) (β β₀ : ℝ) (μ0 : Measure (Torus d))
    (φ : Fin 3 → Torus d → ℝ) (χ : Fin 3 → ℝ → Torus d → ℝ) :
    cubicKappa D ρ β β₀ μ0 (fun _ => 0) φ χ =
      ∫ x, responseInverse (periodicRiesz d D.s) μ0 β₀ (propagator D ρ 0 0 (φ 0)) x *
        responseInverse (periodicRiesz d D.s) μ0 β₀ (propagator D ρ 0 0 (φ 1)) x *
        responseInverse (periodicRiesz d D.s) μ0 β₀ (propagator D ρ 0 0 (φ 2)) x ∂μ0 := by
  unfold cubicKappa cyc3
  simp only [min_self, setIntegral_Icc_self_zero, add_zero, zero_add, mul_zero, sub_zero]

/-! ### Group E: `S.ρ = 1` -/

private lemma convFun_one_torus (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) :
    convFun (periodicRiesz d s) (fun _ => (1 : ℝ)) x = 0 := by
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  unfold convFun
  simp only [mul_one]
  rw [integral_sub_left_eq_self (periodicRiesz d s) (volume : Measure (Torus d)) x]
  exact (integral_periodicRiesz hd hs0 hsd).2

/-- [E1] `1` is a thermal density for `V = 0` (the periodic Riesz kernel has mean zero).  Route: copy `HRS.ME.FamW.convFun_one` and `isThermal_one`
(`HRS/ME/FamWA.lean:69-81`, not in the shared build): `integral_sub_left_eq_self` with `Measure.IsNegInvariant` of `volume` on the torus
(`Measure.pi.isNegInvariant`), `integral_periodicRiesz hd hs0 hsd` (`HRS/Kernel/Riesz.lean:3727`, `.2`). -/
theorem isThermalDensity_one_zero (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) :
    IsThermalDensity (periodicRiesz d s) (fun _ => (0 : ℝ)) β (fun _ => (1 : ℝ)) := by
  refine ⟨⟨fun _ => zero_le_one, measurable_const, by simp⟩, fun x => ?_⟩
  simp [convFun_one_torus hd hs0 hsd]

/-! ### Group F: the prepared covariance on the uniform measure -/

/-- [F1] `C_{β,Leb}(f, φ₀) = ∫ f R φ₀ = A ∫ f ψ_k + B ∫ f ψ_{2k}` for continuous `f` (`β₀ = β > 0`, so `preparedCov` is the `susceptibilityCov` branch).
Route: unfold `preparedCov` (`if_neg hβ.ne'`), `susceptibilityCov`, `l2Inner`, `projMean`, `pair`; `q42_responseInverse_eq` (`HRS/Main/Q42Aux1.lean:400`,
`α = 1`, `γ = b`) gives `R φ₀ =ᵐ A ψ_k + B ψ_{2k}` (continuous, so integrable), hence `∫ R φ₀ = 0` (`q42_int_cosTest`, `q42_two_smul_ne`) and
`∫ (f - ∫f) R φ₀ = ∫ f R φ₀` (`integral_sub`, `integral_mul_const`); `integral_congr_ae`, `integral_add`, `integral_const_mul`. -/
theorem preparedCov_phi0 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (b : ℝ) {f : Torus d → ℝ} (hf : Continuous f) :
    preparedCov d s β (volume : Measure (Torus d)) f (phi0 k b) =
      (1 + β * rieszCoeff d s k)⁻¹ * (∫ x, f x * PDE.cosTest k x) +
        b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹ * (∫ x, f x * PDE.cosTest ((2 : ℤ) • k) x) := by
  have hk2 : (2 : ℤ) • k ≠ 0 := q42_two_smul_ne hk
  have hR := q42_responseInverse_eq hd hs0 hsd hβ k hk (phi0 k b) 1 b (fun x => by simp [phi0])
  have hc1 : Continuous (fun x => PDE.cosTest k x) :=
    continuous_const.mul (Torus.continuous_cosMode k)
  have hc2 : Continuous (fun x => PDE.cosTest ((2 : ℤ) • k) x) :=
    continuous_const.mul (Torus.continuous_cosMode _)
  have hi1 : Integrable (fun x => PDE.cosTest k x) (volume : Measure (Torus d)) :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => PDE.cosTest ((2 : ℤ) • k) x) (volume : Measure (Torus d)) :=
    hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfi1 : Integrable (fun x => f x * PDE.cosTest k x) (volume : Measure (Torus d)) :=
    (hf.mul hc1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfi2 : Integrable (fun x => f x * PDE.cosTest ((2 : ℤ) • k) x) (volume : Measure (Torus d)) :=
    (hf.mul hc2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the a.e. form `Q` of `R φ₀`
  have hQc : Continuous (fun x => (1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
      (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) :=
    (continuous_const.mul hc1).add (continuous_const.mul hc2)
  have hQi : Integrable (fun x => (1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
      (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x)
        (volume : Measure (Torus d)) :=
    (hi1.const_mul _).add (hi2.const_mul _)
  have hQint : ∫ x, ((1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
      (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) = 0 := by
    rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      q42_int_cosTest hk, q42_int_cosTest hk2]
    simp
  have hfQi : Integrable (fun x => f x * ((1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
      (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x))
        (volume : Measure (Torus d)) :=
    (hf.mul hQc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold preparedCov
  rw [if_neg hβ.ne']
  unfold susceptibilityCov l2Inner projMean pair
  have key : ∫ x, (f x - ∫ y, f y) *
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β (phi0 k b) x =
      ∫ x, (f x - ∫ y, f y) * ((1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
        (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) :=
    integral_congr_ae (hR.mono fun x hx => by simp only [hx])
  rw [key]
  have gen : ∀ Q : Torus d → ℝ, Integrable (fun x => f x * Q x) (volume : Measure (Torus d)) →
      Integrable Q (volume : Measure (Torus d)) → ∫ x, Q x = 0 →
      ∫ x, (f x - ∫ y, f y) * Q x = ∫ x, f x * Q x := by
    intro Q h1 h2 h3
    have hfun : (fun x => (f x - ∫ y, f y) * Q x) = fun x => f x * Q x - (∫ y, f y) * Q x :=
      funext fun x => by ring
    rw [hfun, integral_sub h1 (h2.const_mul _), integral_const_mul, h3, mul_zero, sub_zero]
  rw [gen _ hfQi hQi hQint]
  have hfe : (fun x => f x * ((1 * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
      (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x)) =
      fun x => (1 * (1 + β * rieszCoeff d s k)⁻¹) * (f x * PDE.cosTest k x) +
        (b * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * (f x * PDE.cosTest ((2 : ℤ) • k) x) := by
    funext x; ring
  rw [hfe, integral_add (hfi1.const_mul _) (hfi2.const_mul _), integral_const_mul,
    integral_const_mul, one_mul]

end HRS.MH.EdgeSharp
