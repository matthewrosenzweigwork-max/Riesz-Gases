import HRS.ME.CondExample

/-!
# HRS.ME.TiltConv: the cosine-tilted conditioned limit (Example 5.12, second conjunct)

Assuming the centering clause `HRS.Main.centering_transition` (as hypothesis `hCT`, `type_of%`),
`v = C_β(ψ,ψ) > 0` and `|a| < 1`, the cosine-tilted expectations of bounded continuous `f ∘ Z_N`
under the tilt `(1 + a cos Z_N) / E[1 + a cos Z_N]` converge to `∫ f · cosineTiltDensity a v`.

Route.  With `ν_N = law(P_{N+1,β}) Z_{N+1}` (shifted by one as in `HRS.ME.CondExample`) and
`γ = gaussianReal 0 v.toNNReal`, the Gibbs integrals of `g ∘ Z` are the integrals of `g` against `ν_N`
(change of variables).  The normaliser `∫ (1 + a cos) dν_N` and the numerator
`∫ f · (1 + a cos) dν_N` converge (weak convergence tested on bounded continuous functions), and the
limit normaliser is `1 + a e^{-v/2} > 0`.  The Gaussian integral `∫ cos dγ = e^{-v/2}` comes from the
characteristic function, and the density identification uses `integral_gaussianReal_eq_integral_smul`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
open HRS.ME.CondExample

noncomputable section

namespace HRS.ME.TiltConv

/-- `|1 + a cos z| ≤ 2` when `|a| ≤ 1`. -/
theorem abs_one_add_mul_cos_le {a : ℝ} (ha : |a| ≤ 1) (z : ℝ) : |1 + a * Real.cos z| ≤ 2 := by
  have h1 : |a * Real.cos z| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha (Real.abs_cos_le_one z) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have h2 := abs_add_le (1 : ℝ) (a * Real.cos z)
  rw [abs_one] at h2
  linarith

/-- `∫ cos dN(0, v) = e^{-v/2}` (from the characteristic function of the Gaussian). -/
theorem integral_cos_gaussianReal (v : ℝ≥0) :
    ∫ x, Real.cos x ∂(gaussianReal 0 v) = Real.exp (-(v : ℝ) / 2) := by
  have hint : Integrable (fun x : ℝ => Complex.exp ((1 : ℝ) * x * Complex.I)) (gaussianReal 0 v) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp ((1 : ℝ) * x * Complex.I)).aestronglyMeasurable
    · simp [Complex.norm_exp]
  have h1 : ∫ x, Real.cos x ∂(gaussianReal 0 v)
      = (∫ x, Complex.exp ((1 : ℝ) * x * Complex.I) ∂(gaussianReal 0 v)).re := by
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    congr 1
    funext x
    simp [Complex.exp_ofReal_mul_I_re]
  have h2 := charFun_gaussianReal (μ := 0) (v := v) 1
  rw [charFun_apply_real] at h2
  rw [h1, h2]
  simp [Complex.exp_re]
  ring

/-- Density identification: `∫ f · cosineTiltDensity a v = (1 + a e^{-v/2})⁻¹ ∫ f (1 + a cos) dγ_v`. -/
theorem integral_cosineTilt_eq {v : ℝ} (hv : 0 < v) (a : ℝ) (f : ℝ → ℝ) :
    ∫ z, f z * HRS.cosineTiltDensity a v z =
      (1 + a * Real.exp (-v / 2))⁻¹ * ∫ z, f z * (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal) := by
  have hw : v.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hv).ne'
  have hvc : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal v hv.le
  rw [integral_gaussianReal_eq_integral_smul hw, ← integral_const_mul]
  congr 1
  funext z
  simp only [HRS.cosineTiltDensity, gaussianPDFReal, smul_eq_mul, sub_zero]
  rw [hvc]
  ring

/-- Bounded continuous tests of the shifted laws, with the Gibbs integrals rewritten as integrals
against `ν_N = shiftedLaw`. -/
theorem tilt_convergence {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (hCT : type_of% (@HRS.Main.centering_transition d))
    (hv : 0 < susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) (a : ℝ)
    (ha1 : |a| < 1) :
    ∀ f : ℝ → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) →
      Tendsto (fun N => ∫ X, f (linCoord (withDensityReal ρ) ψ X) * ((1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X)) /
          ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y)) ∂(canonicalGibbs (periodicRiesz d s) V N β))
          ∂(canonicalGibbs (periodicRiesz d s) V N β)) atTop
        (𝓝 (∫ z, f z * cosineTiltDensity a (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) z)) := by
  intro f hf hfb
  obtain ⟨M, hM⟩ := hfb
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  have hconv := (hCT hd (s := s) hs0 hsd V hV β hβ ρ hρ ψ hψ).1 hs
  set v := susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ with hvdef
  have hconv' : ∀ F : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, F x ∂(shiftedLaw s V β ρ ψ N)) atTop
      (𝓝 (∫ x, F x ∂(gaussianReal 0 v.toNNReal))) :=
    fun F => (tendsto_add_atTop_iff_nat 1).2 (hconv F)
  have hvc : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal v hv.le
  -- change of variables: Gibbs integrals of `g ∘ Z` are integrals against `ν_N`
  have hCOV : ∀ g : ℝ → ℝ, Measurable g → ∀ N : ℕ,
      ∫ X, g (linCoord (withDensityReal ρ) ψ X) ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β) =
        ∫ z, g z ∂(shiftedLaw s V β ρ ψ N) := by
    intro g hg N
    unfold shiftedLaw law
    exact (integral_map (linCoord_measurable (ρ := ρ) (N := N + 1) hψc).aemeasurable
      hg.aestronglyMeasurable).symm
  -- test functions
  have hg1c : Continuous (fun z : ℝ => 1 + a * Real.cos z) :=
    continuous_const.add (continuous_const.mul Real.continuous_cos)
  have hg1b : ∀ z, |1 + a * Real.cos z| ≤ 2 := fun z => abs_one_add_mul_cos_le ha1.le z
  have hg2c : Continuous (fun z : ℝ => f z * (1 + a * Real.cos z)) := hf.mul hg1c
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hg2b : ∀ z, |f z * (1 + a * Real.cos z)| ≤ M * 2 := fun z => by
    rw [abs_mul]
    exact mul_le_mul (hM z) (hg1b z) (abs_nonneg _) hM0
  -- limits of the normaliser and of the numerator
  have hc1 : Tendsto (fun N => ∫ z, (1 + a * Real.cos z) ∂(shiftedLaw s V β ρ ψ N)) atTop
      (𝓝 (∫ z, (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal))) :=
    conv_bc hconv' _ hg1c 2 hg1b
  have hc2 : Tendsto (fun N => ∫ z, f z * (1 + a * Real.cos z) ∂(shiftedLaw s V β ρ ψ N)) atTop
      (𝓝 (∫ z, f z * (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal))) :=
    conv_bc hconv' _ hg2c (M * 2) hg2b
  -- the limit normaliser
  have hcos : Integrable (fun z : ℝ => Real.cos z) (gaussianReal 0 v.toNNReal) :=
    integrable_of_bdd Real.continuous_cos.measurable 1 (fun z => Real.abs_cos_le_one z)
  have hγc : ∫ z, (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal) = 1 + a * Real.exp (-v / 2) := by
    have hi1 : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 v.toNNReal) := integrable_const 1
    rw [integral_add hi1 (hcos.const_mul a), integral_const, integral_const_mul,
      integral_cos_gaussianReal, hvc]
    simp
  have hE1 : Real.exp (-v / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE0 : 0 < Real.exp (-v / 2) := Real.exp_pos _
  have hcpos : 0 < 1 + a * Real.exp (-v / 2) := by
    have h1 : -|a| * Real.exp (-v / 2) ≤ a * Real.exp (-v / 2) :=
      mul_le_mul_of_nonneg_right (neg_abs_le a) hE0.le
    have h2 : |a| * Real.exp (-v / 2) ≤ |a| := mul_le_of_le_one_right (abs_nonneg a) hE1
    linarith
  have hL1ne : ∫ z, (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal) ≠ 0 := by
    rw [hγc]
    exact hcpos.ne'
  -- the limit, identified with the cosine-tilt density
  have hgoal : ∫ z, f z * cosineTiltDensity a v z =
      (∫ z, f z * (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal)) *
        (∫ z, (1 + a * Real.cos z) ∂(gaussianReal 0 v.toNNReal))⁻¹ := by
    rw [hγc, integral_cosineTilt_eq hv a f]
    ring
  -- the tilted Gibbs integrals, rewritten against `ν_N`
  have hrw : ∀ N : ℕ,
      ∫ X, f (linCoord (withDensityReal ρ) ψ X) * ((1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X)) /
          ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y))
            ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β))
          ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β) =
        (∫ z, f z * (1 + a * Real.cos z) ∂(shiftedLaw s V β ρ ψ N)) *
          (∫ z, (1 + a * Real.cos z) ∂(shiftedLaw s V β ρ ψ N))⁻¹ := by
    intro N
    have e1 : ∫ X, f (linCoord (withDensityReal ρ) ψ X) * (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X))
          ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β) =
        ∫ z, f z * (1 + a * Real.cos z) ∂(shiftedLaw s V β ρ ψ N) :=
      hCOV (fun z => f z * (1 + a * Real.cos z)) hg2c.measurable N
    have e2 : ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y))
          ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β) =
        ∫ z, (1 + a * Real.cos z) ∂(shiftedLaw s V β ρ ψ N) :=
      hCOV (fun z => 1 + a * Real.cos z) hg1c.measurable N
    rw [← e1, ← e2, ← integral_mul_const]
    congr 1
    funext X
    ring
  have hT : Tendsto (fun N : ℕ => ∫ X, f (linCoord (withDensityReal ρ) ψ X) *
      ((1 + a * Real.cos (linCoord (withDensityReal ρ) ψ X)) /
          ∫ Y, (1 + a * Real.cos (linCoord (withDensityReal ρ) ψ Y))
            ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β))
          ∂(canonicalGibbs (periodicRiesz d s) V (N + 1) β)) atTop
      (𝓝 (∫ z, f z * cosineTiltDensity a v z)) := by
    rw [hgoal]
    exact Tendsto.congr (fun N => (hrw N).symm) (hc2.mul (hc1.inv₀ hL1ne))
  exact (tendsto_add_atTop_iff_nat 1).1 hT

end HRS.ME.TiltConv

end
