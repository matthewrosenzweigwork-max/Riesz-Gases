import HRS.PDE.TorusFPExistAux4

/-!
# D1 existence, helper 5: extension of a positive functional from smooth functions and Riesz

Generic (PDE-free) machinery: a positive normalised linear functional on the smooth functions on
`𝕋^n`, bounded by the sup norm, is the integral against a probability measure.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped CompactlySupported

namespace HRS

variable {n : ℕ}

/-- Smooth functions as a submodule of `C(𝕋^n, ℝ)`. -/
def d1_smoothSub (n : ℕ) : Submodule ℝ C(Torus n, ℝ) where
  carrier := {g | Torus.IsSmooth (g : Torus n → ℝ)}
  add_mem' {a b} ha hb := by
    have := d1_isSmooth_comb 1 1 ha hb
    have e : ⇑(a + b) = fun x => 1 * a x + 1 * b x := by funext x; simp
    show Torus.IsSmooth (⇑(a + b))
    rw [e]; exact this
  zero_mem' := d1_isSmooth_const (n := n) 0
  smul_mem' c g hg := by
    have := d1_isSmooth_comb c 0 hg (d1_isSmooth_const (n := n) 0)
    have e : ⇑(c • g) = fun x => c * g x + 0 * 0 := by funext x; simp
    show Torus.IsSmooth (⇑(c • g))
    rw [e]; exact this

theorem d1_smoothSub_dense : DenseRange (d1_smoothSub n).subtype := by
  rw [Metric.denseRange_iff]
  intro g r hr
  obtain ⟨ψ, hψ, hψg⟩ := d1_exists_smooth_approx g.continuous (half_pos hr)
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  refine ⟨⟨⟨ψ, hψc⟩, hψ⟩, ?_⟩
  rw [dist_eq_norm]
  have : ‖g - (⟨ψ, hψc⟩ : C(Torus n, ℝ))‖ ≤ r / 2 := by
    rw [ContinuousMap.norm_le _ (half_pos hr).le]
    intro x
    simpa [Real.norm_eq_abs] using hψg x
  exact lt_of_le_of_lt this (half_lt_self hr)

/-- Extension of a bounded positive linear functional from the smooth functions. -/
theorem d1_extend_functional (lam : d1_smoothSub n →ₗ[ℝ] ℝ)
    (hb : ∀ g : d1_smoothSub n, |lam g| ≤ ‖(g : C(Torus n, ℝ))‖)
    (hpos : ∀ g : d1_smoothSub n, (∀ x, 0 ≤ (g : C(Torus n, ℝ)) x) → 0 ≤ lam g) :
    ∃ Λ : C(Torus n, ℝ) →L[ℝ] ℝ, (∀ g, |Λ g| ≤ ‖g‖) ∧
      (∀ g : d1_smoothSub n, Λ (g : C(Torus n, ℝ)) = lam g) ∧
      ∀ g : C(Torus n, ℝ), (∀ x, 0 ≤ g x) → 0 ≤ Λ g := by
  let e : d1_smoothSub n →ₗ[ℝ] C(Torus n, ℝ) := (d1_smoothSub n).subtype
  have hnorm : ∀ g : d1_smoothSub n, ‖lam g‖ ≤ 1 * ‖e g‖ := fun g => by
    simpa [e, Real.norm_eq_abs] using hb g
  let Λ : C(Torus n, ℝ) →L[ℝ] ℝ := lam.extendOfNorm e
  have hext : ∀ g : d1_smoothSub n, Λ (g : C(Torus n, ℝ)) = lam g := fun g =>
    LinearMap.extendOfNorm_eq d1_smoothSub_dense ⟨1, hnorm⟩ g
  have hbound : ∀ g, |Λ g| ≤ ‖g‖ := by
    intro g
    have := LinearMap.norm_extendOfNorm_apply_le d1_smoothSub_dense 1 hnorm g
    rw [← Real.norm_eq_abs]
    simpa using this
  refine ⟨Λ, hbound, hext, ?_⟩
  intro g hg
  by_contra hneg
  rw [not_le] at hneg
  set ε : ℝ := -(Λ g) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨ψ, hψ, hψg⟩ := d1_exists_smooth_approx g.continuous hεpos
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  have hψ' : Torus.IsSmooth (fun x => ψ x + ε) := by
    have := d1_isSmooth_comb 1 ε hψ (d1_isSmooth_const (n := n) 1)
    convert this using 1
    funext x; simp
  let G : d1_smoothSub n := ⟨⟨fun x => ψ x + ε, hψc.add continuous_const⟩, hψ'⟩
  have hG0 : ∀ x, 0 ≤ (G : C(Torus n, ℝ)) x := by
    intro x
    have := hψg x
    have h2 := abs_le.1 this
    have := hg x
    show 0 ≤ ψ x + ε
    linarith [h2.1, h2.2]
  have h1 : 0 ≤ lam G := hpos G hG0
  have h2 : |Λ (g - (G : C(Torus n, ℝ)))| ≤ ‖g - (G : C(Torus n, ℝ))‖ := hbound _
  have h3 : ‖g - (G : C(Torus n, ℝ))‖ ≤ 2 * ε := by
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro x
    have := abs_le.1 (hψg x)
    rw [Real.norm_eq_abs, abs_le]
    show -(2 * ε) ≤ g x - (ψ x + ε) ∧ g x - (ψ x + ε) ≤ 2 * ε
    constructor <;> linarith [this.1, this.2]
  rw [map_sub, hext G] at h2
  have := (abs_le.1 (h2.trans h3)).2
  have := (abs_le.1 (h2.trans h3)).1
  rw [hε] at *
  linarith


/-- Riesz–Markov–Kakutani on the compact space `𝕋^n`: a positive normalised continuous linear
functional is the integral against a probability measure. -/
theorem d1_exists_measure_of_functional (Λ : C(Torus n, ℝ) →L[ℝ] ℝ)
    (hpos : ∀ g : C(Torus n, ℝ), (∀ x, 0 ≤ g x) → 0 ≤ Λ g) (h1 : Λ 1 = 1) :
    ∃ ν : Measure (Torus n), IsProbabilityMeasure ν ∧ ∀ g : C(Torus n, ℝ), ∫ x, g x ∂ν = Λ g := by
  let Λc : C_c(Torus n, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀
      { toFun := fun g => Λ g.toContinuousMap
        map_add' := fun f g => by
          rw [← map_add]; congr 1
        map_smul' := fun c f => by
          simp only [RingHom.id_apply]
          rw [← map_smul]; congr 1 }
      (fun g hg => hpos _ (fun x => by simpa using hg x))
  have hint : ∀ g : C(Torus n, ℝ), ∫ x, g x ∂(RealRMK.rieszMeasure Λc) = Λ g := by
    intro g
    have := RealRMK.integral_rieszMeasure Λc ⟨g, HasCompactSupport.of_compactSpace _⟩
    exact this
  refine ⟨RealRMK.rieszMeasure Λc, ?_, hint⟩
  constructor
  have h := hint 1
  rw [h1] at h
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h
  have hfin : IsFiniteMeasure (RealRMK.rieszMeasure Λc) := inferInstance
  have : (RealRMK.rieszMeasure Λc) Set.univ = 1 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have : ((RealRMK.rieszMeasure Λc) Set.univ).toReal = 1 := h
    rw [this]; simp
  exact this

end HRS
