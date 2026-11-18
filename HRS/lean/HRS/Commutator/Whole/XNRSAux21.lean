import HRS.Commutator.Whole.XNRSAux20

/-!
# Packet X-NRS, part 21: the real kernel of an even Fourier cutoff
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- A smooth compactly supported real function as a complex Schwartz function. -/
def xsch (ψ : Euc d → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) : 𝓢(Euc d, ℂ) :=
  (show HasCompactSupport (fun ξ => ((ψ ξ : ℝ) : ℂ)) from
    hc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hψ)

lemma xsch_apply (ψ : Euc d → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (ξ : Euc d) :
    xsch ψ hψ hc ξ = ((ψ ξ : ℝ) : ℂ) := rfl

/-- `∫ cos(2π⟨z,ξ⟩) ψ(ξ) dξ`. -/
def xKr (ψ : Euc d → ℝ) (z : Euc d) : ℝ := ∫ ξ, Real.cos (2 * Real.pi * inner ℝ z ξ) * ψ ξ

lemma xinvF_even (S : 𝓢(Euc d, ℂ)) (ψ : Euc d → ℝ) (hS : ∀ ξ, S ξ = (ψ ξ : ℂ))
    (he : ∀ ξ, ψ (-ξ) = ψ ξ) (z : Euc d) :
    (𝓕⁻ S : 𝓢(Euc d, ℂ)) z = ((xKr ψ z : ℝ) : ℂ) := by
  rw [xfourierInv_apply, SchwartzMap.fourier_coe, Real.fourier_eq']
  set g : Euc d → ℂ := fun v => Complex.exp (((-2 * Real.pi * inner ℝ v (-z) : ℝ) : ℂ) * Complex.I) • S v
    with hg
  have hgi : Integrable g := by
    have := (Real.fourierIntegral_convergent_iff (V := Euc d) (E := ℂ) (-z)).2
      (S.integrable (μ := volume))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [hg, Circle.smul_def, Real.fourierChar_apply]
    congr 2
    push_cast; ring
  have hgn : Integrable (fun v => g (-v)) := hgi.comp_neg
  have h1 : ∫ v, g v = ∫ v, g (-v) := (integral_neg_eq_self g volume).symm
  have key : ∀ v, g v + g (-v) = 2 * ((Real.cos (2 * Real.pi * inner ℝ z v) * ψ v : ℝ) : ℂ) := by
    intro v
    have hx1 : ((-2 * Real.pi * inner ℝ v (-z) : ℝ) : ℂ) = ((2 * Real.pi * inner ℝ z v : ℝ) : ℂ) := by
      rw [inner_neg_right, real_inner_comm]; push_cast; ring
    have hx2 : ((-2 * Real.pi * inner ℝ (-v) (-z) : ℝ) : ℂ) = -((2 * Real.pi * inner ℝ z v : ℝ) : ℂ) := by
      rw [inner_neg_neg, real_inner_comm]; push_cast; ring
    simp only [hg, smul_eq_mul, hS, he, hx1, hx2]
    have := Complex.two_cos (((2 * Real.pi * inner ℝ z v : ℝ) : ℂ))
    rw [neg_mul]
    push_cast at this ⊢
    rw [neg_mul] at this
    linear_combination (-(ψ v : ℂ)) * this
  have h2 : 2 * ∫ v, g v = ∫ v, (2 * ((Real.cos (2 * Real.pi * inner ℝ z v) * ψ v : ℝ) : ℂ)) := by
    calc 2 * ∫ v, g v = (∫ v, g v) + ∫ v, g (-v) := by rw [← h1]; ring
      _ = ∫ v, (g v + g (-v)) := (integral_add hgi hgn).symm
      _ = _ := integral_congr_ae (Eventually.of_forall key)
  rw [integral_const_mul, integral_complex_ofReal] at h2
  have h3 : (2 : ℂ) * ∫ v, g v = 2 * ((xKr ψ z : ℝ) : ℂ) := by
    rw [h2]; rfl
  exact mul_left_cancel₀ two_ne_zero h3

end HRS.Commutator.Whole.XNRS
