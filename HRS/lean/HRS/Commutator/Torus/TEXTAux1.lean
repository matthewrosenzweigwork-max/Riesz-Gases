import HRS.Commutator.Torus.TPOSAux4

/-!
# T-EXT-A helpers, part 1: convolution on the torus

`textConv K f (x) = ∫ K(x-y) f(y) dy`; integrability, the Fourier coefficient identity
`fcoef (K ⋆ f) k = fcoef K k · fcoef f k` for `K, f ∈ L¹(𝕋^d)`, and the uniqueness theorem
(an integrable function with vanishing Fourier coefficients vanishes a.e.).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Convolution on the torus. -/
def textConv (K f : Torus d → ℝ) (x : Torus d) : ℝ := ∫ y, K (x - y) * f y

lemma text_integrable_prod {K f : Torus d → ℝ} (hK : Integrable K) (hf : Integrable f) :
    Integrable (fun p : Torus d × Torus d => K (p.1 - p.2) * f p.2) (volume.prod volume) := by
  have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf hK
    (μ := (volume : Measure (Torus d)))
  refine this.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [mul_comm]

lemma text_integrable_conv {K f : Torus d → ℝ} (hK : Integrable K) (hf : Integrable f) :
    Integrable (textConv K f) :=
  (text_integrable_prod hK hf).integral_prod_left

lemma text_fcoef_conv {K f : Torus d → ℝ} (hK : Integrable K) (hf : Integrable f)
    (k : Lattice d) :
    Torus.fcoef (textConv K f) k = Torus.fcoef K k * Torus.fcoef f k := by
  have hprod := text_integrable_prod hK hf
  have hmc : Continuous (fun x : Torus d => Torus.mode (-k) x) := Torus.continuous_mode (-k)
  set G : Torus d × Torus d → ℂ := fun p =>
    Torus.mode (-k) p.1 * (((K (p.1 - p.2) * f p.2 : ℝ)) : ℂ) with hG
  have hGint : Integrable G (volume.prod volume) := by
    have h1 : Integrable (fun p : Torus d × Torus d => Torus.mode (-k) p.1 *
        (((K (p.1 - p.2) * f p.2 : ℝ)) : ℂ)) (volume.prod volume) :=
      hprod.ofReal.bdd_mul (hmc.comp continuous_fst).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => (Torus.norm_mode (-k) _).le)
    exact h1
  have h1 : ∀ x : Torus d, Torus.mode (-k) x * ((textConv K f x : ℝ) : ℂ) =
      ∫ y, G (x, y) := by
    intro x
    unfold textConv
    rw [← integral_complex_ofReal, ← integral_const_mul]
  unfold Torus.fcoef
  simp_rw [h1]
  rw [integral_integral_swap hGint]
  have h2 : ∀ y : Torus d, ∫ x, G (x, y) =
      Torus.mode (-k) y * (f y : ℂ) * ∫ x, Torus.mode (-k) x * (K x : ℂ) := by
    intro y
    have h3 : ∀ x : Torus d, G (x, y) = Torus.mode (-k) y * (f y : ℂ) *
        (Torus.mode (-k) (x - y) * (K (x - y) : ℂ)) := by
      intro x
      simp only [hG]
      have : Torus.mode (-k) x = Torus.mode (-k) (x - y) * Torus.mode (-k) y := by
        rw [← Torus.mode_add_arg]; simp
      rw [this]; push_cast; ring
    simp_rw [h3]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun x => Torus.mode (-k) x * (K x : ℂ)) y
  simp_rw [h2]
  rw [integral_mul_const, mul_comm]

end HRS.Commutator.TorusNote
