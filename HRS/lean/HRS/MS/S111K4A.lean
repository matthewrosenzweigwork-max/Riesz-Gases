import HRS.Prob.Gaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# S11.1 / T01 (S11K4), part A: representation of a centered Gaussian vector as a linear image of the standard one

For a finite index type `ι`, `k4gm ι` is the product of standard Gaussians on `ι → ℝ`.  A centered Gaussian random
vector `X : Ω → (ι → ℝ)` has law `(k4gm ι).map (R *ᵥ ·)` for a matrix `R` (the square root of its covariance), and the
coordinate second moments of `k4gm ι` are the Kronecker delta.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace HRS.MS.S111K4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard Gaussian product measure on `ι → ℝ`. -/
def k4gm (ι : Type*) [Fintype ι] : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)

instance k4gm_prob : IsProbabilityMeasure (k4gm ι) := by unfold k4gm; infer_instance

theorem k4_integral_eval (f : ℝ → ℝ) (hf : Continuous f) (k : ι) :
    ∫ y, f (y k) ∂(k4gm ι) = ∫ x, f x ∂(gaussianReal 0 1) := by
  have h := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) k).map_eq
  conv_rhs => rw [← h]
  exact (integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable).symm

theorem k4_integral_cross (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (k l : ι) (hkl : k ≠ l) :
    ∫ y, f (y k) * g (y l) ∂(k4gm ι) = (∫ x, f x ∂(gaussianReal 0 1)) * ∫ x, g x ∂(gaussianReal 0 1) := by
  have hind := iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hkl)
  have := h2.integral_fun_comp_mul_comp (f := f) (g := g)
    (measurable_pi_apply k).aemeasurable (measurable_pi_apply l).aemeasurable
    (by simpa using hf.aestronglyMeasurable) (by simpa using hg.aestronglyMeasurable)
  rw [← k4_integral_eval f hf k, ← k4_integral_eval g hg l]
  exact this

/-- Coordinate second moments of the standard Gaussian vector. -/
theorem k4_second_moment (k l : ι) :
    ∫ y, y k * y l ∂(k4gm ι) = if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h
    simp only [if_true]
    have := k4_integral_eval (ι := ι) (fun x => x ^ 2) (by fun_prop) k
    rw [HRS.gauss_sq] at this
    simpa [sq] using this
  · simp only [h, if_false]
    have := k4_integral_cross (ι := ι) (fun x => x) (fun x => x) (by fun_prop) (by fun_prop) k l h
    simpa using this

theorem k4_memLp_coord (k : ι) : MemLp (fun y : ι → ℝ => y k) 2 (k4gm ι) := by
  have h := (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) k).map_eq
  have h2 : MemLp (id : ℝ → ℝ) 2 ((k4gm ι).map (fun y : ι → ℝ => y k)) := by
    rw [k4gm, h]; exact memLp_id_gaussianReal 2
  exact (memLp_map_measure_iff aestronglyMeasurable_id (measurable_pi_apply k).aemeasurable).1 h2

theorem k4_integrable_coord_mul (k l : ι) : Integrable (fun y : ι → ℝ => y k * y l) (k4gm ι) :=
  (k4_memLp_coord k).integrable_mul (k4_memLp_coord l)

/-- Second moment of a linear form of the standard Gaussian vector. -/
theorem k4_linear_sq (a : ι → ℝ) :
    ∫ y, (∑ k, a k * y k) ^ 2 ∂(k4gm ι) = ∑ k, a k ^ 2 := by
  have e : ∀ y : ι → ℝ, (∑ k, a k * y k) ^ 2 = ∑ k, ∑ l, (a k * a l) * (y k * y l) := fun y => by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
    (k4_integrable_coord_mul k l).const_mul _]
  have : ∀ k ∈ (Finset.univ : Finset ι), ∫ y, ∑ l, (a k * a l) * (y k * y l) ∂(k4gm ι) = a k ^ 2 := by
    intro k _
    rw [integral_finset_sum _ fun l _ => (k4_integrable_coord_mul k l).const_mul _]
    simp_rw [integral_const_mul, k4_second_moment]
    simp [sq]
  rw [Finset.sum_congr rfl this]

end HRS.MS.S111K4
