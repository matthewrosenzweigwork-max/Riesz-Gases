import HRS.Sections.ScrnAux13

/-!
# Packet SCRN, part 14: Parseval identities for the covariances of the transported statistics

* `scrn_parseval_re`: `∑_k Re(conj û(k) v̂(k)) = ∫ u v` for continuous real `u, v`.
* `scrn_parseval_grad`: `∑_k (2π|k|)² Re(conj f̂(k) ĝ(k)) = ∫ ⟨∇f, ∇g⟩` for `C²` functions.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace HRS

variable {d : ℕ}

open PDE PDE.ClassicalAux

theorem scrn_parseval_re {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v) :
    HasSum (fun k : Lattice d => (conj (coeffOf u k) * coeffOf v k).re) (∫ x, u x * v x) := by
  have hmu : MemLp (fun x => (u x : ℂ)) 2 volume := (memLp_two_of_continuous hu).ofReal
  have hmv : MemLp (fun x => (v x : ℂ)) 2 volume := (memLp_two_of_continuous hv).ofReal
  have hP := hasSum_parseval (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) hmu hmv
  have e : (∫ t, conj ((u t : ℂ)) * (v t : ℂ)) = ((∫ x, u x * v x : ℝ) : ℂ) := by
    have h1 : (∫ t, conj ((u t : ℂ)) * (v t : ℂ)) = ∫ t, (((u t * v t : ℝ)) : ℂ) := by
      congr 1; funext x; simp [Complex.conj_ofReal]
    rw [h1]
    exact integral_ofReal (𝕜 := ℂ)
  rw [e] at hP
  exact Complex.reCLM.hasSum hP

theorem scrn_parseval_grad {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) :
    HasSum (fun k : Lattice d => (2 * Real.pi * Lattice.enorm k) ^ 2 *
      (conj (coeffOf f k) * coeffOf g k).re)
      (∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x)) := by
  have hf1 : Torus.IsCk 1 f := hf.of_le (by norm_num)
  have hg1 : Torus.IsCk 1 g := hg.of_le (by norm_num)
  have hcf : ∀ j, Continuous (Torus.partialDeriv j f) := fun j => continuous_partialDeriv j f hf1
  have hcg : ∀ j, Continuous (Torus.partialDeriv j g) := fun j => continuous_partialDeriv j g hg1
  have hj : ∀ j : Fin d, HasSum (fun k : Lattice d => ((2 * Real.pi * (k j : ℝ)) ^ 2 *
      (conj (coeffOf f k) * coeffOf g k).re))
      (∫ x, Torus.partialDeriv j f x * Torus.partialDeriv j g x) := by
    intro j
    have := scrn_parseval_re (hcf j) (hcg j)
    rw [coeffOf_partialDeriv j f hf1, coeffOf_partialDeriv j g hg1] at this
    have e : (fun k : Lattice d => ((2 * Real.pi * (k j : ℝ)) ^ 2 *
        (conj (coeffOf f k) * coeffOf g k).re)) =
        fun k => (conj (derivCoeff j (coeffOf f) k) * derivCoeff j (coeffOf g) k).re := by
      funext k
      have h1 : conj (derivCoeff j (coeffOf f) k) * derivCoeff j (coeffOf g) k =
          (((2 * Real.pi * (k j : ℝ)) ^ 2 : ℝ) : ℂ) * (conj (coeffOf f k) * coeffOf g k) := by
        simp only [derivCoeff, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
          map_intCast]
        have hI : Complex.I ^ 2 = -1 := Complex.I_sq
        push_cast
        linear_combination (-(2 * (Real.pi : ℂ) * (k j : ℂ)) ^ 2 * (conj (coeffOf f k) * coeffOf g k)) * hI
      rw [h1, Complex.re_ofReal_mul]
    rw [e]; exact this
  have hsum := hasSum_sum (s := Finset.univ) (fun (j : Fin d) _ => hj j)
  have hint : ∀ j : Fin d, Integrable (fun x => Torus.partialDeriv j f x * Torus.partialDeriv j g x) :=
    fun j => ((hcf j).mul (hcg j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI : ∫ x, inner ℝ (Torus.grad f x) (Torus.grad g x) =
      ∑ j : Fin d, ∫ x, Torus.partialDeriv j f x * Torus.partialDeriv j g x := by
    rw [← integral_finset_sum _ (fun j _ => hint j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [inner_euc, grad_apply]
  have hen : ∀ k : Lattice d, (2 * Real.pi * Lattice.enorm k) ^ 2 =
      ∑ j : Fin d, (2 * Real.pi * (k j : ℝ)) ^ 2 := by
    intro k
    have : Lattice.enorm k ^ 2 = ∑ i, ((k i : ℤ) : ℝ) ^ 2 := by
      unfold Lattice.enorm Lattice.toEuc
      rw [EuclideanSpace.norm_sq_eq]
      simp
    rw [mul_pow, this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hI]
  convert hsum using 1
  funext k
  rw [hen k, Finset.sum_mul]

end HRS
