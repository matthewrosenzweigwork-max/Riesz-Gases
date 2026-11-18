import HRS.MS.WsStatAux22

/-!
# S21 packet I-1: convolution contraction of `W_p` on a Banach space and Gaussian convolutions

* `s21_wasserstein_conv_le`: `W_p(P * gamma, Q * gamma) <= W_p(P, Q)` for probability measures on a separable Banach space
  (the proof of `wassersteinE_add_indep_le`, stated for the measures `((P.prod gamma).map (+))`).
* `s21_gauss_conv`: `multivariateGaussian 0 S1 * multivariateGaussian 0 S2 = multivariateGaussian 0 (S1 + S2)` for positive
  semidefinite `S1, S2` (characteristic functions).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole

theorem s21_wasserstein_conv_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (p : ℝ) (hp : 1 ≤ p) (P Q γ : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure γ] :
    wassersteinE p ((P.prod γ).map (fun z : B × B => z.1 + z.2))
        ((Q.prod γ).map (fun z : B × B => z.1 + z.2)) ≤ wassersteinE p P Q := by
  have hp0 : 0 < p := by linarith
  refine le_iInf fun π => ?_
  obtain ⟨π, hπ⟩ := π
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hkey : ∀ (f : B × B → B), Measurable f → ∀ (ρ : Measure B), π.map f = ρ →
      ((π.prod γ).map (fun w : (B × B) × B => f w.1 + w.2)) =
        (ρ.prod γ).map (fun z : B × B => z.1 + z.2) := by
    intro f hf ρ hρ
    have e1 : (fun w : (B × B) × B => f w.1 + w.2) =
        (fun z : B × B => z.1 + z.2) ∘ (Prod.map f id) := by ext w <;> simp
    rw [e1, ← Measure.map_map (by fun_prop) (by fun_prop), ← hρ]
    congr 1
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
  set T : (B × B) × B → B × B := fun w => (w.1.1 + w.2, w.1.2 + w.2) with hT
  have hTm : Measurable T := by rw [hT]; fun_prop
  have hcoup : IsCoupling ((π.prod γ).map T)
      ((P.prod γ).map (fun z : B × B => z.1 + z.2))
      ((Q.prod γ).map (fun z : B × B => z.1 + z.2)) := by
    constructor
    · rw [Measure.map_map measurable_fst hTm]
      exact hkey Prod.fst measurable_fst _ hπ.1
    · rw [Measure.map_map measurable_snd hTm]
      exact hkey Prod.snd measurable_snd _ hπ.2
  refine (wassersteinE_le_cost hcoup).trans ?_
  refine le_of_eq ?_
  congr 1
  rw [lintegral_map (by fun_prop) hTm]
  have : ∀ w : (B × B) × B, ENNReal.ofReal (‖(T w).1 - (T w).2‖ ^ p) =
      ENNReal.ofReal (‖w.1.1 - w.1.2‖ ^ p) := fun w => by
    simp [hT]
  simp only [this]
  rw [lintegral_prod _ (by fun_prop)]
  simp

theorem s21_gauss_conv {p : ℕ} {S1 S2 : Matrix (Fin p) (Fin p) ℝ} (h1 : S1.PosSemidef) (h2 : S2.PosSemidef) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S1).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S2)).map (fun z => z.1 + z.2) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (S1 + S2) := by
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [charFun_map_add_prod_eq_mul, Pi.mul_apply, charFun_multivariateGaussian h1,
    charFun_multivariateGaussian h2, charFun_multivariateGaussian (h1.add h2), ← Complex.exp_add]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, Matrix.add_mulVec, dotProduct_add,
    Complex.ofReal_add]
  ring

theorem s21_gauss_smul {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosSemidef) (c : ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map (fun z => c • z) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) ((c ^ 2) • S) := by
  have hS' : ((c ^ 2) • S).PosSemidef := hS.smul (sq_nonneg c)
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [charFun_map_smul, charFun_multivariateGaussian hS, charFun_multivariateGaussian hS']
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  simp [Matrix.mulVec_smul, dotProduct_smul]
  ring

end HRS.MS.S21
