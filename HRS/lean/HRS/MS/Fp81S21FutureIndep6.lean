import HRS.MS.Fp81S21FutureIndep5
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.MS.R26T3

/-- Every finite restriction of the retained source is jointly Gaussian. -/
theorem fp81s21_source_gaussian_process {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : E → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h))
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → E),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2))) :
    IsGaussianProcess W P := by
  constructor
  intro I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let Z : Ω → (Fin (Fintype.card I) → ℝ) := fun ω i => W (e.symm i).1 ω
  have hZm : AEMeasurable Z P :=
    (measurable_pi_iff.2 fun i => hWm _).aemeasurable
  have hZg : HRS.IsCenteredGaussian (P.map Z) :=
    s21g2_s11a_gauss_of_laws hZm fun c => ⟨_, hcomb _ c (fun i => (e.symm i).1)⟩
  let L : (Fin (Fintype.card I) → ℝ) →L[ℝ] (I → ℝ) :=
    { toFun := fun x i => x (e i)
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  have hL : (fun ω => I.restrict (W · ω)) = L ∘ Z := by
    funext ω i
    simp [L, Z, Finset.restrict_def]
  rw [hL]
  exact (HasGaussianLaw.mk hZm hZg.1).map L

/-- Orthogonal source subfamilies generate independent random elements. -/
theorem fp81s21_source_indep_of_orthogonal {Ω E S T : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : E → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h)) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → E),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (hcov : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h')
    (a : S → E) (b : T → E) (hab : ∀ s t, inner ℝ (a s) (b t) = 0) :
    IndepFun (fun ω s => W (a s) ω) (fun ω t => W (b t) ω) P := by
  have hg := (fp81s21_source_gaussian_process P W hWm hcomb).comp_right
    (Sum.elim a b)
  have hg' : IsGaussianProcess (Sum.elim (fun s => W (a s)) (fun t => W (b t))) P := by
    convert hg using 1
    funext x
    cases x <;> rfl
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero hg'
    (fun s => (hWm (a s)).aemeasurable) (fun t => (hWm (b t)).aemeasurable)
  intro s t
  have hmean (h : E) : ∫ ω, W h ω ∂P = 0 := by
    have hlaw := hcomb 1 (fun _ => 1) (fun _ => h)
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, one_smul] at hlaw
    have hi := integral_map (hWm h).aemeasurable
      (aestronglyMeasurable_id : AEStronglyMeasurable (id : ℝ → ℝ) (P.map (W h)))
    simpa [hlaw] using hi.symm
  rw [covariance_eq_sub (hW2 (a s)) (hW2 (b t)), hmean, hmean, mul_zero, sub_zero]
  simp only [Pi.mul_apply]
  rw [hcov, hab]

#print axioms fp81s21_source_gaussian_process
#print axioms fp81s21_source_indep_of_orthogonal

end HRS.Fp81.S21
end
