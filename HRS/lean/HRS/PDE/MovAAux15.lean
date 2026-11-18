import HRS.PDE.MovAAux14

/-!
# MOVA Aux15: the weak form of the mean-field equation in terms of `∫ ψ · pdeRHS`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_integral_ibp (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) :
    ∫ x, Torus.partialDeriv j f x * g x = -∫ x, f x * Torus.partialDeriv j g x :=
  PDE.integral_partialDeriv_mul j f g hf hg

theorem mova_int_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  mova_integrable_of_continuous hf

theorem mova_integral_sum_cont {ι : Type*} (s : Finset ι) (u : ι → Torus d → ℝ)
    (hu : ∀ i, Continuous (u i)) : ∫ x, ∑ i ∈ s, u i x = ∑ i ∈ s, ∫ x, u i x :=
  integral_finsetSum _ fun i _ => mova_int_cont (hu i)

/-- The flux component `f_j = β⁻¹∂_jρ + ρ(∂_jV + F_j)`. -/
def mova_fj (D : DynData d) (ρ : Torus d → ℝ) (j : Fin d) (y : Torus d) : ℝ :=
  D.invβ * Torus.partialDeriv j ρ y + ρ y * (Torus.partialDeriv j D.V y + mova_F D ρ j y)

theorem mova_pdeRHS_eq (D : DynData d) (ρ : Torus d → ℝ) (x : Torus d) :
    mova_pdeRHS D ρ x = ∑ j, Torus.partialDeriv j (mova_fj D ρ j) x := rfl

theorem mova_fj_isCk (D : DynData d) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ) (hV : Torus.IsCk 2 D.V)
    (j : Fin d) : Torus.IsCk 1 (mova_fj D ρ j) := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hFj : Torus.IsCk 1 (mova_F D ρ j) := by
    rw [mova_F_eq D hρ1]; exact mova_isCk_one_convFun hgi (mova_isCk_partialDeriv hρ j)
  exact mova_isCk_add (mova_isCk_const_mul _ (mova_isCk_partialDeriv hρ j))
    (mova_isCk_mul hρ1 (mova_isCk_add (mova_isCk_partialDeriv hV j) hFj))

/-- The weak form integrand equals `∫ ψ · pdeRHS`. -/
theorem mova_wk_eq (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) {ρ : Torus d → ℝ}
    (hρ : Torus.IsCk 2 ρ) (hdens : IsProbDensity ρ) (hV : Torus.IsCk 2 D.V) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) :
    pair (withDensityReal ρ) (fun x => D.invβ * Torus.laplacian ψ x -
        inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) +
      interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
    ∫ x, ψ x * mova_pdeRHS D ρ x := by
  have hd := b15_one_le_d D
  have hρ1 := mova_isCk_one_of_two hρ
  have hψ1 := mova_isCk_one_of_two hψ
  have hV1 := mova_isCk_one_of_two hV
  have hρc := mova_continuous_of_isCk hρ
  have hgi := mova_integrable_periodicRiesz hd D.hs0 D.hsd
  have hdρ : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ρ) := fun j => mova_isCk_partialDeriv hρ j
  have hdψ : ∀ j, Torus.IsCk 1 (Torus.partialDeriv j ψ) := fun j => mova_isCk_partialDeriv hψ j
  have hFj : ∀ j, Torus.IsCk 1 (mova_F D ρ j) := fun j => by
    rw [mova_F_eq D hρ1]; exact mova_isCk_one_convFun hgi (hdρ j)
  have cρ := hρc
  have cdρ : ∀ j, Continuous (Torus.partialDeriv j ρ) := fun j => mova_continuous_partialDeriv hρ1 j
  have cdψ : ∀ j, Continuous (Torus.partialDeriv j ψ) := fun j => mova_continuous_partialDeriv hψ1 j
  have cddψ : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j ψ)) := fun j =>
    mova_continuous_partialDeriv (hdψ j) j
  have cdV : ∀ j, Continuous (Torus.partialDeriv j D.V) := fun j => mova_continuous_partialDeriv hV1 j
  have cF : ∀ j, Continuous (mova_F D ρ j) := fun j => mova_continuous_of_isCk (hFj j)
  have cfj : ∀ j, Continuous (mova_fj D ρ j) := fun j => mova_continuous_of_isCk (mova_fj_isCk D hρ hV j)
  unfold pair
  rw [PDE.MFPairing.integral_withDensityReal hdens.measurable hdens.nonneg,
    PDE.MFPairing.interactionPairing_eq_of_isCk hd D ρ hρ1 hdens.nonneg ψ hψ]
  have e1 : ∀ x, ρ x * (D.invβ * Torus.laplacian ψ x - inner ℝ (Torus.grad D.V x) (Torus.grad ψ x)) =
      ∑ j, (D.invβ * (ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) -
        ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x)) := by
    intro x
    rw [mova_laplacian_eq_sum hψ, mova_inner_eq_sum, mul_sub, Finset.sum_sub_distrib]
    have h1 : ρ x * (D.invβ * ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ψ) x) =
        ∑ j, D.invβ * (ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : ρ x * ∑ j, (Torus.grad D.V x).ofLp j * (Torus.grad ψ x).ofLp j =
        ∑ j, ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [mova_grad_apply, mova_grad_apply]
    rw [h1, h2]
  have e2 : ∀ x, ρ x * inner ℝ (Torus.grad ψ x) (Torus.matVec D.M
      (convGradConv (periodicRieszGrad d D.s) ρ x)) =
      ∑ j, (-(ρ x * (mova_F D ρ j x * Torus.partialDeriv j ψ x))) := by
    intro x
    rw [hM, mova_matVec_neg_one, inner_neg_right, mova_inner_eq_sum, mul_neg, Finset.mul_sum,
      Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [mova_grad_apply, mova_F]; ring
  simp_rw [e1, e2]
  rw [mova_integral_sum_cont Finset.univ (fun j x => D.invβ * (ρ x *
        Torus.partialDeriv j (Torus.partialDeriv j ψ) x) - ρ x * (Torus.partialDeriv j D.V x *
        Torus.partialDeriv j ψ x))
      (fun j => (continuous_const.mul (cρ.mul (cddψ j))).sub (cρ.mul ((cdV j).mul (cdψ j)))),
    mova_integral_sum_cont Finset.univ (fun j x => -(ρ x * (mova_F D ρ j x * Torus.partialDeriv j ψ x)))
      (fun j => (cρ.mul ((cF j).mul (cdψ j))).neg), ← Finset.sum_add_distrib]
  simp_rw [mova_pdeRHS_eq, Finset.mul_sum]
  rw [mova_integral_sum_cont Finset.univ (fun j x => ψ x * Torus.partialDeriv j (mova_fj D ρ j) x)
    (fun j => (mova_continuous_of_isCk hψ).mul (mova_continuous_partialDeriv (mova_fj_isCk D hρ hV j) j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have c1 : Continuous fun x => D.invβ * (ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) :=
    continuous_const.mul (cρ.mul (cddψ j))
  have c2 : Continuous fun x => ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x) :=
    cρ.mul ((cdV j).mul (cdψ j))
  have c3 : Continuous fun x => ρ x * (mova_F D ρ j x * Torus.partialDeriv j ψ x) :=
    cρ.mul ((cF j).mul (cdψ j))
  have c4 : Continuous fun x => Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x :=
    (cdρ j).mul (cdψ j)
  have i12 : Integrable (fun x => D.invβ * (ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x) -
      ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x)) := mova_int_cont (c1.sub c2)
  rw [integral_sub (mova_int_cont c1) (mova_int_cont c2), integral_neg, integral_const_mul]
  have ibp1 := mova_integral_ibp j hρ1 (hdψ j)
  have ibp2 := mova_integral_ibp j (mova_fj_isCk D hρ hV j) hψ1
  have e3 : ∫ x, ψ x * Torus.partialDeriv j (mova_fj D ρ j) x =
      ∫ x, Torus.partialDeriv j (mova_fj D ρ j) x * ψ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have c5 : Continuous fun x => D.invβ * (Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x) :=
    continuous_const.mul c4
  have e4 : ∫ x, mova_fj D ρ j x * Torus.partialDeriv j ψ x =
      D.invβ * (∫ x, Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x) +
        (∫ x, ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x)) +
          (∫ x, ρ x * (mova_F D ρ j x * Torus.partialDeriv j ψ x)) := by
    have : (fun x => mova_fj D ρ j x * Torus.partialDeriv j ψ x) = fun x =>
        (D.invβ * (Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x) +
          ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x)) +
          ρ x * (mova_F D ρ j x * Torus.partialDeriv j ψ x) := by
      funext x; simp only [mova_fj]; ring
    have i45 : Integrable (fun x => D.invβ * (Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x) +
        ρ x * (Torus.partialDeriv j D.V x * Torus.partialDeriv j ψ x)) := mova_int_cont (c5.add c2)
    rw [this, integral_add i45 (mova_int_cont c3),
      integral_add (mova_int_cont c5) (mova_int_cont c2), integral_const_mul]
  rw [e3, ibp2, e4]
  have ibp1' : ∫ x, ρ x * Torus.partialDeriv j (Torus.partialDeriv j ψ) x =
      -∫ x, Torus.partialDeriv j ρ x * Torus.partialDeriv j ψ x := by linarith
  rw [ibp1']
  ring

end HRS
