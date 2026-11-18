import HRS.MS.S21E_Kappa
import HRS.MC.E213U18a

/-!
# S2.1(iii) packet G10: `κ` evaluated on a product of three linear functionals (generic Banach space)

`s21e_kappa_trilin`: `κ(ℓ₀ ⊗ ℓ₁ ⊗ ℓ₂) = κ₀(ℓ₀⊗ℓ₁⊗ℓ₂) - ½ Σ₆ E[ℓ_i(D) ℓ_j(Z) ℓ_k(Z)] + ½ Σ₆ E[ℓ_k(Z) J(ℓ_i ⊗ ℓ_j)]` (sums over the six orderings), and in the
cyclic form `κ = κ₀ - Σ_cyc E[ℓ_i(D) ℓ_{i+1}(Z) ℓ_{i+2}(Z)] + Σ_cyc E[ℓ_{i+2}(Z) J(ℓ_i ⊗ ℓ_{i+1})]` when `J` is symmetric.  This reduces the formula clause of the frozen
conclusion to three explicit identities: the initial term (W0) and the two Wick contractions (W1: drift term, W2: noise term), the content of the open packet H2.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace HRS.MS.S21E

open HRS HRS.Contr HRS.MC.E213T HRS.MC.E213U18

section Generic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The sum of a triple function over the six orderings. -/
def s21eSum6 (G : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  G 0 1 2 + G 0 2 1 + G 1 0 2 + G 1 2 0 + G 2 0 1 + G 2 1 0

theorem s21e_kappa_trilin (κ₀ : TensorDual B 3)
    (hκsym : ∀ (σ : Equiv.Perm (Fin 3)) (M : B [×3]→L[ℝ] ℝ), κ₀ (M.domDomCongr σ) = κ₀ M)
    {D Z : Ω → B} {J : Ω → TensorDual B 2}
    (hDm : AEStronglyMeasurable D P) (hZm : AEStronglyMeasurable Z P) (hJm : AEStronglyMeasurable J P)
    (hi3 : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P) (hi21 : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P)
    (ℓ : Fin 3 → B →L[ℝ] ℝ) :
    s21eKappa P κ₀ D Z J (trilin ℓ) =
      κ₀ (trilin ℓ) - (1 / 2) * s21eSum6 (fun i j k => ∫ ω, ℓ i (D ω) * ℓ j (Z ω) * ℓ k (Z ω) ∂P)
        + (1 / 2) * s21eSum6 (fun i j k => ∫ ω, ℓ k (Z ω) * J ω (mk2 (ℓ i) (ℓ j)) ∂P) := by
  have hbD : ∀ ℓ' : Fin 3 → B →L[ℝ] ℝ,
      bochTensor3 P D Z Z (trilin ℓ') = ∫ ω, ℓ' 0 (D ω) * ℓ' 1 (Z ω) * ℓ' 2 (Z ω) ∂P := by
    intro ℓ'
    rw [bochTensor3_apply hDm hZm hZm hi3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [trilin_apply]
  have hbJ : ∀ ℓ' : Fin 3 → B →L[ℝ] ℝ,
      bochTensor21 P J Z (trilin ℓ') = ∫ ω, ℓ' 2 (Z ω) * J ω (mk2 (ℓ' 0) (ℓ' 1)) ∂P := by
    intro ℓ'
    rw [bochTensor21_apply hJm hZm hi21]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (J ω) (HRS.lastSlot (trilin ℓ') (Z ω)) = _
    rw [lastSlot_trilin, map_smul, smul_eq_mul]
  unfold s21eKappa
  rw [symm3_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin 3),
      (κ₀ - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z) ((trilin ℓ).domDomCongr σ) =
      κ₀ (trilin ℓ) - 3 * bochTensor3 P D Z Z ((trilin ℓ).domDomCongr σ)
        + 3 * bochTensor21 P J Z ((trilin ℓ).domDomCongr σ) := by
    intro σ
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hκsym]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_perm_trilin, sum_perm_trilin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h6 : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    have : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm]; simp [Nat.factorial]
    exact_mod_cast this
  rw [h6]
  simp only [hbD, hbJ, s21eSum6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Cyclic form (for a symmetric `J`): `κ(ℓ₀⊗ℓ₁⊗ℓ₂) = κ₀ - Σ_cyc E[ℓ_i(D) ℓ_{i+1}(Z) ℓ_{i+2}(Z)] + Σ_cyc E[ℓ_{i+2}(Z) J(ℓ_i ⊗ ℓ_{i+1})]`. -/
theorem s21e_kappa_trilin_cyc (κ₀ : TensorDual B 3)
    (hκsym : ∀ (σ : Equiv.Perm (Fin 3)) (M : B [×3]→L[ℝ] ℝ), κ₀ (M.domDomCongr σ) = κ₀ M)
    {D Z : Ω → B} {J : Ω → TensorDual B 2}
    (hDm : AEStronglyMeasurable D P) (hZm : AEStronglyMeasurable Z P) (hJm : AEStronglyMeasurable J P)
    (hi3 : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P) (hi21 : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P)
    (hJsym : ∀ᵐ ω ∂P, ∀ a b : B →L[ℝ] ℝ, J ω (mk2 a b) = J ω (mk2 b a))
    (ℓ : Fin 3 → B →L[ℝ] ℝ) :
    s21eKappa P κ₀ D Z J (trilin ℓ) =
      κ₀ (trilin ℓ) - ∑ i : Fin 3, (∫ ω, ℓ i (D ω) * ℓ (i + 1) (Z ω) * ℓ (i + 2) (Z ω) ∂P)
        + ∑ i : Fin 3, ∫ ω, ℓ (i + 2) (Z ω) * J ω (mk2 (ℓ i) (ℓ (i + 1))) ∂P := by
  rw [s21e_kappa_trilin P κ₀ hκsym hDm hZm hJm hi3 hi21 ℓ]
  have hDsym : ∀ i j k : Fin 3, (∫ ω, ℓ i (D ω) * ℓ j (Z ω) * ℓ k (Z ω) ∂P) =
      ∫ ω, ℓ i (D ω) * ℓ k (Z ω) * ℓ j (Z ω) ∂P := fun i j k => by
    congr 1; funext ω; ring
  have hJs : ∀ i j k : Fin 3, (∫ ω, ℓ k (Z ω) * J ω (mk2 (ℓ i) (ℓ j)) ∂P) =
      ∫ ω, ℓ k (Z ω) * J ω (mk2 (ℓ j) (ℓ i)) ∂P := fun i j k => by
    refine integral_congr_ae ?_
    filter_upwards [hJsym] with ω hω
    rw [hω (ℓ i) (ℓ j)]
  simp only [s21eSum6, Fin.sum_univ_three]
  rw [hDsym 0 2 1, hDsym 1 0 2, hDsym 2 1 0, hJs 0 2 1, hJs 1 0 2, hJs 2 1 0]
  have e1 : ((0 : Fin 3) + 1 = 1) := rfl
  have e2 : ((0 : Fin 3) + 2 = 2) := rfl
  have e3 : ((1 : Fin 3) + 1 = 2) := rfl
  have e4 : ((1 : Fin 3) + 2 = 0) := rfl
  have e5 : ((2 : Fin 3) + 1 = 0) := rfl
  have e6 : ((2 : Fin 3) + 2 = 1) := rfl
  simp only [e1, e2, e3, e4, e5, e6]
  ring

end Generic

end HRS.MS.S21E
