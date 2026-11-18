import HRS.MC.E213U15a
import HRS.MC.E213TSymm
import HRS.Equilibrium.Parametrix.PX1AuxDeriv

/-!
# S2.1(iii) packet G4: the symmetric projective cubic tensor `κ_b` (generic Banach space)

`κ = Sym(κ₀ - 3 E[D ⊗ Z ⊗ Z] + 3 E[J ⊗ Z])` (paper eq:kappa, in the symmetrized-sum form of the torus Thm 2.13) as an element of `projTensor B 3`,
its symmetry, its norm bound `‖κ‖ ≤ ‖κ₀‖ + 3 E‖D‖‖Z‖² + 3 E‖J‖‖Z‖`, and the pairing identity
`(1/6) E κ(D³Φ(Z)) = (1/6) E κ₀(D³Φ(Z)) - E DΦ(Z)[D] + (1/2) E D²Φ(Z)[J]`
(from the generic Gaussian contractions), which turns the interpolation limit `-E DΦ[D] + ½ E D²Φ[J]` into the cubic term.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace HRS.MS.S21E

open HRS HRS.Contr HRS.MC.E213T HRS.MC.E213U15

section Generic

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The tensor `κ = Sym(κ₀ - 3 E[D ⊗ Z ⊗ Z] + 3 E[J ⊗ Z])`. -/
def s21eKappa (κ₀ : TensorDual B 3) (D Z : Ω → B) (J : Ω → TensorDual B 2) : TensorDual B 3 :=
  symm3 B (κ₀ - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z)

theorem s21e_kappa_mem {κ₀ : TensorDual B 3} (hκ₀ : κ₀ ∈ projTensor B 3) {D Z : Ω → B} {J : Ω → TensorDual B 2}
    (hDm : AEStronglyMeasurable D P) (hZm : AEStronglyMeasurable Z P) (hJm : AEStronglyMeasurable J P)
    (hi3 : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P) (hi21 : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P)
    (hJmem : ∀ᵐ ω ∂P, J ω ∈ projTensor B 2) :
    s21eKappa P κ₀ D Z J ∈ projTensor B 3 := by
  unfold s21eKappa
  have h2 : (-3 : ℝ) • bochTensor3 P D Z Z ∈ projTensor B 3 :=
    (projTensor B 3).smul_mem _ (bochTensor3_mem hDm hZm hZm hi3)
  have h3 : (3 : ℝ) • bochTensor21 P J Z ∈ projTensor B 3 :=
    (projTensor B 3).smul_mem _ (bochTensor21_mem hJm hZm hi21 hJmem)
  have h123 := (projTensor B 3).add_mem ((projTensor B 3).add_mem hκ₀ h2) h3
  have heq : κ₀ - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z =
      κ₀ + (-3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z := by
    ext M
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [heq]
  exact symm3_mem h123

theorem s21e_kappa_symm (κ₀ : TensorDual B 3) (D Z : Ω → B) (J : Ω → TensorDual B 2) (M : B [×3]→L[ℝ] ℝ)
    (σ : Equiv.Perm (Fin 3)) :
    s21eKappa P κ₀ D Z J (M.domDomCongr σ) = s21eKappa P κ₀ D Z J M :=
  symm3_symmetric _ M σ

theorem s21e_kappa_norm_le {κ₀ : TensorDual B 3} {D Z : Ω → B} {J : Ω → TensorDual B 2}
    (hDm : AEStronglyMeasurable D P) (hZm : AEStronglyMeasurable Z P) (hJm : AEStronglyMeasurable J P)
    (hi3 : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P) (hi21 : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P) :
    ‖s21eKappa P κ₀ D Z J‖ ≤
      ‖κ₀‖ + 3 * (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) + 3 * (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P) := by
  unfold s21eKappa
  refine ((symm3 B).le_opNorm _).trans ?_
  have hs : ‖symm3 B‖ ≤ 1 := norm_symm3_le B
  have hn : ‖κ₀ - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z‖ ≤
      ‖κ₀‖ + 3 * (∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P) + 3 * (∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P) := by
    have n2 : ‖bochTensor3 P D Z Z‖ ≤ ∫ ω, ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖ ∂P := norm_bochTensor3_le hDm hZm hZm hi3
    have n3 : ‖bochTensor21 P J Z‖ ≤ ∫ ω, ‖J ω‖ * ‖Z ω‖ ∂P := norm_bochTensor21_le hJm hZm hi21
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add_right ?_ _)) ?_)
    · refine (ContinuousLinearMap.opNorm_smul_le (3 : ℝ) _).trans ?_
      rw [Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left n2 (by norm_num)
    · refine (ContinuousLinearMap.opNorm_smul_le (3 : ℝ) _).trans ?_
      rw [Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left n3 (by norm_num)
  calc ‖symm3 B‖ * ‖κ₀ - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z‖
      ≤ 1 * ‖κ₀ - (3 : ℝ) • bochTensor3 P D Z Z + (3 : ℝ) • bochTensor21 P J Z‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hn

/-- `D³Φ(z)` is invariant under permutations of its arguments, so `Sym` is invisible against it. -/
theorem s21e_kappa_apply (κ₀ : TensorDual B 3) (D Z : Ω → B) (J : Ω → TensorDual B 2) {Φ : B → ℝ}
    (hΦ : MemCb 3 Φ) (z : B) :
    s21eKappa P κ₀ D Z J (iteratedFDeriv ℝ 3 Φ z) =
      κ₀ (iteratedFDeriv ℝ 3 Φ z) - 3 * bochTensor3 P D Z Z (iteratedFDeriv ℝ 3 Φ z)
        + 3 * bochTensor21 P J Z (iteratedFDeriv ℝ 3 Φ z) := by
  unfold s21eKappa
  rw [symm3_apply]
  have hsym : ∀ σ : Equiv.Perm (Fin 3),
      (iteratedFDeriv ℝ 3 Φ z).domDomCongr σ = iteratedFDeriv ℝ 3 Φ z := fun σ => by
    ext v
    exact HRS.Parx.iteratedFDeriv_perm hΦ.1.contDiffAt σ v
  simp only [hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h6 : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    have : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Fintype.card_perm]; simp [Nat.factorial]
    exact_mod_cast this
  rw [h6]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

theorem s21e_integrable_apply3 {Φ : B → ℝ} (hΦ : MemCb 3 Φ) {Z : Ω → B} (hZ : AEStronglyMeasurable Z P)
    (u : TensorDual B 3) : Integrable (fun ω => u (iteratedFDeriv ℝ 3 Φ (Z ω))) P := by
  have hc : Continuous (iteratedFDeriv ℝ 3 Φ) := hΦ.1.continuous_iteratedFDeriv (by norm_num)
  have hg : Continuous fun z => u (iteratedFDeriv ℝ 3 Φ z) := u.continuous.comp hc
  obtain ⟨C, hC⟩ := hΦ.2 3 le_rfl
  refine (integrable_const (‖u‖ * C)).mono' (hg.comp_aestronglyMeasurable hZ)
    (Filter.Eventually.of_forall fun ω => ?_)
  refine (u.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (hC ⟨Z ω, rfl⟩) (norm_nonneg _)

/-- **G4 (pairing identity).**  With the generic Gaussian contractions: `(1/6) E κ(D³Φ(Z)) = (1/6) E κ₀(D³Φ(Z)) - E DΦ(Z)[D] + (1/2) E D²Φ(Z)[J]`. -/
theorem s21e_pairing_identity (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ) (Z D : Ω → B)
    (J : Ω → projTensor B 2) (hZ : IsCenteredGaussian (law P Z)) (hZc : InFirstChaos P ξ 2 Z)
    (hDc : InSecondChaos P ξ 3 D) (hJc : InFirstChaos P ξ 2 J) (Φ : B → ℝ) (hΦ : MemCb 3 Φ)
    (hZa : AEStronglyMeasurable Z P) (hDa : AEStronglyMeasurable D P)
    (hJa : AEStronglyMeasurable (fun ω => (J ω : TensorDual B 2)) P)
    (hD1 : Integrable (fun ω => ‖D ω‖) P) (hDZZ : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P)
    (hJ1 : Integrable (fun ω => ‖(J ω : TensorDual B 2)‖) P)
    (hJZ : Integrable (fun ω => ‖(J ω : TensorDual B 2)‖ * ‖Z ω‖) P) (κ₀ : TensorDual B 3) :
    (1 / 6 : ℝ) * ∫ ω, s21eKappa P κ₀ D Z (fun ω => (J ω : TensorDual B 2)) (iteratedFDeriv ℝ 3 Φ (Z ω)) ∂P =
      (1 / 6 : ℝ) * ∫ ω, κ₀ (iteratedFDeriv ℝ 3 Φ (Z ω)) ∂P - ∫ ω, fderiv ℝ Φ (Z ω) (D ω) ∂P +
        (1 / 2 : ℝ) * ∫ ω, (J ω : TensorDual B 2) (iteratedFDeriv ℝ 2 Φ (Z ω)) ∂P := by
  have hd := u15_drift_generic P ξ hξ Z D hZ hZc hDc Φ hΦ hZa hDa hD1 hDZZ
  have hj := u15_J_generic P ξ hξ Z hZ hZc J 2 le_rfl hJc Φ hΦ hZa hJa hJ1 hJZ
  have i0 := s21e_integrable_apply3 P hΦ hZa κ₀
  have i1 := s21e_integrable_apply3 P hΦ hZa (bochTensor3 P D Z Z)
  have i2 := s21e_integrable_apply3 P hΦ hZa (bochTensor21 P (fun ω => (J ω : TensorDual B 2)) Z)
  simp_rw [s21e_kappa_apply P κ₀ D Z (fun ω => (J ω : TensorDual B 2)) hΦ]
  have h1 : Integrable (fun ω => κ₀ (iteratedFDeriv ℝ 3 Φ (Z ω)) -
      3 * bochTensor3 P D Z Z (iteratedFDeriv ℝ 3 Φ (Z ω))) P := i0.sub (i1.const_mul 3)
  have h2 : Integrable (fun ω => 3 * bochTensor21 P (fun ω => (J ω : TensorDual B 2)) Z
      (iteratedFDeriv ℝ 3 Φ (Z ω))) P := i2.const_mul 3
  have h3 : Integrable (fun ω => 3 * bochTensor3 P D Z Z (iteratedFDeriv ℝ 3 Φ (Z ω))) P := i1.const_mul 3
  rw [integral_add h1 h2, integral_sub i0 h3, integral_const_mul, integral_const_mul]
  rw [hd, hj]
  ring

end Generic

end HRS.MS.S21E
