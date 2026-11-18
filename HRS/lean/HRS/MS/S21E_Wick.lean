import HRS.MS.S21E_Trilin
import HRS.MS.S21E_Fin
import HRS.MS.GenPathAux10

/-!
# S2.1(iii) packet G11: the formula clause from the three explicit identities (initial term, drift Wick contraction, noise Wick contraction)

* `s21eEvalCLM`, `s21eObs`: the observation `w ↦ w(τ)(φ)` (`φ ∈ Σ^m`) as a continuous linear functional on `OscPath`; `M = trilin ℓ` for every `M` of the frozen clause.
* `s21e_formulaFor_of_wick`: for the tensor `κ = Sym(κ₀ - 3E[D⊗Z⊗Z] + 3E[J⊗Z])` the frozen identity `κ[M] = cubicFormula` follows from
  (W0) `κ₀(ℓ₀⊗ℓ₁⊗ℓ₂) = ∫ r₀r₁r₂ dμ₀`,
  (W1) `E[ℓ_i(D) ℓ_{i+1}(Z) ℓ_{i+2}(Z)] = ∫_0^{t_i} ∬ h_{∇f_i^r} χ_{i+1}^r χ_{i+2}^r`,
  (W2) `E[ℓ_{i+2}(Z) J(ℓ_i ⊗ ℓ_{i+1})] = (2/β) ∫_0^{t_i∧t_{i+1}} ∫ ∇f_i^r·∇f_{i+1}^r χ_{i+2}^r`,
  (the open packet H2) together with symmetry of `κ₀` and `J` and the integrability clause.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option maxSynthPendingDepth 3

namespace HRS.Whole

variable {d : ℕ}

/-- The pairing with an oscillator test function as a continuous linear functional on `B_m`. -/
def s21eEvalCLM (m : ℝ) {φ : Euc d → ℝ} (hφ : MemOsc m φ) : OscDual d m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (OscSpace.ofFun m φ)).comp
    (OscDual.toDual (d := d) (m := m)).toContinuousLinearEquiv.toContinuousLinearMap

theorem s21eEvalCLM_apply (m : ℝ) {φ : Euc d → ℝ} (hφ : MemOsc m φ) (u : OscDual d m) :
    s21eEvalCLM m hφ u = OscDual.eval u φ := by
  unfold s21eEvalCLM
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe]
  exact OscDual.toDual_ofFun u φ hφ

/-- The observation `w ↦ w(t)(φ)` on the path space. -/
def s21eObs (m T : ℝ) {φ : Euc d → ℝ} (hφ : MemOsc m φ) (t : Set.Icc (0 : ℝ) T) :
    OscPath d m T →L[ℝ] ℝ :=
  (s21eEvalCLM m hφ).comp (ContinuousMap.evalCLM ℝ t)

theorem s21eObs_apply (m T : ℝ) {φ : Euc d → ℝ} (hφ : MemOsc m φ) (t : Set.Icc (0 : ℝ) T) (w : OscPath d m T) :
    s21eObs m T hφ t w = OscDual.eval (OscPath.at' w t) φ := by
  unfold s21eObs
  exact s21eEvalCLM_apply m hφ (OscPath.at' w t)

/-- Every `M` of the frozen formula clause is the product form `trilin ℓ` of the three observations. -/
theorem s21e_M_eq_trilin (m T : ℝ) {φ : Fin 3 → Euc d → ℝ} (hφ : ∀ i, MemOsc m (φ i))
    (τ : Fin 3 → Set.Icc (0 : ℝ) T) (M : (OscPath d m T) [×3]→L[ℝ] ℝ)
    (hM : ∀ w : Fin 3 → OscPath d m T, M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) :
    M = HRS.MC.E213U18.trilin (fun i => s21eObs m T (hφ i) (τ i)) := by
  ext w
  rw [hM w, HRS.MC.E213U18.trilin_apply, Fin.prod_univ_three, s21eObs_apply, s21eObs_apply, s21eObs_apply]

/-- **G11.**  The formula clause from the initial term (W0), the drift contraction (W1), the noise contraction (W2) and the integrability clause. -/
theorem s21e_formulaFor_of_wick {s a β β₀ T a₀ : ℝ} {ρ : ℝ → Euc d → ℝ}
    (κ : projTensor (OscPath d (wholeSpaceIndex d) T) 3)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
    (hκ₀sym : ∀ (σ : Equiv.Perm (Fin 3)) (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
      κ₀ (M.domDomCongr σ) = κ₀ M)
    (D Z : Ω → OscPath d (wholeSpaceIndex d) T)
    (J : Ω → TensorDual (OscPath d (wholeSpaceIndex d) T) 2)
    (hDm : AEStronglyMeasurable D P) (hZm : AEStronglyMeasurable Z P) (hJm : AEStronglyMeasurable J P)
    (hi3 : Integrable (fun ω => ‖D ω‖ * ‖Z ω‖ * ‖Z ω‖) P) (hi21 : Integrable (fun ω => ‖J ω‖ * ‖Z ω‖) P)
    (hJsym : ∀ᵐ ω ∂P, ∀ x y : OscPath d (wholeSpaceIndex d) T →L[ℝ] ℝ,
      J ω (HRS.MC.E213U18.mk2 x y) = J ω (HRS.MC.E213U18.mk2 y x))
    (hκ : (κ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) = HRS.MS.S21E.s21eKappa P κ₀ D Z J)
    (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ) (hφ : ∀ i, IsOscTest (wholeSpaceIndex d) (φ i))
    (χ : Fin 3 → ℝ → Euc d → ℝ)
    (hint : CubicFormulaIntegrable (quadraticGradientDyn d s a β) ρ β₀ (withDensityReal (ρ 0))
      (fun i => a₀ + τ i) φ χ)
    (hW0 : κ₀ (HRS.MC.E213U18.trilin (fun i => s21eObs (wholeSpaceIndex d : ℝ) T (hφ i).2 (τ i))) =
      ∫ x, responseInverse (rieszKernel d s) (withDensityReal (ρ 0)) β₀
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (a₀ + τ 0) (φ 0)) x *
          responseInverse (rieszKernel d s) (withDensityReal (ρ 0)) β₀
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (a₀ + τ 1) (φ 1)) x *
          responseInverse (rieszKernel d s) (withDensityReal (ρ 0)) β₀
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (a₀ + τ 2) (φ 2)) x ∂(withDensityReal (ρ 0)))
    (hW1 : ∀ i : Fin 3,
      (∫ ω, s21eObs (wholeSpaceIndex d : ℝ) T (hφ i).2 (τ i) (D ω) *
          s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 1)).2 (τ (i + 1)) (Z ω) *
          s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 2)).2 (τ (i + 2)) (Z ω) ∂P) =
        ∫ r in Set.Icc (0 : ℝ) (a₀ + τ i), ∫ x, ∫ y,
          commutatorKernel d s (fun z => gradient (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r
            (a₀ + τ i) (φ i)) z) x y * χ (i + 1) r x * χ (i + 2) r y)
    (hW2 : ∀ i : Fin 3,
      (∫ ω, s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 2)).2 (τ (i + 2)) (Z ω) *
          J ω (HRS.MC.E213U18.mk2 (s21eObs (wholeSpaceIndex d : ℝ) T (hφ i).2 (τ i))
            (s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 1)).2 (τ (i + 1)))) ∂P) =
        (2 / β) * ∫ r in Set.Icc (0 : ℝ) (min (a₀ + τ i) (a₀ + τ (i + 1))), ∫ x,
          inner ℝ (gradient (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (a₀ + τ i) (φ i)) x)
            (gradient (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (a₀ + τ (i + 1)) (φ (i + 1))) x) *
            χ (i + 2) r x) :
    S21eFormulaFor d s a β β₀ ρ T a₀ κ τ φ χ := by
  intro M hM
  refine ⟨?_, hint⟩
  have hMeq := s21e_M_eq_trilin (wholeSpaceIndex d : ℝ) T (fun i => (hφ i).2) τ M hM
  rw [hMeq, hκ, HRS.MS.S21E.s21e_kappa_trilin_cyc P κ₀ hκ₀sym hDm hZm hJm hi3 hi21 hJsym, hW0]
  simp only [hW1, hW2, ← Finset.mul_sum]
  unfold cubicFormula
  have hs : (quadraticGradientDyn d s a β).s = s := rfl
  simp only [hs]

end HRS.Whole
