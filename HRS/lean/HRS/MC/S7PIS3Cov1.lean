import HRS.MC.S7PIDefs
import HRS.MC.S7FCF5A1
import HRS.MC.L2C3Aux5
import HRS.PDE.MeanFieldLinearLoss

/-!
# Packet piS3, part 2a: infrastructure for `s7_PIS_cov_struct`

Gram matrices of continuous vector fields in `L²(ρ)` are PSD, `propagator` is `C¹` on `[0, t]` (junk `0`
included), `∇ 0 = 0`, and the continuity of the energy integrand `v ↦ ∫ ∇U^{v,t_i}φ_i · ∇U^{v,t_j}φ_j ρ_v`
on `[0, t_i ∧ t_j]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIS3_grad_zero (x : Torus d) : Torus.grad (0 : Torus d → ℝ) x = 0 := by
  unfold Torus.grad
  have : Torus.lift (0 : Torus d → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [this]
  simp [gradient]

theorem S7PIS3_isCk_zero : Torus.IsCk 1 (0 : Torus d → ℝ) := by
  unfold Torus.IsCk
  have : Torus.lift (0 : Torus d → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [this]
  exact contDiff_const

/-- On `[0,t]` the adjoint propagator is `C¹` (it is `C²` for a classical solution, and `0` otherwise). -/
theorem S7PIS3_prop_isCk (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ) {v : ℝ}
    (hv0 : 0 ≤ v) (hvt : v ≤ t) : Torus.IsCk 1 (propagator D ρ v t φ) := by
  by_cases h : ∃ f, IsClassicalAdjointSolution D ρ t φ f
  · unfold propagator
    rw [dif_pos h]
    exact HRS.PDE.ClassicalAux.isCk_of_le (by norm_num) (h.choose_spec.c2 v ⟨hv0, hvt⟩)
  · unfold propagator
    rw [dif_neg h]
    exact S7PIS3_isCk_zero

theorem S7PIS3_integrable_of_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The Gram matrix of continuous vector fields in `L²(ρ)` (times a nonnegative constant) is PSD. -/
theorem S7PIS3_gram_psd {q : ℕ} (w : ℝ) (hw : 0 ≤ w) (a : Fin q → Torus d → Euc d)
    (ha : ∀ i, Continuous (a i)) (ρ : Torus d → ℝ) (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) :
    (Matrix.of fun i j => w * ∫ x, inner ℝ (a i x) (a j x) * ρ x).PosSemidef := by
  have hint : ∀ i j, Integrable (fun x => inner ℝ (a i x) (a j x) * ρ x) := fun i j =>
    S7PIS3_integrable_of_cont (((ha i).inner (ha j)).mul hρ)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    simp_rw [real_inner_comm (a i _)]
  · intro x
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply]
    have hsum : ∑ i, x i * ∑ j, w * (∫ y, inner ℝ (a i y) (a j y) * ρ y) * x j =
        w * ∫ y, ‖∑ i, x i • a i y‖ ^ 2 * ρ y := by
      have e1 : ∀ y, ‖∑ i, x i • a i y‖ ^ 2 * ρ y =
          ∑ i, ∑ j, x i * x j * (inner ℝ (a i y) (a j y) * ρ y) := by
        intro y
        rw [← real_inner_self_eq_norm_sq, sum_inner, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_sum]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inner_smul_left, inner_smul_right]
        simp only [conj_trivial]
        ring
      simp_rw [e1]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      ring
    rw [hsum]
    exact mul_nonneg hw (integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hρ0 y))

/-- Continuity of the energy integrand on `[0, t_i ∧ t_j]`. -/
theorem S7PIS3_g_cont (R : Regime d) {ti tj : ℝ} (hti : 0 ≤ ti) (htj : 0 ≤ tj) {φi φj : Torus d → ℝ}
    (hφi : Torus.IsSmooth φi) (hφj : Torus.IsSmooth φj) :
    ContinuousOn (fun v => ∫ x, inner ℝ (Torus.grad (propagator R.D R.ρ v ti φi) x)
      (Torus.grad (propagator R.D R.ρ v tj φj) x) * R.ρ v x) (Set.Icc 0 (min ti tj)) := by
  rcases (le_min hti htj).eq_or_lt with h0 | hpos
  · rw [← h0, Set.Icc_self]
    exact continuousOn_singleton _ _
  · have hi : 0 < ti := lt_of_lt_of_le hpos (min_le_left _ _)
    have hj : 0 < tj := lt_of_lt_of_le hpos (min_le_right _ _)
    obtain ⟨Fi, hFi, hpi⟩ := HRS.MC.L2C3.l2c3_classical R hi hφi
    obtain ⟨Fj, hFj, hpj⟩ := HRS.MC.L2C3.l2c3_classical R hj hφj
    have hμ : ContinuousOn (fun p : ℝ × Torus d => R.ρ p.1 p.2)
        (Set.Icc 0 (min ti tj) ×ˢ Set.univ) :=
      (HRS.MC.Sec7.S7FCF5A.fcf5_A1_rho_cont_proof R).mono
        (Set.prod_mono (fun v hv => Set.mem_Ici.2 hv.1) le_rfl)
    refine (HRS.PDE.MFLinear.continuous_energy_integrand hFi hFj (min_le_left _ _) (min_le_right _ _)
      hμ).congr fun r hr => ?_
    simp only
    rw [hpi r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩, hpj r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩]

end HRS.MC.Sec7.S7PIS3

end
