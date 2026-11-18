import HRS.MS.WsStatAux19

/-!
# S21 packet F3f: helper lemmas for the centred coordinate identity

* `s21_pair_emp_meas`, `s21_pair_emp_bdd`, `s21_pair_emp_integrable`: `zeta |-> pair (empirical (Y zeta)) f` for bounded measurable `f`.
* `s21_fluc_eq_neg_half_comm`: for `M = -1`, `flucInteractionRd D psi X rho = -(1/2) centeredPairFunctional (commutatorKernel ..)`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s21_pair_emp_meas {N : ℕ} (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → EucConfig d N)
    (hY : Measurable Y) {f : Euc d → ℝ} (hf : Measurable f) :
    Measurable fun ζ => HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) f := by
  have e : (fun ζ => HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) f) = fun ζ => (N : ℝ)⁻¹ * ∑ i, f (Y ζ i) :=
    funext fun ζ => HRS.Whole.pair_empirical hN _ _
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hf.comp ((measurable_pi_apply i).comp hY))

theorem s21_pair_emp_bdd {N : ℕ} (hN : 0 < N) (x : EucConfig d N) {f : Euc d → ℝ} {B : ℝ}
    (hB : ∀ z, |f z| ≤ B) : |HRS.Whole.pair (HRS.Whole.empirical x) f| ≤ B := by
  rw [HRS.Whole.pair_empirical hN, abs_mul, abs_of_nonneg (by positivity)]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc (N : ℝ)⁻¹ * |∑ i, f (x i)| ≤ (N : ℝ)⁻¹ * ∑ i, |f (x i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hB _) (by positivity)
    _ = B := by simp [Finset.sum_const]; field_simp

theorem s21_pair_emp_integrable {N : ℕ} (hN : 0 < N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Y : Ω → EucConfig d N) (hY : Measurable Y) {f : Euc d → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    Integrable (fun ζ => HRS.Whole.pair (HRS.Whole.empirical (Y ζ)) f) P :=
  Integrable.of_bound (s21_pair_emp_meas hN Y hY hf).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs]; exact s21_pair_emp_bdd hN (Y ζ) hB)

theorem s21_commK_neg (s : ℝ) (v : Euc d → Euc d) (x y : Euc d) :
    commutatorKernel d s (fun z => -v z) x y = -1 * commutatorKernel d s v x y := by
  unfold commutatorKernel
  rw [show -v x - -v y = -(v x - v y) by abel, inner_neg_left]
  ring

theorem s21_fluc_eq_neg_half_comm (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (hM : D.M = -1)
    {N : ℕ} {ρ : Euc d → ℝ} (hρ : RegSliceRd ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (X : EucConfig d N) :
    HRS.Whole.AppendixA.flucInteractionRd D ψ X ρ = -(1 / 2 : ℝ) * centeredPairFunctional
      (commutatorKernel d D.s (fun x => gradient ψ x)) X (HRS.Whole.withDensityReal ρ) := by
  rw [HRS.MS.GenPath.s56_fluc_eq_comm D hd hs0 hsd hρ hψ X]
  have e : (fun x => Torus.matVec D.M.transpose (gradient ψ x)) = fun x => -gradient ψ x := by
    funext x
    rw [hM]
    simp [Torus.matVec]
  rw [e]
  have e2 : commutatorKernel d D.s (fun x => -gradient ψ x) =
      fun x y => -1 * commutatorKernel d D.s (fun x => gradient ψ x) x y :=
    funext fun x => funext fun y => s21_commK_neg D.s _ x y
  rw [e2, HRS.MS.S53.s53_cPF_const_mul]
  ring

end HRS.MS.S21
