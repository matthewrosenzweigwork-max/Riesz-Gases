import HRS.MS.R26T8AP11a3
import HRS.MS.R26T8AP19

/-!
# S8.2 T8A packet P11 (helper a4): the divergence source of a conormal `Q` against a smooth density is conormal
`r26t8a_divSource_conormal`: `Q` is `Conormal (K+2) b M σ' A`, `ρ` is `C^{K+1}` with jets of order `≤ K+1` bounded by `Cρ`;
then `divSource ρ Q = ρ Σ ∂²_{x_i} Q + Σ ∂_iρ ∂_{x_i} Q` is `Conormal K b M (σ'+2)` (constant below).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_divSource_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (K b : ℕ) {M σ' A Cρ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ Cρ) {Q : Euc d → Euc d → ℝ} (hQ : Conormal (K + 2) b M σ' A Q)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) ρ)
    (hj : ∀ j ≤ K + 1, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ Cρ) :
    Conormal K b M (σ' + 2)
      ((d : ℝ) * (2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * (2 * (2 * A)))) +
        (d : ℝ) * (2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * (2 * A))))
      (r26t8a_divSource ρ Q) := by
  have hdx1 : ∀ i : Fin d, Conormal (K + 1) b M (σ' + 1) (2 * A) (r26t8a_dx i Q) := fun i =>
    r26t8a_f8_dx_conormal (k := K + 1) hchi hA hQ i
  have hdx2 : ∀ i : Fin d, Conormal K b M (σ' + 1 + 1) (2 * (2 * A)) (r26t8a_dx i (r26t8a_dx i Q)) := fun i =>
    r26t8a_f8_dx_conormal (k := K) hchi (by positivity) (hdx1 i) i
  have hdx1' : ∀ i : Fin d, Conormal K b M (σ' + 1) (2 * A) (r26t8a_dx i Q) := fun i =>
    r26t8a_conormal_mono (Nat.le_succ K) (hdx1 i)
  have hρK : ContDiff ℝ (K : WithTop ℕ∞) ρ := hρ.of_le (by exact_mod_cast Nat.le_succ K)
  have hjK : ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j ρ x‖ ≤ Cρ := fun j hj' x => hj j (by omega) x
  -- the derivatives of rho
  have hdρ : ∀ i : Fin d, ContDiff ℝ (K : WithTop ℕ∞) (fun x => fderiv ℝ ρ x (EuclideanSpace.single i 1)) := fun i =>
    (hρ.fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const
  have hjdρ : ∀ i : Fin d, ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ ρ x (EuclideanSpace.single i 1)) x‖ ≤ Cρ := by
    intro i j hjK' x
    have hfd : ContDiff ℝ (K : WithTop ℕ∞) (fderiv ℝ ρ) := hρ.fderiv_right (by push_cast; exact le_rfl)
    have h1 := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).norm_iteratedFDeriv_comp_left
      (hfd.contDiffAt (x := x)) (n := j) (by exact_mod_cast hjK')
    have e : (fun x => fderiv ℝ ρ x (EuclideanSpace.single i 1)) =
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)) ∘ fderiv ℝ ρ := rfl
    rw [e]
    refine h1.trans ?_
    have hap : ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
      simp only [ContinuousLinearMap.apply_apply, one_mul]
      calc ‖f (EuclideanSpace.single i 1)‖ ≤ ‖f‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ := f.le_opNorm _
        _ = ‖f‖ := by simp
    rw [norm_iteratedFDeriv_fderiv]
    have := hj (j + 1) (by omega) x
    calc ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ * ‖iteratedFDeriv ℝ (j + 1) ρ x‖
        ≤ 1 * Cρ := mul_le_mul hap this (norm_nonneg _) zero_le_one
      _ = Cρ := one_mul _
  have hc1 : 0 ≤ 2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * (2 * (2 * A))) := by positivity
  have hc2 : 0 ≤ 2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * (2 * A)) := by positivity
  have hT1 : ∀ i : Fin d, Conormal K b M (σ' + 1 + 1) (2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * (2 * (2 * A))))
      (fun x y => ρ x * r26t8a_dx i (r26t8a_dx i Q) x y) := fun i =>
    r26t8a_conormal_mul_x hchi (by positivity) hC hρK hjK (hdx2 i)
  have hT2 : ∀ i : Fin d, Conormal K b M (σ' + 1 + 1) (2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * (2 * A)))
      (fun x y => fderiv ℝ ρ x (EuclideanSpace.single i 1) * r26t8a_dx i Q x y) := fun i =>
    r26t8a_conormal_mono_sA hc2 le_rfl (by linarith)
      (r26t8a_conormal_mul_x hchi (by positivity) hC (hdρ i) (hjdρ i) (hdx1' i))
  have S1 := r26t8a_conormal_sum hchi (Finset.univ : Finset (Fin d)) (fun i _ => hT1 i)
  have S2 := r26t8a_conormal_sum hchi (Finset.univ : Finset (Fin d)) (fun i _ => hT2 i)
  have S3 := r26t8a_conormal_add hchi S1 S2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at S3
  have e : σ' + 1 + 1 = σ' + 2 := by ring
  rw [e] at S3
  refine r26t8a_conormal_congr (fun x y hxy => ?_) S3
  have hf : ContDiffAt ℝ 2 (fun v => Q v y) x := by
    have h1 : ContDiffAt ℝ ((K + 2 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) (x, y) :=
      hQ.1.contDiffAt ((isOpen_ne_fun (continuous_fst : Continuous fun p : Euc d × Euc d => p.1) continuous_snd).mem_nhds hxy)
    have h2 := h1.comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact (h2.of_le (by exact_mod_cast (by omega : 2 ≤ K + 2)))
  rw [r26t8a_f9_divSource_eq hf]
  unfold r26t8a_Stil
  rw [Finset.mul_sum]

end HRS.MS.R26T8A
