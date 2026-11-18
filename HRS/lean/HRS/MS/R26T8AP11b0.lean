import HRS.MS.R26T8AP11g7

/-!
# S8.2 T8A packet P11 (helper b0): the `x`-averaged row of `oneJ` is `C^k`
Smoothness part of P11g (b), which `r26t8a_nonlocal_rows` states only as a jets bound: `z ↦ ∫ oneJ(Q(·,z)) dμ` is `C^k`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_p11_row_smooth (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Q : Euc d → Euc d → ℝ) (A : ℝ) (hA : 0 ≤ A) (hQ : Conormal (k + 2) b M (sigma - 2) A Q) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun z => ∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
          ∂(HRS.Whole.withDensityReal rho)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  obtain ⟨K, hK0, hw⟩ := r26t8a_g6_weight hd k M ha hbeta hrho
  have hσ1 : sigma - 1 < d := by linarith
  obtain ⟨Crow, hCrow0, hrow⟩ := r26t8a_row_lemma hd k b M (sigma - 1) hM hσ1 K hK0
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  -- the swapped pair functions `dx_i Q`
  have hdx : ∀ i : Fin d, Conormal k b M (sigma - 1) (2 * A) (fun z u => r26t8a_dx i Q u z) := by
    intro i
    have h1 := r26t8a_f8_dx_conormal hchi hA (k := k + 1) (hQ) i
    have h2 := r26t8a_conormal_mono (k := k) (k' := k + 1) (by omega) h1
    have e : sigma - 2 + 1 = sigma - 1 := by ring
    rw [e] at h2
    exact r26t8a_f24_conormal_swap hchi h2
  have hrowi := fun i : Fin d => hrow (fun u => rho u * forceMean rho u i) (hw i).1 (hw i).2
    (fun z u => r26t8a_dx i Q u z) (2 * A) (by positivity) (hdx i)
  -- identity for each `z`
  have hid : ∀ z : Euc d, ∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho) =
      -∑ i : Fin d, ∫ u, (rho u * forceMean rho u i) * r26t8a_dx i Q u z := by
    intro z
    rw [(r26t8a_g5_row d hd k b a beta M sigma ha hbeta hM hsd rho hrho Q A hA hQ z).2,
      r26t8a_f25_wd_integral hprob]
    congr 1
    have hint : ∀ i : Fin d, Integrable (fun u => (rho u * forceMean rho u i) * r26t8a_dx i Q u z) :=
      fun i => r26t8a_row_integrable hd k b hM (sigma - 1) hσ1 K hK0 (hw i).1 (hw i).2
        (by positivity : 0 ≤ 2 * A) (hdx i) z
    rw [← integral_finset_sum _ fun i _ => hint i]
    congr 1
    funext u
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pairGradX, movtr_gradient_apply,
      r26t8a_dx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hfun : (fun z => ∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho)) =
      fun z => -∑ i : Fin d, ∫ u, (rho u * forceMean rho u i) * r26t8a_dx i Q u z := funext hid
  rw [hfun]
  exact (ContDiff.sum fun i _ => (hrowi i).1).neg

end HRS.MS.R26T8A
