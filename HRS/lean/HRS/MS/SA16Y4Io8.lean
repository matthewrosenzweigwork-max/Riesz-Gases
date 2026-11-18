import HRS.MS.SA16Y4Io7

/-!
# S.A.16 (SA16Y4) Io8: the explicit order-one master estimate (no weights)

`sa16y4io_master_exp`: for every `a ∈ SB`, Schwartz `u` and `idx`:
`‖∂^idx (eucNonlocal s M a u)‖_p ≤ (d² MB)(C₁ ∑_k C(l,k) ‖ ‖D^k a‖ ‖D^{l-k+1} u‖ ‖_q)` with `1/q = 1/p + (d-s-1)/d`
(only the `Q`-type term; no Hessian of `g`).  Used for the Cauchy property of the mollified images.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Io8
variable {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
include hd hs hs1

theorem sa16y4io_master_exp {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ q C1 : ℝ, 1 < q ∧ q < p ∧ (∃ ra : ℝ, 1 ≤ ra ∧ 1 / q = 1 / ra + 1 / p) ∧ 0 < C1 ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ), (∀ i j, |M i j| ≤ MB) →
        ∀ {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) {l : ℕ} (idx : Fin l → Fin d),
        eLpNorm (partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)) (ENNReal.ofReal p) volume ≤
          ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) * (ENNReal.ofReal C1 *
            ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) *
              eLpNorm (fun x => ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (l - k + 1) u x‖)
                (ENNReal.ofReal q) volume) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨q, C1, hq1, hqp, hrel, hC1, hD1⟩ := sa16y4io_D1_bound hd hs hs1 hp hfar
  have hra : ∃ ra : ℝ, 1 ≤ ra ∧ 1 / q = 1 / ra + 1 / p := by
    refine ⟨(((d : ℝ) - s - 1) / d)⁻¹, ?_, ?_⟩
    · rw [le_inv_comm₀ one_pos (by apply div_pos <;> linarith), inv_one, div_le_one hd0]
      linarith
    · rw [one_div (((d : ℝ) - s - 1) / d)⁻¹, inv_inv]
      linarith
  refine ⟨q, C1, hq1, hqp, hra, hC1, ?_⟩
  intro M MB hM a ha u l idx
  set T : Fin d → Fin d → Euc d → ℝ := fun i j x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
    (sa16q_pdS idx (sa16q_mulS ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)))) x
    (EuclideanSpace.single i (1 : ℝ)) with hT
  have hfun : partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) =
      fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * T i j x :=
    funext fun x => sa16y4io_pd_F hd hs hs1 M ha u idx x
  set S : ℝ≥0∞ := ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) *
    eLpNorm (fun x => ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (l - k + 1) u x‖)
      (ENNReal.ofReal q) volume with hS
  have hTnorm : ∀ i j, eLpNorm (T i j) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C1 * S := by
    intro i j
    refine (hD1 _ i).trans (sa16q_mul_le6 ?_)
    refine (sa16q_Psi_lp ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u) idx hq1.le).trans ?_
    unfold sa16q_NP
    refine Finset.sum_le_sum fun k hk => sa16q_mul_le6 ?_
    have hcont1 : Continuous (fun x => ‖iteratedFDeriv ℝ k a x‖ *
        ‖iteratedFDeriv ℝ (l - k) (⇑(sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)) x‖) :=
      ((ha.1.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm).mul
        (((sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u).smooth'.continuous_iteratedFDeriv (m := l - k)
          (sa16q_nat_le_infty _)).norm)
    refine eLpNorm_mono_real hcont1.aestronglyMeasurable (fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hfn : (⇑(sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)) =
        fun y => fderiv ℝ (⇑u) y (EuclideanSpace.single j (1 : ℝ)) := funext (sa16q_dS_apply _ u)
    rw [hfn]
    have := sa16q_norm_iter_pd_le (a := ⇑u) u.smooth' j (l - k) x
    have hlk : l - k + 1 = l - k + 1 := rfl
    exact this
  rw [hfun]
  refine (sa16q_eLpNorm_dsum_le (fun i j x => M j i * T i j x) hp1).trans ?_
  have hterm : ∀ i j, eLpNorm (fun x => M j i * T i j x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal MB * (ENNReal.ofReal C1 * S) := by
    intro i j
    have e1 : (fun x => M j i * T i j x) = (M j i) • (T i j) := by funext x; simp
    rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hM j i)) (hTnorm i j)
  calc ∑ i : Fin d, ∑ j : Fin d, eLpNorm (fun x => M j i * T i j x) (ENNReal.ofReal p) volume
      ≤ ∑ i : Fin d, ∑ j : Fin d, ENNReal.ofReal MB * (ENNReal.ofReal C1 * S) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
end Io8

end HRS.Whole.AppendixA.Phase2SA16Q
