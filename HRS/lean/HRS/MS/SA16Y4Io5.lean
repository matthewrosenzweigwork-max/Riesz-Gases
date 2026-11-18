import HRS.MS.SA16Y4Io4
import HRS.MS.SA16QFin4

/-!
# S.A.16 (SA16Y4) Io5: the order-one master estimate `W^{m+1,p} → W^{m,p}` for smooth weighted coefficients

`sa16y4io_master`: for `1 ≤ d`, `0 ≤ s < d-1`, `p ≥ 2`, `d < p(s+1)`: there is `K < ∞` (depending on `d, s, p, m, MB, W`) such that for every `M`
with `|M_{ij}| ≤ MB`, every `a ∈ SB` with `‖D^κ a(x)‖ ≤ W (1+|x|)^{-(d+3)}` (`κ ≤ m+2`), every Schwartz `u`, `l ≤ m`:
`‖∂^idx (eucNonlocal s M a u)‖_p ≤ K ‖wJet (m+1) u‖_p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Io5
variable {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
include hd hs hs1

theorem sa16y4io_master {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) (m : ℕ) (MB W : ℝ) (hW : 0 ≤ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) →
      ∀ {a : Euc d → ℝ} (ha : sa16q_SB a),
        (∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
        ∀ (u : 𝓢(Euc d, ℝ)) {l : ℕ}, l ≤ m → ∀ (idx : Fin l → Fin d),
        eLpNorm (partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)) (ENNReal.ofReal p) volume ≤
          K * eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hp1r : 1 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨q, C1, hq1, hqp, hrel, hC1, hD1⟩ := sa16y4io_D1_bound hd hs hs1 hp hfar
  have hra : ∃ ra : ℝ, 1 ≤ ra ∧ 1 / q = 1 / ra + 1 / p := by
    refine ⟨(((d : ℝ) - s - 1) / d)⁻¹, ?_, ?_⟩
    · rw [le_inv_comm₀ one_pos (by apply div_pos <;> linarith), inv_one, div_le_one hd0]
      linarith
    · rw [one_div (((d : ℝ) - s - 1) / d)⁻¹, inv_inv]
      linarith
  obtain ⟨KQ, hKQ, hQ⟩ := sa16q_term_unif hd hp1r hq1 (Or.inr ⟨hqp, hra⟩) (m + 1) hW
  refine ⟨((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) * (ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * KQ)),
    ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d)
      (ENNReal.natCast_ne_top d)) ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKQ))
  intro M hM a ha hκ u l hl idx
  set Wj := eLpNorm (wJet (m + 1) (⇑u)) (ENNReal.ofReal p) volume with hWj
  have h2l : ENNReal.ofReal (2 ^ l) ≤ ENNReal.ofReal (2 ^ m) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hl)
  set T : Fin d → Fin d → Euc d → ℝ := fun i j x => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
    (sa16q_pdS idx (sa16q_mulS ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)))) x
    (EuclideanSpace.single i (1 : ℝ)) with hT
  have hfun : partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) =
      fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * T i j x :=
    funext fun x => sa16y4io_pd_F hd hs hs1 M ha u idx x
  have hTnorm : ∀ i j, eLpNorm (T i j) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * (KQ * Wj)) := by
    intro i j
    refine (hD1 _ i).trans (sa16q_mul_le6 ?_)
    refine (sa16q_Psi_lp ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u) idx hq1.le).trans ?_
    refine (sa16q_NP_le (KQ * Wj) (fun k hk => ?_)).trans (mul_le_mul' h2l le_rfl)
    have hcont1 : Continuous (fun x => ‖iteratedFDeriv ℝ k a x‖ *
        ‖iteratedFDeriv ℝ (l - k) (⇑(sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)) x‖) :=
      ((ha.1.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).norm).mul
        (((sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u).smooth'.continuous_iteratedFDeriv (m := l - k)
          (sa16q_nat_le_infty _)).norm)
    refine le_trans (eLpNorm_mono_real hcont1.aestronglyMeasurable (fun x => ?_))
      (hQ ha.1 (fun κ hκ' x => hκ κ (by omega) x) u (κ := k) (n := l - k + 1) (by omega) (by omega))
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hfn : (⇑(sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)) =
        fun y => fderiv ℝ (⇑u) y (EuclideanSpace.single j (1 : ℝ)) := funext (sa16q_dS_apply _ u)
    rw [hfn]
    exact sa16q_norm_iter_pd_le (a := ⇑u) u.smooth' j (l - k) x
  have hTc : ∀ i j, AEStronglyMeasurable (T i j) volume := fun i j =>
    (sa16y4io_cont_D1 hd hs hs1 _ i).aestronglyMeasurable
  rw [hfun]
  refine (sa16q_eLpNorm_dsum_le (fun i j x => M j i * T i j x) hp1).trans ?_
  have hterm : ∀ i j, eLpNorm (fun x => M j i * T i j x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal MB * (ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * (KQ * Wj))) := by
    intro i j
    have e1 : (fun x => M j i * T i j x) = (M j i) • (T i j) := by funext x; simp
    rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hM j i)) (hTnorm i j)
  calc ∑ i : Fin d, ∑ j : Fin d, eLpNorm (fun x => M j i * T i j x) (ENNReal.ofReal p) volume
      ≤ ∑ i : Fin d, ∑ j : Fin d, ENNReal.ofReal MB *
          (ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * (KQ * Wj))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
end Io5

end HRS.Whole.AppendixA.Phase2SA16Q
