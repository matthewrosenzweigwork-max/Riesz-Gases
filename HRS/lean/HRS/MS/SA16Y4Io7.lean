import HRS.MS.SA16Y4Io6
import HRS.MS.SA16QFin5
import HRS.MS.SA16QFin4

/-!
# S.A.16 (SA16Y4) Io7: data of the mollifications up to order `m+2`, smoothness of `eucNonlocal`, and the tail quantity `TS'`

`sa16y4io_mol_data` (weights for `κ ≤ m+2`), `sa16y4io_F_smooth`, `sa16y4io_TS` with `sa16y4io_TS_tendsto`, `sa16y4io_T_le_TS`
(`κ ≤ m`, `n ≤ m+1`, exponent `q` only), used for the Cauchy property of the mollified images in the order-one estimate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Io7
variable {d : ℕ}

lemma sa16y4io_mol_data (hd1 : 1 ≤ d) {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ)
    (N : ℕ) :
    sa16q_SB (sa16q_mol N μ) ∧
      (∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ (sa16q_mol N μ) x‖ ≤
        (d : ℝ) ^ (m + 2) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) := by
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have hμc : Continuous μ := hC.continuous
  refine ⟨sa16q_mol_SB N hμc (sa16q_reg_abs hμ), fun κ hκ x => ?_⟩
  have hμκ : ContDiff ℝ κ μ := hC.of_le (by exact_mod_cast (by omega : κ ≤ m + 3))
  have hΛ : 0 ≤ max Λ 0 := le_max_right _ _
  have h1 := sa16q_weight_conv (a := sa16q_mol N μ) (κ := κ) (Λ2 := 2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0))
    (fun r y => sa16q_mol_pd_weight N hμκ (Λ1 := 2 ^ (d + 3) * max Λ 0)
      (fun r' y' => hw κ (by omega) r' y') r y) x
  refine h1.trans ?_
  have hω : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hpw : (d : ℝ) ^ κ ≤ (d : ℝ) ^ (m + 2) := pow_le_pow_right₀ hd0 (by omega)
  have hc : 0 ≤ 2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpw hc) hω

lemma sa16y4io_F_smooth (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
    (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ ∞ (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) := by
  set Ψ : Fin d → 𝓢(Euc d, ℝ) := fun j => sa16q_mulS ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u) with hΨ
  have hGs : ∀ ψ : 𝓢(Euc d, ℝ), ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) :=
    fun ψ => sa16y4io_conv_contDiff_top hd hs hs1 ψ
  have hBs : ∀ (ψ : 𝓢(Euc d, ℝ)) (i : Fin d), ContDiff ℝ ∞
      (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) y (EuclideanSpace.single i (1 : ℝ))) :=
    fun ψ i => ((hGs ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have e : ∀ j : Fin d, (fun x' => ∫ y, rieszKernel d s (x' - y) *
      (a y * fderiv ℝ ⇑u y (EuclideanSpace.single j (1 : ℝ)))) = HRS.Whole.convFun (rieszKernel d s) (Ψ j) := by
    intro j
    funext x'
    simp only [HRS.Whole.convFun, hΨ, sa16q_mulS_apply, sa16q_dS_apply]
  have hfun : HRS.MH.AdjointRd.eucNonlocal s M a ⇑u = fun y => ∑ i : Fin d, ∑ j : Fin d, M j i *
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Ψ j)) y (EuclideanSpace.single i (1 : ℝ)) := by
    funext y
    unfold HRS.MH.AdjointRd.eucNonlocal
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [e j]
  rw [hfun]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hBs (Ψ j) i)

/-- tail quantity: `∑_{κ ≤ m, n ≤ m+1} ‖ ‖D^κ(a_N - μ)‖ ‖D^n u‖ ‖_q` -/
def sa16y4io_TS (μ : Euc d → ℝ) (u : 𝓢(Euc d, ℝ)) (m : ℕ) (q : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ κ ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 2), sa16q_T μ u N κ n q

lemma sa16y4io_T_le_TS (μ : Euc d → ℝ) (u : 𝓢(Euc d, ℝ)) {m : ℕ} (q : ℝ) (N : ℕ) {κ n : ℕ}
    (hκ : κ ≤ m) (hn : n ≤ m + 1) : sa16q_T μ u N κ n q ≤ sa16y4io_TS μ u m q N := by
  have h1 : sa16q_T μ u N κ n q ≤ ∑ n' ∈ Finset.range (m + 2), sa16q_T μ u N κ n' q :=
    Finset.single_le_sum (s := Finset.range (m + 2)) (f := fun n' => sa16q_T μ u N κ n' q)
      (fun _ _ => bot_le) (Finset.mem_range.2 (by omega : n < m + 2))
  refine h1.trans ?_
  exact Finset.single_le_sum (s := Finset.range (m + 1))
    (f := fun κ' => ∑ n' ∈ Finset.range (m + 2), sa16q_T μ u N κ' n' q)
    (fun _ _ => bot_le) (Finset.mem_range.2 (by omega : κ < m + 1))

lemma sa16y4io_TS_tendsto {μ : Euc d → ℝ} {m : ℕ} (hμ : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) μ) {Λ1 : ℝ}
    (hΛ : 0 ≤ Λ1)
    (hw : ∀ k ≤ m + 3, ∀ r : Fin k → Fin d, ∀ x, |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3) ≤ Λ1)
    (u : 𝓢(Euc d, ℝ)) {q : ℝ} (hq : 1 ≤ q) :
    Tendsto (sa16y4io_TS μ u m q) atTop (𝓝 0) := by
  have : (0 : ℝ≥0∞) = ∑ κ ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (m + 2), 0 := by simp
  unfold sa16y4io_TS
  rw [this]
  refine tendsto_finset_sum _ fun κ hκ => tendsto_finset_sum _ fun n _ => ?_
  have hk : κ ≤ m := by have := Finset.mem_range.1 hκ; omega
  exact sa16q_conv_term (hμ.of_le (by exact_mod_cast (by omega : κ ≤ m + 3))) hΛ
    (fun r' x => hw κ (by omega) r' x) u n hq
end Io7

end HRS.Whole.AppendixA.Phase2SA16Q
