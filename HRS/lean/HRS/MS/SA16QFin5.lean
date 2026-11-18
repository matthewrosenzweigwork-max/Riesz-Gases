import HRS.MS.SA16QFin4

/-!
# S.A.16 (SA16Q), E6 part 19: the Cauchy estimate for the mollified operators
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Fin5
variable {d : ℕ}

/-- `‖ ‖D^κ(a_N - μ)‖ ‖D^n u‖ ‖_R` -/
def sa16q_T (μ : Euc d → ℝ) (u : 𝓢(Euc d, ℝ)) (N κ n : ℕ) (R : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖ *
    ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal R) volume

lemma sa16q_tri {μ : Euc d → ℝ} {κ : ℕ} (hμ : ContDiff ℝ κ μ) (N N' : ℕ) (u : 𝓢(Euc d, ℝ)) (n : ℕ)
    {R : ℝ} (hR : 1 ≤ R) :
    eLpNorm (fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - sa16q_mol N' μ y) x‖ *
      ‖iteratedFDeriv ℝ n u x‖) (ENNReal.ofReal R) volume ≤ sa16q_T μ u N κ n R + sa16q_T μ u N' κ n R := by
  have hμc : Continuous μ := hμ.continuous
  have hmolk : ∀ N, ContDiff ℝ κ (sa16q_mol N μ) := fun N =>
    (sa16y_mollify_smooth N hμc).of_le (by exact_mod_cast le_top)
  have hdiff : ∀ N, ContDiff ℝ κ (fun y => sa16q_mol N μ y - μ y) := fun N => (hmolk N).sub hμ
  have hGc : Continuous (fun x => ‖iteratedFDeriv ℝ n u x‖) :=
    (u.smooth'.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).norm
  have h1R : 1 ≤ ENNReal.ofReal R := by simpa using ENNReal.ofReal_le_ofReal hR
  have hec : ∀ N, Continuous (fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖) :=
    fun N => ((hdiff N).continuous_iteratedFDeriv le_rfl).norm
  have hpt : ∀ x, ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - sa16q_mol N' μ y) x‖ ≤
      ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖ +
        ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N' μ y - μ y) x‖ := by
    intro x
    have e : (fun y => sa16q_mol N μ y - sa16q_mol N' μ y) =
        (fun y => sa16q_mol N μ y - μ y) - (fun y => sa16q_mol N' μ y - μ y) := by
      funext y; simp
    rw [e, iteratedFDeriv_sub_apply (hdiff N).contDiffAt (hdiff N').contDiffAt]
    exact norm_sub_le _ _
  have hmeas : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ κ
      (fun y => sa16q_mol N μ y - sa16q_mol N' μ y) x‖ * ‖iteratedFDeriv ℝ n u x‖) volume := by
    have hsm : ContDiff ℝ κ (fun y => sa16q_mol N μ y - sa16q_mol N' μ y) := (hmolk N).sub (hmolk N')
    exact ((hsm.continuous_iteratedFDeriv le_rfl).norm.mul hGc).aestronglyMeasurable
  refine (eLpNorm_mono_ae_real (g := fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖ *
      ‖iteratedFDeriv ℝ n u x‖ + ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N' μ y - μ y) x‖ *
      ‖iteratedFDeriv ℝ n u x‖) hmeas (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul, norm_norm, norm_norm, ← add_mul]
    exact mul_le_mul_of_nonneg_right (hpt x) (norm_nonneg _)
  · have := eLpNorm_add_le (μ := volume) (p := ENNReal.ofReal R)
      (f := fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N μ y - μ y) x‖ * ‖iteratedFDeriv ℝ n u x‖)
      (g := fun x => ‖iteratedFDeriv ℝ κ (fun y => sa16q_mol N' μ y - μ y) x‖ * ‖iteratedFDeriv ℝ n u x‖)
      h1R
    exact this

/-- the total of all the quantities `T` -/
def sa16q_TS (μ : Euc d → ℝ) (u : 𝓢(Euc d, ℝ)) (m : ℕ) (q r : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ κ ∈ Finset.range (m + 2), ∑ n ∈ Finset.range (m + 1), (sa16q_T μ u N κ n r + sa16q_T μ u N κ n q)

lemma sa16q_T_le_TS (μ : Euc d → ℝ) (u : 𝓢(Euc d, ℝ)) {m : ℕ} (q r : ℝ) (N : ℕ) {κ n : ℕ}
    (hκ : κ ≤ m + 1) (hn : n ≤ m) :
    sa16q_T μ u N κ n r ≤ sa16q_TS μ u m q r N ∧ sa16q_T μ u N κ n q ≤ sa16q_TS μ u m q r N := by
  have h1 : sa16q_T μ u N κ n r + sa16q_T μ u N κ n q ≤ sa16q_TS μ u m q r N := by
    have h1a : sa16q_T μ u N κ n r + sa16q_T μ u N κ n q ≤ ∑ n' ∈ Finset.range (m + 1),
        (sa16q_T μ u N κ n' r + sa16q_T μ u N κ n' q) :=
      Finset.single_le_sum (s := Finset.range (m + 1))
        (f := fun n' => sa16q_T μ u N κ n' r + sa16q_T μ u N κ n' q)
        (fun _ _ => bot_le) (Finset.mem_range.2 (by omega : n < m + 1))
    have h1b : ∑ n' ∈ Finset.range (m + 1), (sa16q_T μ u N κ n' r + sa16q_T μ u N κ n' q) ≤
        sa16q_TS μ u m q r N :=
      Finset.single_le_sum (s := Finset.range (m + 2))
        (f := fun κ' => ∑ n' ∈ Finset.range (m + 1),
          (sa16q_T μ u N κ' n' r + sa16q_T μ u N κ' n' q))
        (fun _ _ => bot_le) (Finset.mem_range.2 (by omega : κ < m + 2))
    exact h1a.trans h1b
  exact ⟨le_trans le_self_add h1, le_trans le_add_self h1⟩

lemma sa16q_TS_tendsto {μ : Euc d → ℝ} {m : ℕ} (hμ : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) μ) {Λ1 : ℝ}
    (hΛ : 0 ≤ Λ1)
    (hw : ∀ k ≤ m + 3, ∀ r : Fin k → Fin d, ∀ x, |partialDeriv r μ x| * (1 + ‖x‖) ^ (d + 3) ≤ Λ1)
    (u : 𝓢(Euc d, ℝ)) {q r : ℝ} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    Tendsto (sa16q_TS μ u m q r) atTop (𝓝 0) := by
  have key : ∀ κ ≤ m + 1, ∀ n (R : ℝ), 1 ≤ R → Tendsto (fun N => sa16q_T μ u N κ n R) atTop (𝓝 0) := by
    intro κ hκ n R hR
    exact sa16q_conv_term (hμ.of_le (by exact_mod_cast (by omega : κ ≤ m + 3))) hΛ
      (fun r' x => hw κ (by omega) r' x) u n hR
  have : (0 : ℝ≥0∞) = ∑ κ ∈ Finset.range (m + 2), ∑ n ∈ Finset.range (m + 1), (0 + 0) := by simp
  unfold sa16q_TS
  rw [this]
  refine tendsto_finset_sum _ fun κ hκ => tendsto_finset_sum _ fun n _ => ?_
  exact (key κ (by have := Finset.mem_range.1 hκ; omega) n r hr).add
    (key κ (by have := Finset.mem_range.1 hκ; omega) n q hq)

end Fin5

end HRS.Whole.AppendixA.Phase2SA16Q
