import HRS.Equilibrium.Parametrix.PX3aAuxC
import HRS.Equilibrium.Parametrix.PX2AuxD

/-!
# Packet PX3a auxiliaries D: homogeneity and derivative bounds of the fundamental solution
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The additive constant in the scaling law of `Efund` (`0` unless `d = 2`). -/
def Ekap (d : ℕ) (t : ℝ) : ℝ := if d = 2 then -(1 / (4 * Real.pi)) * Real.log (t ^ 2) else 0

lemma Efund_smul (hd : 2 ≤ d) {t : ℝ} (ht : 0 < t) {z : Euc d} (hz : z ≠ 0) :
    Efund d (t • z) = t ^ ((2 : ℝ) - d) * Efund d z + Ekap d t := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  unfold Efund e0 Ekap
  rw [h1]
  by_cases h2 : d = 2
  · simp only [h2, if_true]
    subst h2
    rw [mul_pow, Real.log_mul (by positivity) (by positivity)]
    simp
    ring
  · simp only [h2, if_false, add_zero]
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
    have : (t ^ 2) ^ (((2 : ℝ) - d) / 2) = t ^ ((2 : ℝ) - d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1; push_cast; ring
    rw [this]; ring

lemma contDiffOn_Efund (n : WithTop ℕ∞) : ContDiffOn ℝ n (Efund d) {0}ᶜ :=
  fun z hz => (contDiffAt_Efund n hz).contDiffWithinAt

lemma iteratedFDeriv_Efund_smul (hd : 2 ≤ d) {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : 0 < t)
    {y : Euc d} (hy : y ≠ 0) :
    iteratedFDeriv ℝ j (Efund d) (t • y) =
      t ^ ((2 : ℝ) - d - j) • iteratedFDeriv ℝ j (Efund d) y := by
  set L : Euc d →L[ℝ] Euc d := t • ContinuousLinearMap.id ℝ (Euc d) with hL
  have hLy : L y = t • y := by simp [hL]
  have hU : IsOpen ({0}ᶜ : Set (Euc d)) := isOpen_compl_singleton
  have hty : t • y ≠ 0 := smul_ne_zero ht.ne' hy
  have e1 := iteratedFDeriv_comp_clm_of_open hU (contDiffOn_Efund (d := d) ∞') L (x := y)
    (by rw [hLy]; exact hty) j
  have hev : (Efund d ∘ L) =ᶠ[𝓝 y] fun z => t ^ ((2 : ℝ) - d) * Efund d z + Ekap d t := by
    filter_upwards [hU.mem_nhds hy] with z hz
    simp only [Function.comp, hL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact Efund_smul hd ht hz
  have hc : ContDiffAt ℝ (j : WithTop ℕ∞) (fun z => t ^ ((2 : ℝ) - d) * Efund d z) y :=
    contDiffAt_const.mul ((contDiffAt_Efund _ hy))
  have e2 : iteratedFDeriv ℝ j (fun z => t ^ ((2 : ℝ) - d) * Efund d z + Ekap d t) y =
      t ^ ((2 : ℝ) - d) • iteratedFDeriv ℝ j (Efund d) y := by
    show iteratedFDeriv ℝ j ((fun z => t ^ ((2 : ℝ) - d) * Efund d z) + fun _ => Ekap d t) y = _
    rw [iteratedFDeriv_add_apply hc contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    show iteratedFDeriv ℝ j ((t ^ ((2 : ℝ) - d)) • Efund d) y + _ = _
    rw [iteratedFDeriv_const_smul_apply (contDiffAt_Efund _ hy)]
    simp
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, e2, hLy] at e1
  ext v
  have h1 := congrArg (fun T => T v) e1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hL,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at h1
  have h2 := (iteratedFDeriv ℝ j (Efund d) (t • y)).map_smul_univ (fun _ => t) v
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  rw [h2] at h1
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul] at h1 ⊢
  have hp : 0 < t ^ j := pow_pos ht j
  have : t ^ ((2 : ℝ) - d - j) = t ^ ((2 : ℝ) - d) / t ^ j := by
    rw [Real.rpow_sub ht, Real.rpow_natCast]
  rw [this]
  field_simp
  linarith

lemma norm_iteratedFDeriv_Efund_le (hd : 2 ≤ d) {j : ℕ} (hj : 1 ≤ j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Euc d, y ≠ 0 →
      ‖iteratedFDeriv ℝ j (Efund d) y‖ ≤ M * ‖y‖ ^ ((2 : ℝ) - d - j) := by
  have hU : IsOpen ({0}ᶜ : Set (Euc d)) := isOpen_compl_singleton
  have hcont : ContinuousOn (fun y : Euc d => ‖iteratedFDeriv ℝ j (Efund d) y‖) (Metric.sphere 0 1) := by
    have h1 : ContDiffOn ℝ (0 : WithTop ℕ∞) (iteratedFDeriv ℝ j (Efund d)) {0}ᶜ :=
      contDiffOn_iteratedFDeriv_of_isOpen hU (contDiffOn_Efund (d := d) ∞') (m := 0) (i := j)
        (by simp)
    exact (h1.continuousOn.mono (fun y hy => by
      intro h; rw [mem_singleton_iff] at h; subst h; simp at hy)).norm
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Euc d) 1).exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hy' : ‖y‖⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hn.ne') hy
  have hsph : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : Euc d) 1 := by
    simp [norm_smul, inv_mul_cancel₀ hn.ne']
  have := iteratedFDeriv_Efund_smul hd hj hn hy'
  rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at this
  rw [this, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _), mul_comm]
  have := hM _ hsph
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
  gcongr
  exact this.trans (le_max_left _ _)

end HRS.Parx

end
