import HRS.MD.EQLZCap7
import HRS.Energy.Modulated
import HRS.PDE.TorusFPAdapter

/-!
# EQ-LZ packet CAP, helper 8: the energy of the pair cut-off tends to zero

`∫ capG (torCut (k+1)) → 0` (Lebesgue measure on `𝕋^{Nd}`), from the pointwise bound of helper 7, the transfer of the
pair integrals to `𝕋^d` and the capacity estimate of helper 6; and the packaging of `CutFam (badSet d N)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped Classical

namespace HRS.MD.EQLZ.Cap

variable {d N : ℕ}

theorem measurable_Psi (m : ℕ) : Measurable (Psi m) := by
  unfold Psi
  exact Measurable.ite ((measurableSet_le measurable_const measurable_id).inter
    (measurableSet_le measurable_id measurable_const)) measurable_inv measurable_const

theorem Psi_le_exp (m : ℕ) (τ : ℝ) : Psi m τ ≤ Real.exp (2 * m) := by
  unfold Psi
  split_ifs with h
  · calc τ⁻¹ ≤ (Real.exp (-2 * m))⁻¹ := inv_anti₀ (Real.exp_pos _) h.1
      _ = Real.exp (2 * m) := by rw [← Real.exp_neg]; congr 1; ring
  · exact (Real.exp_pos _).le

theorem integrable_Psi_sT (m : ℕ) : Integrable (fun u : Torus d => Psi m (sT u)) := by
  refine Integrable.of_bound ((measurable_Psi m).comp continuous_sT.measurable).aestronglyMeasurable
    (Real.exp (2 * m)) (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Psi_nonneg _ _)]
  exact Psi_le_exp _ _

/-- The pair separation as a function of the point of the big torus. -/
def pairSep (d N : ℕ) (p : Fin N × Fin N) (x : Torus (N * d)) : Torus d :=
  (d1_configEquiv d N).symm x p.1 - (d1_configEquiv d N).symm x p.2

theorem integrable_pair (m : ℕ) {p : Fin N × Fin N} (hp : p ∈ pairs N) :
    Integrable (fun x : Torus (N * d) => Psi m (sT (pairSep d N p x))) := by
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2.ne
  have h1 := (measurePreserving_sub_coord (d := d) (N := N) hne).integrable_comp_of_integrable
    (integrable_Psi_sT (d := d) m)
  have h2 := (d1_configEquiv_symm_measurePreserving d N).integrable_comp_of_integrable h1
  exact h2

theorem integral_pair (m : ℕ) {p : Fin N × Fin N} (hp : p ∈ pairs N) :
    ∫ x : Torus (N * d), Psi m (sT (pairSep d N p x)) = ∫ u : Torus d, Psi m (sT u) := by
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2.ne
  have hmp := measurePreserving_sub_coord (d := d) (N := N) hne
  have hG : Measurable fun u : Torus d => Psi m (sT u) := (measurable_Psi m).comp continuous_sT.measurable
  have h1 : ∫ x : Torus (N * d), Psi m (sT (pairSep d N p x)) =
      ∫ X : Config d N, Psi m (sT (X p.1 - X p.2)) := by
    rw [← d1_integral_configEquiv (d := d) (N := N)]
    simp [pairSep]
  rw [h1]
  calc ∫ X : Config d N, Psi m (sT (X p.1 - X p.2))
      = ∫ u, Psi m (sT u) ∂(Measure.map (fun X : Config d N => X p.1 - X p.2) volume) :=
        (integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hG.aestronglyMeasurable)).symm
    _ = _ := by rw [hmp.map_eq]

theorem sE_Lp_rep (p : Fin N × Fin N) (x : Torus (N * d)) :
    sE (Lp d N p (Torus.rep x)) = sT (pairSep d N p x) := by
  have h : (d1_eucEquiv d N).symm (Torus.rep x) = fun i => Torus.rep ((d1_configEquiv d N).symm x i) := by
    rw [ContinuousLinearEquiv.symm_apply_eq, d1_eucEquiv_rep, (d1_configEquiv d N).apply_symm_apply]
  rw [Lp_apply, h]
  show sE (Torus.rep ((d1_configEquiv d N).symm x p.1) - Torus.rep ((d1_configEquiv d N).symm x p.2)) = _
  rw [← sT_mk, KernelGrad.mk_sub]
  simp [pairSep, Torus.mk_rep]

/-! ### The energy estimate -/

/-- The constant of the gradient bound. -/
def Kc (d N : ℕ) (A : ℝ) : ℝ := (pairs N).card * (8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * A ^ 2

theorem Kc_nonneg (A : ℝ) : 0 ≤ Kc d N A := by
  unfold Kc
  have := CLs_nonneg (d := d) (N := N)
  positivity

theorem capG_torCut_le {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : ∀ x, |deriv Real.smoothTransition x| ≤ A)
    (x : Torus (N * d)) :
    capG (torCut d N m) x ≤ Kc d N A / (m : ℝ) ^ 2 * ∑ p ∈ pairs N, Psi m (sT (pairSep d N p x)) := by
  unfold capG
  refine (fderiv_torCut_sq hm hA _).trans (le_of_eq ?_)
  simp only [Kc, sE_Lp_rep]

theorem energy_torCut_le (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) {A : ℝ}
    (hA : ∀ x, |deriv Real.smoothTransition x| ≤ A) :
    ∫ x : Torus (N * d), capG (torCut d N m) x ≤
      Kc d N A / (m : ℝ) ^ 2 * ((pairs N).card * (2 * ((m : ℝ) + 1))) := by
  have hI : Integrable (fun x : Torus (N * d) =>
      Kc d N A / (m : ℝ) ^ 2 * ∑ p ∈ pairs N, Psi m (sT (pairSep d N p x))) :=
    (integrable_finsetSum _ (fun p hp => integrable_pair m hp)).const_mul _
  have h1 := integral_mono_of_nonneg (ae_of_all _ fun x => capG_nonneg (torCut d N m) x) hI
    (ae_of_all _ fun x => capG_torCut_le hm hA x)
  refine h1.trans ?_
  rw [integral_const_mul, integral_finsetSum _ (fun p hp => integrable_pair m hp)]
  refine mul_le_mul_of_nonneg_left ?_ (by have := Kc_nonneg (d := d) (N := N) A; positivity)
  calc ∑ p ∈ pairs N, ∫ x : Torus (N * d), Psi m (sT (pairSep d N p x))
      = ∑ p ∈ pairs N, ∫ u : Torus d, Psi m (sT u) :=
        Finset.sum_congr rfl fun p hp => integral_pair m hp
    _ ≤ ∑ p ∈ pairs N, 2 * ((m : ℝ) + 1) := Finset.sum_le_sum fun p _ => integral_Psi_sT hd hm
    _ = _ := by simp

theorem cutFam_pair (hd : 2 ≤ d) : CutFam (badSet d N) (fun k => torCut d N (k + 1)) := by
  obtain ⟨A, hA0, hA⟩ := exists_rho_deriv_bound
  refine ⟨fun k => torCut_smooth (by omega), fun k x => torCut_nonneg (by omega) x,
    fun k x => torCut_le_one (by omega) x, fun k y hy => torCut_zero_near (by omega) y hy,
    fun y hy => torCut_one_near y hy, ?_⟩
  set C : ℝ := Kc d N A * (pairs N).card * 2 with hC
  have hlim : Tendsto (fun k : ℕ => C * (2 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa using this.const_mul C
  refine squeeze_zero (fun k => integral_nonneg fun x => capG_nonneg _ _) (fun k => ?_) hlim
  have h := energy_torCut_le (N := N) hd (m := k + 1) (by omega) hA
  refine h.trans ?_
  push_cast
  have hK := Kc_nonneg (d := d) (N := N) A
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have : Kc d N A / ((k : ℝ) + 1) ^ 2 * ((pairs N).card * (2 * ((k : ℝ) + 1 + 1))) =
      C * ((k + 2) / ((k : ℝ) + 1) ^ 2) := by
    rw [hC]; field_simp; ring
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ (by rw [hC]; positivity)
  rw [div_le_iff₀ (by positivity)]
  have : 2 * (1 / ((k : ℝ) + 1)) * ((k + 1) ^ 2) = 2 * ((k : ℝ) + 1) := by field_simp
  rw [this]; nlinarith

end HRS.MD.EQLZ.Cap
