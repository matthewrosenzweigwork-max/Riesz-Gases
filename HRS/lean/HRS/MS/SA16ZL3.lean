import HRS.MS.SA16ZL2

/-!
# S.A.16 (SA16Z) L3: `L^p` bound of the near part of a singular integral by `‖∇f‖_p`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section L3
variable {d : ℕ}

lemma sa16z_Th_meas {f : Euc d → ℝ} (hf : IsCcInfty f) {p : ℝ} :
    Measurable (fun q : (Euc d × Euc d) × ℝ => ‖fderiv ℝ f (q.1.1 - q.2 • q.1.2)‖ₑ ^ p) := by
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have : Continuous (fun q : (Euc d × Euc d) × ℝ => fderiv ℝ f (q.1.1 - q.2 • q.1.2)) :=
    hc.comp (continuous_fst.comp continuous_fst |>.sub (continuous_snd.smul (continuous_snd.comp continuous_fst)))
  exact (this.measurable.enorm).pow_const p

lemma sa16z_D_meas {f : Euc d → ℝ} (hf : IsCcInfty f) :
    Measurable (fun q : Euc d × Euc d => sa16z_D f q.1 q.2) := by
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have h : Measurable (fun q : (Euc d × Euc d) × ℝ => ‖fderiv ℝ f (q.1.1 - q.2 • q.1.2)‖ₑ) := by
    have : Continuous (fun q : (Euc d × Euc d) × ℝ => fderiv ℝ f (q.1.1 - q.2 • q.1.2)) :=
      hc.comp (continuous_fst.comp continuous_fst |>.sub (continuous_snd.smul (continuous_snd.comp continuous_fst)))
    exact this.measurable.enorm
  exact h.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))

lemma sa16z_D_pow_le {f : Euc d → ℝ} (hf : IsCcInfty f) {p : ℝ} (hp : 1 < p) (x z : Euc d) :
    sa16z_D f x z ^ p ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p := by
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have hm : Measurable (fun t : ℝ => ‖fderiv ℝ f (x - t • z)‖ₑ) :=
    ((hc.comp (continuous_const.sub (continuous_id.smul continuous_const))).measurable).enorm
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine ⟨?_⟩; simp
  have := sa16z_jensen (volume.restrict (Ioc (0 : ℝ) 1)) hp hm.aemeasurable
  simpa [sa16z_D, Measure.restrict_apply_univ] using this

lemma sa16z_Gz_meas {f : Euc d → ℝ} (hf : IsCcInfty f) {p : ℝ} (z : Euc d) :
    Measurable (fun x : Euc d => ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p) := by
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have hm : Measurable (fun q : Euc d × ℝ => ‖fderiv ℝ f (q.1 - q.2 • z)‖ₑ ^ p) := by
    have : Continuous (fun q : Euc d × ℝ => fderiv ℝ f (q.1 - q.2 • z)) :=
      hc.comp (continuous_fst.sub (continuous_snd.smul continuous_const))
    exact this.measurable.enorm.pow_const p
  exact hm.lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))

lemma sa16z_G_int {f : Euc d → ℝ} (hf : IsCcInfty f) {p : ℝ} (z : Euc d) :
    ∫⁻ x, ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p = ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p := by
  have hc : Continuous (fderiv ℝ f) := hf.1.continuous_fderiv (by simp)
  have hm : Measurable (fun q : Euc d × ℝ => ‖fderiv ℝ f (q.1 - q.2 • z)‖ₑ ^ p) := by
    have : Continuous (fun q : Euc d × ℝ => fderiv ℝ f (q.1 - q.2 • z)) :=
      hc.comp (continuous_fst.sub (continuous_snd.smul continuous_const))
    exact this.measurable.enorm.pow_const p
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have : ∀ t : ℝ, ∫⁻ x, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p = ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p := fun t =>
    lintegral_sub_right_eq_self (fun y => ‖fderiv ℝ f y‖ₑ ^ p) (t • z)
  simp_rw [this]
  simp

lemma sa16z_swap_kappa {f : Euc d → ℝ} (hf : IsCcInfty f) {κ : Euc d → ℝ≥0∞} (hκ : Measurable κ) {p : ℝ} :
    ∫⁻ x, ∫⁻ z, κ z * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p =
      (∫⁻ z, κ z) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p := by
  have hmeas : Measurable (fun q : Euc d × Euc d => ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (q.1 - t • q.2)‖ₑ ^ p) :=
    (sa16z_Th_meas hf).lintegral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  have hm2 : Measurable (fun q : Euc d × Euc d => κ q.2 *
      ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (q.1 - t • q.2)‖ₑ ^ p) := (hκ.comp measurable_snd).mul hmeas
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have : ∀ z : Euc d, ∫⁻ x, κ z * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p =
      κ z * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p := by
    intro z
    rw [lintegral_const_mul _ (sa16z_Gz_meas hf z), sa16z_G_int hf z]
  simp_rw [this]
  rw [lintegral_mul_const _ hκ]

lemma sa16z_step1 {f : Euc d → ℝ} (hf : IsCcInfty f) {κ : Euc d → ℝ≥0∞} (hκ : Measurable κ)
    (hA : ∫⁻ z, κ z ≠ ⊤) {p : ℝ} (hp : 1 < p) (x : Euc d) :
    (∫⁻ z, κ z * sa16z_D f x z) ^ p ≤
      (∫⁻ z, κ z) ^ (p - 1) * ∫⁻ z, κ z * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (x - t • z)‖ₑ ^ p := by
  haveI : IsFiniteMeasure (volume.withDensity κ) := isFiniteMeasure_withDensity hA
  have hνuniv : (volume.withDensity κ) univ = ∫⁻ z, κ z := by
    rw [withDensity_apply _ MeasurableSet.univ]; simp
  have hDm : Measurable (fun z => sa16z_D f x z) :=
    Measurable.of_uncurry_left (f := sa16z_D f) (sa16z_D_meas hf) (x := x)
  have hj := sa16z_jensen (volume.withDensity κ) hp hDm.aemeasurable
  rw [hνuniv, lintegral_withDensity_eq_lintegral_mul _ hκ hDm,
    lintegral_withDensity_eq_lintegral_mul _ hκ (hDm.pow_const p)] at hj
  simp only [Pi.mul_apply] at hj
  refine hj.trans ?_
  gcongr with z
  exact sa16z_D_pow_le hf hp x z

end L3

end HRS.Whole.AppendixA.Phase2SA16R

