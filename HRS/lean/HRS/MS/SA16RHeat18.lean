import HRS.MS.SA16RHeat17

/-!
# S.A.16 (SA16R) Heat18: general integration by parts against a translated test function

`sa16r_ibp_gen`: for smooth `h` and `ψ ∈ C_c^∞`: `∫ (∂_i h)(z) ψ(x-z) dz = ∫ h(z) (∂_i ψ)(x-z) dz`.
`sa16r_lap_ibp`: with `lap ψ x = ∑_i ∂_i∂_i ψ (x)`: `∫ (∑_i ∂_i(∂_i g_a))(z) ψ(x-z) dz = ∫ g_a(z) (lap ψ)(x-z) dz`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat18
variable {d : ℕ}

lemma sa16r_ibp_gen {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (x : Euc d)
    (e : Euc d) :
    ∫ z, fderiv ℝ h z e * ψ (x - z) = ∫ z, h z * fderiv ℝ ψ (x - z) e := by
  set f : Euc d → ℝ := fun z => ψ (x - z) with hfdef
  have hf : ContDiff ℝ ∞ f := hψ.1.comp (contDiff_const.sub contDiff_id)
  have hfs : HasCompactSupport f := hψ.2.comp_homeomorph (Homeomorph.subLeft x)
  have hfd : ∀ z, fderiv ℝ f z e = -fderiv ℝ ψ (x - z) e := by
    intro z
    have h1 : HasFDerivAt (fun z : Euc d => x - z) (-(ContinuousLinearMap.id ℝ (Euc d))) z :=
      (hasFDerivAt_id z).const_sub x
    have h2 := (hψ.1.differentiable (by simp) (x - z)).hasFDerivAt.comp z h1
    have h3 : HasFDerivAt f _ z := h2
    rw [h3.fderiv]
    simp
  have hdf : Continuous (fun z => fderiv ℝ f z e) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdh : Continuous (fun z => fderiv ℝ h z e) :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun z => fderiv ℝ f z e * h z) :=
    (hdf.mul hh.continuous).integrable_of_hasCompactSupport ((hfs.fderiv_apply ℝ e).mul_right)
  have h2 : Integrable (fun z => f z * fderiv ℝ h z e) :=
    (hf.continuous.mul hdh).integrable_of_hasCompactSupport (hfs.mul_right)
  have h3 : Integrable (fun z => f z * h z) :=
    (hf.continuous.mul hh.continuous).integrable_of_hasCompactSupport (hfs.mul_right)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e) h1 h2 h3
    (fun z _ => (hf.differentiable (by simp)) z) (fun z _ => (hh.differentiable (by simp)) z)
  have hL : ∫ z, fderiv ℝ h z e * ψ (x - z) = ∫ z, f z * fderiv ℝ h z e := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hfdef]; ring
  have hR : ∫ z, h z * fderiv ℝ ψ (x - z) e = -∫ z, fderiv ℝ f z e * h z := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hfd z]; ring
  rw [hL, hR]
  exact this

/-- the Laplacian of a function `ψ`, `∑_i ∂_i ∂_i ψ` -/
def sa16r_lap (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)

lemma sa16r_dg_contDiff (a : ℝ) (i : Fin d) : ContDiff ℝ ∞ (sa16r_dg d a i) := by
  unfold sa16r_dg
  exact (((contDiff_apply ℝ ℝ i).comp PiLp.contDiff_ofLp).neg.div_const _).mul
    (sa16r_g_contDiff (a := a))

lemma sa16r_lap_ibp {a : ℝ} (ha : 0 < a) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (x : Euc d) :
    ∫ z, (∑ i : Fin d, fderiv ℝ (sa16r_dg d a i) z (EuclideanSpace.single i 1)) * ψ (x - z) =
      ∫ z, sa16r_g d a z * sa16r_lap ψ (x - z) := by
  set e : Fin d → Euc d := fun i => EuclideanSpace.single i 1 with he
  have hψc : Continuous (fun z => ψ (x - z)) := hψ.1.continuous.comp (continuous_const.sub continuous_id)
  have hψs : HasCompactSupport (fun z => ψ (x - z)) := hψ.2.comp_homeomorph (Homeomorph.subLeft x)
  have hψi : ∀ i : Fin d, IsCcInfty (fun y => fderiv ℝ ψ y (e i)) := fun i => sa16s_cc_fderiv hψ (e i)
  have hint1 : ∀ i : Fin d, Integrable (fun z => fderiv ℝ (sa16r_dg d a i) z (e i) * ψ (x - z)) := by
    intro i
    have hc : Continuous (fun z => fderiv ℝ (sa16r_dg d a i) z (e i)) :=
      ((sa16r_dg_contDiff a i).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.mul hψc).integrable_of_hasCompactSupport hψs.mul_left
  have hint2 : ∀ i : Fin d, Integrable (fun z => sa16r_g d a z *
      fderiv ℝ (fun y => fderiv ℝ ψ y (e i)) (x - z) (e i)) := by
    intro i
    obtain ⟨B, hB⟩ := sa16r_cc_bdd (sa16s_cc_fderiv (hψi i) (e i))
    refine Integrable.mono' ((sa16r_g_int ha).norm.mul_const B) ?_ (Eventually.of_forall fun z => ?_)
    · exact (sa16r_g_contDiff (a := a)).continuous.aestronglyMeasurable.mul
        (((((hψi i).1.continuous_fderiv (by simp)).clm_apply continuous_const).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB (x - z)) (norm_nonneg _)
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hint1 i)]
  simp only [sa16r_lap, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hint2 i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := sa16r_ibp_gen (sa16r_dg_contDiff a i) hψ x (e i)
  have h2 := sa16r_ibp_gen (sa16r_g_contDiff (a := a)) (hψi i) x (e i)
  rw [h1]
  have h3 : ∫ z, sa16r_dg d a i z * fderiv ℝ ψ (x - z) (e i) = ∫ z, fderiv ℝ (sa16r_g d a) z (e i) *
      (fun y => fderiv ℝ ψ y (e i)) (x - z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [← sa16r_g_fderiv ha z i]
  rw [h3, h2]

end Heat18

end HRS.Whole.AppendixA.Phase2SA16R
