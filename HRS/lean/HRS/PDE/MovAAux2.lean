import HRS.PDE.MovAAux1
import HRS.PDE.MeanFieldThermalExist

/-!
# MOVA Aux2: convolution lemmas on the torus (kernel derivative, bounds, Lipschitz, joint continuity),
the identification `∇g * ρ = g * ∇ρ` for the cancellation convention.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_integrable_of_continuous {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem mova_bound_of_continuous {f : Torus d → ℝ} (hf : Continuous f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  obtain ⟨B, hB⟩ := PDE.MFSchauder.exists_bound_of_cont hf
  exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩

/-- Integrability of the convolution integrand. -/
theorem mova_conv_integrand_integrable {k f : Torus d → ℝ} (hk : Integrable k) (hf : Continuous f)
    (x : Torus d) : Integrable (fun z => k z * f (x - z)) :=
  PDE.MFSchauder.integrable_mul_cont hk (hf.comp (continuous_const.sub continuous_id))

theorem mova_convFun_eq (k f : Torus d → ℝ) (x : Torus d) : convFun k f x = ∫ z, k z * f (x - z) :=
  PDE.MFSchauder.convFun_eq' k f x

theorem mova_convFun_sub_left {a b f : Torus d → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hf : Continuous f) (x : Torus d) :
    convFun (fun z => a z - b z) f x = convFun a f x - convFun b f x := by
  rw [mova_convFun_eq, mova_convFun_eq, mova_convFun_eq]
  simp_rw [sub_mul]
  exact integral_sub (mova_conv_integrand_integrable ha hf x) (mova_conv_integrand_integrable hb hf x)

theorem mova_convFun_add_right {k f g : Torus d → ℝ} (hk : Integrable k) (hf : Continuous f)
    (hg : Continuous g) (x : Torus d) :
    convFun k (fun y => f y + g y) x = convFun k f x + convFun k g x := by
  rw [mova_convFun_eq, mova_convFun_eq, mova_convFun_eq]
  simp_rw [mul_add]
  exact integral_add (mova_conv_integrand_integrable hk hf x) (mova_conv_integrand_integrable hk hg x)

theorem mova_convFun_sub_right {k f g : Torus d → ℝ} (hk : Integrable k) (hf : Continuous f)
    (hg : Continuous g) (x : Torus d) :
    convFun k (fun y => f y - g y) x = convFun k f x - convFun k g x := by
  rw [mova_convFun_eq, mova_convFun_eq, mova_convFun_eq]
  simp_rw [mul_sub]
  exact integral_sub (mova_conv_integrand_integrable hk hf x) (mova_conv_integrand_integrable hk hg x)

theorem mova_convFun_const_mul_right {k f : Torus d → ℝ} (c : ℝ) (x : Torus d) :
    convFun k (fun y => c * f y) x = c * convFun k f x := by
  rw [mova_convFun_eq, mova_convFun_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

theorem mova_convFun_sum_right {k : Torus d → ℝ} {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ}
    (hk : Integrable k) (hf : ∀ i ∈ s, Continuous (f i)) (x : Torus d) :
    convFun k (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, convFun k (f i) x := by
  simp_rw [mova_convFun_eq]
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ fun i hi => mova_conv_integrand_integrable hk (hf i hi) x

/-- The `L¹` norm of a kernel. -/
def mova_L1 (k : Torus d → ℝ) : ℝ := ∫ z, |k z|

theorem mova_L1_nonneg (k : Torus d → ℝ) : 0 ≤ mova_L1 k := integral_nonneg fun z => abs_nonneg _

theorem mova_abs_convFun_le {k f : Torus d → ℝ} (hk : Integrable k) (hf : Continuous f) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (x : Torus d) : |convFun k f x| ≤ mova_L1 k * B := by
  rw [mova_convFun_eq]
  have h1 : |∫ z, k z * f (x - z)| ≤ ∫ z, |k z * f (x - z)| := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => k z * f (x - z))
  refine h1.trans ?_
  have h2 : ∫ z, |k z * f (x - z)| ≤ ∫ z, |k z| * B := by
    refine integral_mono (mova_conv_integrand_integrable hk hf x).abs (hk.abs.mul_const B) fun z => ?_
    simp only
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
  refine h2.trans (le_of_eq ?_)
  rw [integral_mul_const]
  rfl

theorem mova_tdist_sub_sub (x y z : Torus d) :
    KernelGrad.tdist (x - z) (y - z) = KernelGrad.tdist x y := by
  rw [KernelGrad.tdist_eq_sub_zero, KernelGrad.tdist_eq_sub_zero x y, sub_sub_sub_cancel_right]

theorem mova_convFun_lipschitz {k f : Torus d → ℝ} (hk : Integrable k) (hf : Continuous f) {L : ℝ}
    (hL : KernelGrad.IsLipschitz L f) (x y : Torus d) :
    |convFun k f x - convFun k f y| ≤ mova_L1 k * L * KernelGrad.tdist x y := by
  rw [mova_convFun_eq, mova_convFun_eq, ← integral_sub (mova_conv_integrand_integrable hk hf x)
    (mova_conv_integrand_integrable hk hf y)]
  have h1 : |∫ z, (k z * f (x - z) - k z * f (y - z))| ≤ ∫ z, |k z * f (x - z) - k z * f (y - z)| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun z => k z * f (x - z) - k z * f (y - z))
  refine h1.trans ?_
  have h2 : ∫ z, |k z * f (x - z) - k z * f (y - z)| ≤ ∫ z, |k z| * (L * KernelGrad.tdist x y) := by
    refine integral_mono (((mova_conv_integrand_integrable hk hf x).sub
      (mova_conv_integrand_integrable hk hf y)).abs) (hk.abs.mul_const _) fun z => ?_
    simp only
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := hL (x - z) (y - z)
    rwa [mova_tdist_sub_sub] at this
  refine h2.trans (le_of_eq ?_)
  rw [integral_mul_const]
  unfold mova_L1
  ring

/-- Kernel derivative: `∂_j (k * f) = (∂_j k) * f` for a `C¹` kernel and a continuous function. -/
theorem mova_partialDeriv_convFun_kernel {k f : Torus d → ℝ} (hk : Torus.IsCk 1 k)
    (hf : Continuous f) (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j (convFun k f) x = convFun (Torus.partialDeriv j k) f x := by
  have e1 : convFun k f = convFun f k := funext (PDE.MFThermalExist.convFun_comm k f)
  rw [e1, PDE.MFSchauder.convFun_partialDeriv (mova_integrable_of_continuous hf) hk j x]
  exact PDE.MFThermalExist.convFun_comm f _ x

/-- Function derivative: `∂_j (k * f) = k * ∂_j f` for an integrable kernel and a `C¹` function. -/
theorem mova_partialDeriv_convFun {k f : Torus d → ℝ} (hk : Integrable k) (hf : Torus.IsCk 1 f)
    (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j (convFun k f) x = convFun k (Torus.partialDeriv j f) x :=
  PDE.MFSchauder.convFun_partialDeriv hk hf j x

theorem mova_isCk_one_convFun {k f : Torus d → ℝ} (hk : Integrable k) (hf : Torus.IsCk 1 f) :
    Torus.IsCk 1 (convFun k f) := PDE.MFSchauder.convFun_isCk_one hk hf

theorem mova_isCk_two_of_partials {f : Torus d → ℝ} (h1 : Torus.IsCk 1 f)
    (h : ∀ j : Fin d, Torus.IsCk 1 (Torus.partialDeriv j f)) : Torus.IsCk 2 f := by
  have := PDE.MFHolder.isCk_succ_of_partials (m := 1) h1 (fun j => by simpa using h j)
  simpa using this

theorem mova_isCk_two_convFun {k f : Torus d → ℝ} (hk : Integrable k) (hf : Torus.IsCk 2 f) :
    Torus.IsCk 2 (convFun k f) := by
  refine mova_isCk_two_of_partials (mova_isCk_one_convFun hk (mova_isCk_one_of_two hf)) fun j => ?_
  have e : Torus.partialDeriv j (convFun k f) = convFun k (Torus.partialDeriv j f) :=
    funext fun x => mova_partialDeriv_convFun hk (mova_isCk_one_of_two hf) j x
  rw [e]
  exact mova_isCk_one_convFun hk (mova_isCk_partialDeriv hf j)

theorem mova_integrable_periodicRiesz (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) := PDE.MFOneLe.integrable_periodicRiesz hd s hs0 hsd

/-- Joint continuity of the convolution in a compact parameter. -/
theorem mova_continuous_convFun_param {P : Type*} [TopologicalSpace P] [CompactSpace P]
    [FirstCountableTopology P]
    {k : Torus d → ℝ} (hk : Integrable k) {f : P → Torus d → ℝ}
    (hf : Continuous fun q : P × Torus d => f q.1 q.2) :
    Continuous fun q : P × Torus d => convFun k (f q.1) q.2 := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := P × Torus d)).exists_bound_of_continuousOn hf.continuousOn
  have hB' : ∀ p y, |f p y| ≤ max B 0 := fun p y => by
    have := hB (p, y) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have e : (fun q : P × Torus d => convFun k (f q.1) q.2) = fun q => ∫ z, k z * f q.1 (q.2 - z) := by
    funext q; exact mova_convFun_eq _ _ _
  rw [e]
  refine continuous_of_dominated (bound := fun z => |k z| * max B 0) (fun q => ?_) (fun q => ?_)
    (hk.abs.mul_const _) (Filter.Eventually.of_forall fun z => ?_)
  · exact (hk.aestronglyMeasurable).mul
      ((hf.comp (continuous_const.prodMk (continuous_const.sub continuous_id))).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB' _ _) (abs_nonneg _)
  · exact continuous_const.mul (hf.comp (continuous_fst.prodMk (continuous_snd.sub continuous_const)))

/-- The cancellation convolution `∇g * ρ` is `g * ∇ρ` (`ρ ∈ C¹`, `g = periodicRiesz`). -/
theorem mova_convGradConv_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : Torus.IsCk 1 ρ) (j : Fin d) (x : Torus d) :
    (convGradConv (periodicRieszGrad d s) ρ x).ofLp j =
      convFun (periodicRiesz d s) (Torus.partialDeriv j ρ) x := by
  have hg := mova_integrable_periodicRiesz hd hs0 hsd
  rw [PDE.MFOneLe.convGradConv_eq_partialDeriv hd s hs0 hsd hρ (mova_isCk_one_convFun hg hρ) j x,
    mova_partialDeriv_convFun hg hρ j x]

end HRS
