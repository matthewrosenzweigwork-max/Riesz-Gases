import HRS.MH.ScreenedK4Aux1

/-! Packet K4 of `B:lem:screened` (S.B.4): proof of `gk_rep_L1` in `ScreenedSpec.lean`.
Fubini with `gk_weak` (K3) for every translation `y`; the kernel bound `k4_kernel_L1_bound` gives the
integrability on the product; the representative is measurable by the Fubini theorem. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem gk_rep_L1_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (i : Fin d)
    (v : Euc d → ℝ) (hv : Integrable v) :
    IsGradKernelRep d s i v (fun x => ∫ y, rieszKernelGrad d s (x - y) i * v y) := by
  have hd1 : 1 ≤ d := by omega
  have hKi : Measurable (fun u : Euc d => rieszKernelGrad d s u i) := k4_comp_measurable s i
  intro φ
  obtain ⟨hφc, hφb, hφi, -⟩ := k3_sch_props φ
  obtain ⟨C, hC0, hC⟩ := k4_kernel_L1_bound hd1 hs0 hs1 (⇑φ) hφc hφb hφi
  -- the integrand on the product `(x, y) ↦ ∂_i g(x - y) v(y) φ(x)`
  have hFm : AEStronglyMeasurable
      (fun p : Euc d × Euc d => rieszKernelGrad d s (p.1 - p.2) i * v p.2 * φ p.1) (volume.prod volume) := by
    have h1 : Measurable (fun p : Euc d × Euc d => rieszKernelGrad d s (p.1 - p.2) i) :=
      hKi.comp (measurable_fst.sub measurable_snd)
    have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => v p.2) (volume.prod volume) :=
      hv.aestronglyMeasurable.comp_snd
    have h3 : Measurable (fun p : Euc d × Euc d => φ p.1) := φ.continuous.measurable.comp measurable_fst
    exact (h1.aestronglyMeasurable.mul h2).mul h3.aestronglyMeasurable
  -- for each `y`, the `x`-section is integrable (`gk_weak`)
  have hx : ∀ y : Euc d, Integrable (fun x => rieszKernelGrad d s (x - y) i * v y * φ x) := fun y => by
    have e : (fun x => rieszKernelGrad d s (x - y) i * v y * φ x) =
        fun x => rieszKernelGrad d s (x - y) i * φ x * v y := by
      funext x; ring
    rw [e]
    exact (gk_weak_proof hd hs0 hs1 i φ y).1.mul_const (v y)
  -- pointwise bound of the `x`-integral of the norm
  have hnorm : ∀ y : Euc d, ∫ x, ‖rieszKernelGrad d s (x - y) i * v y * φ x‖ ≤ ‖v y‖ * C := by
    intro y
    obtain ⟨hI, hle⟩ := hC y
    calc ∫ x, ‖rieszKernelGrad d s (x - y) i * v y * φ x‖
        ≤ ∫ x, ‖v y‖ * (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) := by
          apply integral_mono (hx y).norm (hI.const_mul _)
          intro x
          have key : ‖rieszKernelGrad d s (x - y) i‖ * ‖φ x‖ ≤
              ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right (k4_comp_norm_le s (x - y) i) (norm_nonneg _)
          calc ‖rieszKernelGrad d s (x - y) i * v y * φ x‖
              = ‖v y‖ * (‖rieszKernelGrad d s (x - y) i‖ * ‖φ x‖) := by
                rw [norm_mul, norm_mul]; ring
            _ ≤ ‖v y‖ * (‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖) :=
                mul_le_mul_of_nonneg_left key (norm_nonneg _)
      _ = ‖v y‖ * ∫ x, ‖rieszKernelGrad d s (x - y)‖ * ‖φ x‖ := integral_const_mul _ _
      _ ≤ ‖v y‖ * C := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  -- integrability on the product
  have hFint : Integrable
      (fun p : Euc d × Euc d => rieszKernelGrad d s (p.1 - p.2) i * v p.2 * φ p.1) (volume.prod volume) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Filter.Eventually.of_forall (fun y => hx y), ?_⟩
    have hmeasN : AEStronglyMeasurable (fun y => ∫ x, ‖rieszKernelGrad d s (x - y) i * v y * φ x‖) volume :=
      (hFm.norm.prod_swap).integral_prod_right'
    refine Integrable.mono' (hv.norm.const_mul C) hmeasN (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact (hnorm y).trans_eq (mul_comm _ _)
  -- the kernel convolution `g * ∂_iφ` as the negative of an `x`-integral (`gk_weak`)
  have hconv : ∀ y : Euc d, HRS.Whole.convFun (rieszKernel d s)
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y =
        -∫ x, rieszKernelGrad d s (x - y) i * φ x := fun y => by
    rw [(gk_weak_proof hd hs0 hs1 i φ y).2, neg_neg]
  have hGb : ∀ y : Euc d, ‖∫ x, rieszKernelGrad d s (x - y) i * φ x‖ ≤ C := fun y =>
    (norm_integral_le_integral_norm _).trans (((integral_mono (gk_weak_proof hd hs0 hs1 i φ y).1.norm
      (hC y).1 (fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (k4_comp_norm_le s (x - y) i) (norm_nonneg _)))).trans (hC y).2)
  have hGmeas : AEStronglyMeasurable (fun y => ∫ x, rieszKernelGrad d s (x - y) i * φ x) volume := by
    have hH : Measurable (fun p : Euc d × Euc d => rieszKernelGrad d s (p.2 - p.1) i * φ p.2) :=
      (hKi.comp (measurable_snd.sub measurable_fst)).mul (φ.continuous.measurable.comp measurable_snd)
    exact (hH.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hB : Integrable (fun y => v y * ∫ x, rieszKernelGrad d s (x - y) i * φ x) volume := by
    refine Integrable.mono' (hv.norm.const_mul C) (hv.aestronglyMeasurable.mul hGmeas)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    calc ‖v y‖ * ‖∫ x, rieszKernelGrad d s (x - y) i * φ x‖ ≤ ‖v y‖ * C :=
          mul_le_mul_of_nonneg_left (hGb y) (norm_nonneg _)
      _ = C * ‖v y‖ := mul_comm _ _
  -- (a) integrability of `w φ`
  have ha : Integrable (fun x => (∫ y, rieszKernelGrad d s (x - y) i * v y) * φ x) volume := by
    refine hFint.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [integral_mul_const]
  -- (b) integrability of `v · (g * ∂_iφ)`
  have hb : Integrable (fun y => v y * HRS.Whole.convFun (rieszKernel d s)
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y) volume := by
    have e : (fun y => v y * HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y) =
        fun y => -(v y * ∫ x, rieszKernelGrad d s (x - y) i * φ x) := by
      funext y; rw [hconv y, mul_neg]
    rw [e]
    exact hB.neg
  -- (c) the identity
  have h2 : ∀ y : Euc d, ∫ x, rieszKernelGrad d s (x - y) i * v y * φ x =
      v y * ∫ x, rieszKernelGrad d s (x - y) i * φ x := by
    intro y
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have hc : ∫ x, (∫ y, rieszKernelGrad d s (x - y) i * v y) * φ x =
      -∫ y, v y * HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y := by
    have h1 : ∫ x, (∫ y, rieszKernelGrad d s (x - y) i * v y) * φ x =
        ∫ x, ∫ y, rieszKernelGrad d s (x - y) i * v y * φ x := by
      congr 1; funext x; rw [integral_mul_const]
    rw [h1, integral_integral_swap (f := fun x y => rieszKernelGrad d s (x - y) i * v y * φ x) hFint]
    simp only [h2, hconv, mul_neg, integral_neg, neg_neg]
  exact ⟨ha, hb, hc⟩

end HRS.MH.Screened
