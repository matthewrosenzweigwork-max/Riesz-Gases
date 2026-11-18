import HRS.Energy.Commutator.Basic
import HRS.Kernel.GradD1

/-!
# Clause (a): absolute convergence of the commutator integrals (packet CM-A)

Source: main manuscript lines 2820-2821 (`B:eq:commutator-quantity` and the sentence after it).

**Route.**  For `x ≠ y` the symmetrised kernel is `|(v(x)-v(y))·∇g(x-y)| ≤ L·tdist(x,y)·|∇g(x-y)|`,
and `|∇g(z)| ≤ C(tdist(z,0)^{-s-1} + 1)` (`KernelGrad.periodicRieszGrad_bound_tdist` for `2 ≤ d`,
`KernelGradD1.periodicRieszGrad_bound_tdist` for `d = 1`), hence `|k(x,y)| ≤ C L (tdist^{-s} + 1)`
(`tdist ≤ √d/2`).  `tdist(·,0)^{-s}` is integrable on `𝕋^d` for `s < d`
(`KernelGrad.integrable_norm_rpow_neg`, `norm_le_tdist`, `integrableOn_min_rpow`); against a density
`ρ ≤ Λ` both `∫ k(X_i, y) ρ(y) dy` and `∬ k ρ ρ` are then absolutely convergent (Tonelli with
`KernelAux2.lintegral_sub_left_torus`).  No analysis risk, ~250 lines.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d N : ℕ} {s : ℝ}

/-- A Lipschitz field is continuous. -/
theorem IsLipschitzVF.continuous {L : ℝ} {v : Torus d → Euc d} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    Continuous v := by
  have hK : (0 : ℝ) ≤ L * d := mul_nonneg hL (Nat.cast_nonneg d)
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (L * d)) fun x y => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]
  calc ‖v x - v y‖ ≤ L * KernelGrad.tdist x y := hv x y
    _ ≤ L * (d * ‖x - y‖) := by
        gcongr
        rw [KernelGrad.tdist_eq_sub_zero]
        exact KernelGrad.tdist_le_mul_norm _
    _ = L * d * ‖x - y‖ := by ring

/-- Pointwise bound of the symmetrised kernel: `|k(x,y)| ≤ C L (|x-y|^{-s} + 1)` for `x ≠ y`, with
`C = C(d,s)` independent of `L` and `v`. -/
theorem commKernel_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
      ∀ x y : Torus d, x ≠ y →
        |commKernel (periodicRieszGrad d s) v x y| ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := by
  obtain ⟨C₀, hC₀⟩ := KernelGradD1.periodicRieszGrad_bound_tdist_aux_of_one_le hd hs0 hsd
  refine ⟨|C₀| * (d + 1), by positivity, fun L v hL hv x y hxy => ?_⟩
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have ht : 0 < KernelGrad.tdist x y := by
    rw [KernelGrad.tdist_eq_sub_zero]; exact KernelGrad.tdist_pos hz
  have ht0 : 0 ≤ KernelGrad.tdist x y := ht.le
  -- `t ≤ d`: `tdist ≤ d ‖x-y‖ ≤ d/2`
  have hnorm : ‖x - y‖ ≤ 1 / 2 :=
    (KernelGrad.norm_le_iff (by norm_num) _).2 fun i => KernelGrad.abs_centeredRep_le _ i
  have htd : KernelGrad.tdist x y ≤ d := by
    rw [KernelGrad.tdist_eq_sub_zero]
    refine (KernelGrad.tdist_le_mul_norm _).trans ?_
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  -- gradient bound at `x - y`
  have hG : ‖periodicRieszGrad d s (x - y)‖ ≤ |C₀| * (KernelGrad.tdist x y ^ (-s - 1) + 1) := by
    rw [KernelGrad.tdist_eq_sub_zero]
    refine (hC₀ _ hz).trans (mul_le_mul_of_nonneg_right (le_abs_self C₀) ?_)
    exact add_nonneg (Real.rpow_nonneg (KernelGrad.tdist_nonneg _ _) _) zero_le_one
  have hB : KernelGrad.tdist x y ^ (-s) = KernelGrad.tdist x y ^ (-s - 1) * KernelGrad.tdist x y := by
    have h1 := Real.rpow_add_one ht.ne' (-s - 1)
    rw [← h1]; congr 1; ring
  have hB0 : 0 ≤ KernelGrad.tdist x y ^ (-s) := Real.rpow_nonneg ht0 _
  have hv' : ‖v x - v y‖ ≤ L * KernelGrad.tdist x y := hv x y
  calc |commKernel (periodicRieszGrad d s) v x y|
      = |inner ℝ (v x - v y) (periodicRieszGrad d s (x - y))| := by
        unfold commKernel; rw [if_neg hxy]
    _ ≤ ‖v x - v y‖ * ‖periodicRieszGrad d s (x - y)‖ := abs_real_inner_le_norm _ _
    _ ≤ (L * KernelGrad.tdist x y) * (|C₀| * (KernelGrad.tdist x y ^ (-s - 1) + 1)) :=
        mul_le_mul hv' hG (norm_nonneg _) (mul_nonneg hL ht0)
    _ = |C₀| * L * (KernelGrad.tdist x y ^ (-s) + KernelGrad.tdist x y) := by rw [hB]; ring
    _ ≤ |C₀| * L * ((d + 1) * (KernelGrad.tdist x y ^ (-s) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) hL)
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith
    _ = |C₀| * (d + 1) * L * (KernelGrad.tdist x y ^ (-s) + 1) := by ring

/-- A bounded density gives a measure dominated by a multiple of Lebesgue measure. -/
theorem absConv_withDensityReal_le {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) :
    withDensityReal ρ ≤ ENNReal.ofReal B • (volume : Measure (Torus d)) := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold withDensityReal
  rw [withDensity_apply', Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ a in A, ENNReal.ofReal (ρ a) ≤ ∫⁻ _ in A, ENNReal.ofReal B :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hB a)
    _ = ENNReal.ofReal B * volume A := setLIntegral_const _ _

theorem absConv_isFiniteMeasure {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) :
    IsFiniteMeasure (withDensityReal ρ) := by
  refine ⟨?_⟩
  have h := Measure.le_iff'.1 (absConv_withDensityReal_le hB) Set.univ
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))

theorem absConv_integrable_mu {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B)
    {g : Torus d → ℝ} (hg : Integrable g volume) : Integrable g (withDensityReal ρ) :=
  (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure (absConv_withDensityReal_le hB)

theorem absConv_integral_mu_le {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hB0 : 0 ≤ B)
    {g : Torus d → ℝ} (hg0 : ∀ y, 0 ≤ g y) (hg : Integrable g volume) :
    ∫ y, g y ∂(withDensityReal ρ) ≤ B * ∫ y, g y := by
  have h1 := integral_mono_measure (absConv_withDensityReal_le hB) (Filter.Eventually.of_forall hg0)
    (hg.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hB0, smul_eq_mul] at h1
  exact h1

/-- Integrability on `ν ⊗ μ` from fibrewise integrability and a uniform fibrewise `L¹` bound. -/
theorem absConv_integrable_prod {ν μ : Measure (Torus d)} [IsFiniteMeasure ν] [SFinite μ]
    {F : Torus d × Torus d → ℝ} (hF : Measurable F)
    (hx : ∀ x, Integrable (fun y => F (x, y)) μ) {M : ℝ}
    (hM : ∀ x, ∫ y, ‖F (x, y)‖ ∂μ ≤ M) : Integrable F (ν.prod μ) := by
  rw [integrable_prod_iff hF.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => hx x, ?_⟩
  refine Integrable.of_bound ?_ M (Filter.Eventually.of_forall fun x => ?_)
  · exact (hF.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hM x

/-- **Clause (a) of `commutator_estimate`.**  For a probability density bounded by `Λ` and a
Lipschitz field, the integrals defining `offDiagPairing` converge absolutely. -/
theorem offDiagIntegrable_of_lipschitz (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} {N : ℕ}
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) (X : Config d N)
    {L : ℝ} {v : Torus d → Euc d} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    OffDiagIntegrable (commKernel (periodicRieszGrad d s) v) X (withDensityReal ρ) := by
  obtain ⟨C, hC0, hC⟩ := commKernel_bound hd hs0 hsd
  have hK : 0 ≤ C * L := mul_nonneg hC0 hL
  have hvc : Continuous v := IsLipschitzVF.continuous hL hv
  have hmeas : Measurable (fun p : Torus d × Torus d => commKernel (periodicRieszGrad d s) v p.1 p.2) := by
    unfold commKernel
    refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
    refine Measurable.inner ?_ ?_
    · exact (hvc.measurable.comp measurable_fst).sub (hvc.measurable.comp measurable_snd)
    · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)
  -- pointwise bound by a function of `x - y`
  have hbound : ∀ x y : Torus d,
      |commKernel (periodicRieszGrad d s) v x y| ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      unfold commKernel
      rw [if_pos rfl, abs_zero]
      exact mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one)
    · have h1 := hC L v hL hv x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have h2 : KernelGrad.tdist x y ^ (-s) ≤ ‖x - y‖ ^ (-s) := by
        rw [KernelGrad.tdist_eq_sub_zero]
        exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hz) (KernelGrad.norm_le_tdist _)
          (by linarith)
      calc |commKernel (periodicRieszGrad d s) v x y|
          ≤ C * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ (C * L) * (‖x - y‖ ^ (-s) + 1) := mul_le_mul_of_nonneg_left (by linarith) hK
  have hgi : Integrable (fun z : Torus d => (C * L) * (‖z‖ ^ (-s) + 1)) volume :=
    ((KernelGrad.integrable_norm_rpow_neg (by omega) hsd).add (integrable_const _)).const_mul _
  have hgi' : ∀ x : Torus d, Integrable (fun y : Torus d => (C * L) * (‖x - y‖ ^ (-s) + 1)) volume :=
    fun x => hgi.comp_sub_left x
  have hΛB : ∀ x, ρ x ≤ max Λ 0 := fun x => (hΛ x).trans (le_max_left _ _)
  have hB0 : 0 ≤ max Λ 0 := le_max_right _ _
  haveI := absConv_isFiniteMeasure hΛB
  have hx : ∀ x : Torus d,
      Integrable (fun y => commKernel (periodicRieszGrad d s) v x y) (withDensityReal ρ) := by
    intro x
    refine Integrable.mono' (absConv_integrable_mu hΛB (hgi' x)) ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hbound x y
  refine ⟨fun i => hx (X i), ?_⟩
  refine absConv_integrable_prod (ν := withDensityReal ρ) (μ := withDensityReal ρ) hmeas hx
    (M := max Λ 0 * ∫ z : Torus d, (C * L) * (‖z‖ ^ (-s) + 1)) fun x => ?_
  have h1 : ∫ y, ‖commKernel (periodicRieszGrad d s) v x y‖ ∂(withDensityReal ρ)
      ≤ ∫ y, (C * L) * (‖x - y‖ ^ (-s) + 1) ∂(withDensityReal ρ) :=
    integral_mono (hx x).norm (absConv_integrable_mu hΛB (hgi' x)) fun y => by
      rw [Real.norm_eq_abs]; exact hbound x y
  have h2 : ∫ y : Torus d, (C * L) * (‖x - y‖ ^ (-s) + 1)
      = ∫ z : Torus d, (C * L) * (‖z‖ ^ (-s) + 1) :=
    integral_sub_left_eq_self (fun z : Torus d => (C * L) * (‖z‖ ^ (-s) + 1)) volume x
  refine h1.trans ?_
  rw [← h2]
  exact absConv_integral_mu_le hΛB hB0
    (fun y => mul_nonneg hK (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one))
    (hgi' x)

end HRS.Commutator
