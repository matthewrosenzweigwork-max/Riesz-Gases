import HRS.MH.ConventionHolder2

/-!
# `convGradConv_coeff_of_holder`

Relocation of `HRS.convGradConv_coeff_of_holder`.

Route (decided before writing code; est. 130 lines, far below the 1200-line limit).  The repo's
proof of the `C¹` version (`KernelGradD1.coeff_convGradConv_lip_of_one_le`, `GradD1.lean`, and its
`d ≥ 2` twin in `GradFourier.lean`) regularises the kernel by the heat kernel `heatRieszGrad ε`
(uniformly `GoodKernel`, with continuous kernel, so the Fourier coefficient of the convolution is
explicit: `KernelGrad.coeff_convGradConv_heat`) and passes to the limit `ε → 0` by dominated
convergence; the only place where `C¹` (Lipschitz) is used is the *domination* of the integrand
`kern G_ε h x` and the uniform bound of `convGradConv G_ε h`.  Replacing the Lipschitz
domination `L C (|z|^{-s}+d) + B C (...)` by the Hölder domination of
`Duality.kern_norm_holder`/`integrable_dom_holder`
(`Λ C (|z|^{β-s-1} + |z|^β) + B C (...)`, valid for all uniformly good kernels at once) gives the
Hölder version verbatim: no mollification of `ρ` is needed.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.ConventionHolder

variable {d : ℕ} {s C : ℝ} {G : Torus d → Euc d}

/-- The Hölder dominating function. -/
def chDom (s C Λ B β : ℝ) (d : ℕ) (z : Torus d) : ℝ :=
  Λ * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β) + B * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)

theorem ch_integrable_dom (hG : KernelGrad.GoodKernel d s C G) {Λ B β : ℝ} (hβ0 : 0 < β)
    (hβ : s + 1 - d < β) : Integrable (chDom s C Λ B β d) :=
  Duality.integrable_dom_holder hG hβ0 hβ

theorem ch_kern_bound_ae (hG : KernelGrad.GoodKernel d s C G) {h : Torus d → ℝ} {B Λ β : ℝ}
    (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d) :
    ∀ᵐ z : Torus d, ‖KernelGrad.kern G h x z‖ ≤ chDom s C Λ B β d z := by
  filter_upwards [KernelGrad.torus_ae_ne' hG.pos] with z hz
  exact Duality.kern_norm_holder hG hB hB0 hΛ hH x hz

/-- Continuity of the cancellation convolution of a Hölder function. -/
theorem ch_continuous_op (hG : KernelGrad.GoodKernel d s C G) {h : Torus d → ℝ} (hc : Continuous h)
    {B Λ β : ℝ} (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ) (hβ0 : 0 < β)
    (hβ : s + 1 - d < β)
    (hH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) :
    Continuous (HRS.convGradConv G h) := by
  have : HRS.convGradConv G h = fun x => ∫ z, KernelGrad.kern G h x z :=
    funext (KernelGrad.convGradConv_eq_integral_kern G h)
  rw [this]
  refine continuous_of_dominated (bound := chDom s C Λ B β d)
    (fun x => (KernelGrad.measurable_kern hG hc.measurable x).aestronglyMeasurable)
    (fun x => ch_kern_bound_ae hG hB hB0 hΛ hH x) (ch_integrable_dom hG hβ0 hβ)
    (Eventually.of_forall fun z => ?_)
  unfold KernelGrad.kern
  split_ifs
  · fun_prop
  · fun_prop

theorem ch_bound_op (hG : KernelGrad.GoodKernel d s C G) {h : Torus d → ℝ} {B Λ β : ℝ}
    (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ) (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d) :
    ‖HRS.convGradConv G h x‖ ≤ ∫ z, chDom s C Λ B β d z := by
  rw [KernelGrad.convGradConv_eq_integral_kern]
  exact norm_integral_le_of_norm_le (ch_integrable_dom hG hβ0 hβ)
    (ch_kern_bound_ae hG hB hB0 hΛ hH x)

/-- Pointwise convergence of the heat-regularised convolutions, with Hölder domination. -/
theorem ch_tendsto_heat (hsd : s < d)
    (hGε : ∀ ε : ℝ, 0 < ε → KernelGrad.GoodKernel d s C (heatRieszGrad d s ε))
    {h : Torus d → ℝ} (hh : Continuous h) {B Λ β : ℝ} (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B)
    (hΛ : 0 ≤ Λ) (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) (x : Torus d) :
    Tendsto (fun ε => HRS.convGradConv (heatRieszGrad d s ε) h x) (𝓝[>] 0)
      (𝓝 (HRS.convGradConv (periodicRieszGrad d s) h x)) := by
  simp_rw [KernelGrad.convGradConv_eq_integral_kern]
  refine tendsto_integral_filter_of_dominated_convergence (chDom s C Λ B β d) ?_ ?_
    (ch_integrable_dom (hGε 1 one_pos) hβ0 hβ) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (KernelGrad.measurable_kern (hGε ε hε) hh.measurable x).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ch_kern_bound_ae (hGε ε hε) hB hB0 hΛ hH x
  · refine Eventually.of_forall fun z => ?_
    unfold KernelGrad.kern
    split_ifs
    · exact ((KernelGrad.heat_tendsto hsd z).const_smul _)
    · exact ((KernelGrad.heat_tendsto hsd z).const_smul _)

open scoped ComplexConjugate in
/-- Fourier coefficients of `∇g * h` (cancellation convention) for a Hölder function `h`
(copy of `KernelGradD1.coeff_convGradConv_lip_of_one_le` with the Hölder domination). -/
theorem ch_coeff_holder {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hcont : Continuous h) {B Λ β : ℝ} (hB : ∀ x, |h x| ≤ B) (hB0 : 0 ≤ B) (hΛ : 0 ≤ Λ)
    (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β)
    (k : Lattice d) (i : Fin d) :
    ∫ x, Torus.mode (-k) x * ((HRS.convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hGε⟩ := KernelGradD1.goodKernel_heat_of_one_le hd hs0 hsd
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  have hLHS : Tendsto (fun ε : ℝ => ∫ x, Torus.mode (-k) x *
      ((HRS.convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ)) l
      (𝓝 (∫ x, Torus.mode (-k) x * ((HRS.convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hc := ch_continuous_op (hGε ε hε) hcont hB hB0 hΛ hβ0 hβ hH
      have : Continuous fun x : Torus d => Torus.mode (-k) x *
          ((HRS.convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ) :=
        (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hc))
      exact this.aestronglyMeasurable
    · refine ⟨∫ z, chDom s C Λ B β d z, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans ?_ (ch_bound_op (hGε ε hε) hB hB0 hΛ hβ0 hβ hH x)
      have := PiLp.norm_apply_le (HRS.convGradConv (heatRieszGrad d s ε) h x) i
      simpa using this
    · refine Eventually.of_forall fun x => ?_
      have := ch_tendsto_heat hsd hGε hcont hB hB0 hΛ hβ0 hβ hH x
      have h2 := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp this
      exact (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h2))
  set R : ℝ → ℂ := fun ε => (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
    ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
      ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ)) with hR
  have hRc : Continuous R := by
    simp only [hR]
    fun_prop
  have hRHS : Tendsto R l (𝓝 ((∫ y, Torus.mode (-k) y * (h y : ℂ)) *
      ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)))) := by
    have := (hRc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hR] using this
  have hEq : (fun ε : ℝ => ∫ x, Torus.mode (-k) x *
      ((HRS.convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ)) =ᶠ[l] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact KernelGrad.coeff_convGradConv_heat hsd hε (hGε ε hε) hcont hB k i
  exact tendsto_nhds_unique (hLHS.congr' hEq) hRHS

theorem convGradConv_coeff_of_holder_proof :
    type_of% @HRS.convGradConv_coeff_of_holder := by
  intro d s α hd hs0 hsd hα0 hα1 hα ρ hρ i
  obtain ⟨B, Λ, hB0, hΛ0, hB, hH⟩ := ch_hol_data hρ
  have e1 : ∀ (φ : Torus d → ℝ) (k : Lattice d),
      PDE.coeffOf φ k = ∫ x, Torus.mode (-k) x * (φ x : ℂ) :=
    fun φ k => KernelGrad.coeffOf_eq_integral φ k
  funext k
  rw [e1, ch_coeff_holder hd hs0 hsd hρ.1 hB hB0 hΛ0 hα0 hα hH k i]
  unfold PDE.gradRieszCoeff PDE.derivCoeff PDE.rieszMult
  rw [e1]
  ring

end HRS.MH.ConventionHolder
