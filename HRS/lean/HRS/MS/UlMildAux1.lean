import HRS.MS.UlOuC
import HRS.MS.UlNl
import HRS.MS.UlTailTie
import HRS.MS.LcMarkovAux2

/-!
# UL-4, part 1 (UlMildAux1): semigroup law, time continuity, uniform continuity and the integral Minkowski bound

(docstring: see `UlMildAux3.lean`.)  Helper lemmas carry the prefix `ul4_`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff ComplexConjugate FourierTransform RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.Ul
open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UlocMW
open HRS.MS.Lc HRS.MD.EQLawPath

variable {d : ℕ}

/-- measurability of `ouSg τ h` for a continuous `h` -/
theorem ul4_ouSg_measurable (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {h : Euc d → ℝ}
    (hh : Continuous h) : Measurable (ouSg Q ν τ h) := by
  have := (StronglyMeasurable.integral_prod_right (f := fun (x y : Euc d) => h (ouExp Q τ x + y))
    (ν := ouLaw Q ν τ) (hh.measurable.comp (((ouExp Q τ).continuous.measurable.comp
      measurable_fst).add measurable_snd)).stronglyMeasurable).measurable
  exact this

/-- `|ouSg τ h| ≤ B` if `|h| ≤ B` -/
theorem ul4_ouSg_abs_le (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) {h : Euc d → ℝ} {B : ℝ}
    (hB : ∀ y, |h y| ≤ B) (x : Euc d) : |ouSg Q ν τ h x| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := ouLaw Q ν τ)
    (f := fun y => h (ouExp Q τ x + y)) (C := B)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB _)
  simpa [ouSg, Real.norm_eq_abs] using this

/-- the semigroup law `P_{a+b} h = P_a P_b h` for bounded continuous `h` -/
theorem ul4_semigroup (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 ≤ ν) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {h : Euc d → ℝ} (hh : Continuous h) {B : ℝ} (hB : ∀ y, |h y| ≤ B) (x : Euc d) :
    ouSg Q ν (a + b) h x = ouSg Q ν a (ouSg Q ν b h) x := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  have := hP
  have hνc : Continuous fun _ : ℝ => ν := continuous_const
  have h1 := lcSg_ou Q hW hν le_rfl (add_nonneg ha hb) hh.measurable x
  have h2 := lc_markov hW hνc (fun _ => hν) (ul2_lcHyp_zero Q) hh (M := B)
    (fun y => by simpa [Real.norm_eq_abs] using hB y) (r := 0) (v := a) (t := 0 + (a + b))
    le_rfl ha (by linarith) x
  have h3 : lcSg P W (fun _ => ν) Q (fun _ => (0 : Euc d)) (fun _ _ => (0 : Euc d)) a (0 + (a + b)) h =
      ouSg Q ν b h := by
    funext y
    have := lcSg_ou Q hW hν ha hb hh.measurable y
    rwa [show 0 + (a + b) = a + b by ring]
  have h4 := lcSg_ou Q hW hν le_rfl ha (ul4_ouSg_measurable Q ν b hh) x
  rw [zero_add] at h4
  rw [← h1, h2, h3, h4]

/-- a `C²` function with bounded derivatives is Lipschitz -/
theorem ul4_lip_of_cb {h : Euc d → ℝ} (hf : ContDiff ℝ 1 h) {M : ℝ}
    (hM : ∀ y, ‖fderiv ℝ h y‖ ≤ M) (a b : Euc d) : |h a - h b| ≤ M * ‖a - b‖ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have := (lipschitzWith_of_nnnorm_fderiv_le (f := h) (C := ⟨M, hM0⟩)
    (hf.differentiable one_ne_zero) (fun x => by exact_mod_cast hM x)).dist_le_mul a b
  rw [Real.dist_eq, dist_eq_norm] at this
  exact this

/-- continuity in time of the OU semigroup applied to a fixed `C_b^2` function at a fixed point -/
theorem ul4_ouSg_cont_time (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {h : Euc d → ℝ}
    (hf : ContDiff ℝ 2 h) {M : ℝ} (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) (x : Euc d) :
    ContinuousOn (fun s => ouSg Q ν s h x) (Set.Ici 0) := by
  intro s hs
  rcases (show (0 : ℝ) ≤ s from hs).eq_or_lt with h0 | hpos
  · subst h0
    have hh1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M := fun y => by
      have := hM 1 (by norm_num) y
      rwa [norm_iteratedFDeriv_one] at this
    have hh0 : ∀ y, |h y| ≤ M := fun y => by
      have := hM 0 (by norm_num) y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    obtain ⟨c, hc0, hc⟩ := ul3C_m1 Q hν 1
    have hbound : ∀ s' ∈ Set.Icc (0 : ℝ) 1, |ouSg Q ν s' h x - h x| ≤
        M * (‖ouExp Q s' x - x‖ + c * Real.sqrt s') := by
      intro s' hs'
      have hi : Integrable (fun y => h (ouExp Q s' x + y)) (ouLaw Q ν s') :=
        Integrable.of_bound (hf.continuous.measurable.comp
          (measurable_const.add measurable_id)).aestronglyMeasurable M
          (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hh0 _)
      have hnorm : Integrable (fun y : Euc d => ‖y‖) (ouLaw Q ν s') :=
        (IsGaussian.integrable_id (μ := ouLaw Q ν s')).norm
      have e : ouSg Q ν s' h x - h x = ∫ y, (h (ouExp Q s' x + y) - h x) ∂(ouLaw Q ν s') := by
        rw [integral_sub hi (integrable_const _)]; simp [ouSg]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hh0 0)
      rw [e, ← Real.norm_eq_abs]
      calc ‖∫ y, (h (ouExp Q s' x + y) - h x) ∂(ouLaw Q ν s')‖
          ≤ ∫ y, M * (‖ouExp Q s' x - x‖ + ‖y‖) ∂(ouLaw Q ν s') := by
            refine norm_integral_le_of_norm_le ((integrable_const _).add hnorm |>.const_mul M)
              (Filter.Eventually.of_forall fun y => ?_)
            rw [Real.norm_eq_abs]
            refine (ul4_lip_of_cb (hf.of_le (by norm_num)) hh1 _ _).trans ?_
            gcongr
            calc ‖ouExp Q s' x + y - x‖ = ‖(ouExp Q s' x - x) + y‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
        _ = M * (‖ouExp Q s' x - x‖ + ∫ y, ‖y‖ ∂(ouLaw Q ν s')) := by
            rw [integral_const_mul, integral_add (integrable_const _) hnorm]; simp
        _ ≤ M * (‖ouExp Q s' x - x‖ + c * Real.sqrt s') := by
            gcongr
            exact hc s' hs'
    have h1 : Continuous fun s' : ℝ => ouExp Q s' x - x :=
      ((ul2_exp_cont Q).clm_apply continuous_const).sub continuous_const
    have h1' : Tendsto (fun s' : ℝ => ‖ouExp Q s' x - x‖) (𝓝[≥] 0) (𝓝 0) := by
      have := (h1.norm.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ici (0 : ℝ)))
      simpa [ouExp_zero] using this
    have h2 : Tendsto (fun s' : ℝ => c * Real.sqrt s') (𝓝[≥] 0) (𝓝 0) := by
      have hc' : Continuous fun s' : ℝ => c * Real.sqrt s' := continuous_const.mul Real.continuous_sqrt
      have := (hc'.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ici (0 : ℝ)))
      simpa using this
    have hg : Tendsto (fun s' : ℝ => M * (‖ouExp Q s' x - x‖ + c * Real.sqrt s')) (𝓝[≥] 0) (𝓝 0) := by
      simpa using (h1'.add h2).const_mul M
    have hs0 : ouSg Q ν 0 h x = h x := ouSg_zero Q hν.le h x
    show ContinuousWithinAt (fun s => ouSg Q ν s h x) (Set.Ici 0) 0
    rw [ContinuousWithinAt, hs0]
    refine tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hg)
    filter_upwards [Icc_mem_nhdsGE (zero_lt_one' ℝ)] with s' hs'
    rw [Real.norm_eq_abs]; exact hbound s' hs'
  · have := (ou_forward_hasDerivAt Q hν.le hf hM hpos x).continuousAt
    exact this.continuousWithinAt

/-! ### Averaging over a probability space of functions (generalised `ulocNormE_avg_le`) -/

section AvgGen

variable {Y : Type*} [MeasurableSpace Y]

/-- Fubini: the Fourier transform of the average is the average of the Fourier transforms -/
theorem ul4_fourier_avg (cz : Euc d → ℝ) (hc : Continuous cz) (hcs : HasCompactSupport cz)
    (H : Euc d → Y → ℝ) (hm : Measurable (Function.uncurry H)) (B : ℝ) (hB : ∀ x y, |H x y| ≤ B)
    (μ : Measure Y) [IsProbabilityMeasure μ] (ξ : Euc d) :
    𝓕 (fun x : Euc d => (((cz x * ∫ y, H x y ∂μ : ℝ)) : ℂ)) ξ =
      ∫ y, 𝓕 (fun x : Euc d => (((cz x * H x y : ℝ)) : ℂ)) ξ ∂μ := by
  simp only [Real.fourier_eq']
  set E : Euc d → ℂ := fun x => Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫) * Complex.I)) with hE
  have hEc : Continuous E := by
    rw [hE]; fun_prop
  have hEn : ∀ x, ‖E x‖ = 1 := fun x => by
    rw [hE]; exact Complex.norm_exp_ofReal_mul_I _
  have step1 : ∀ x : Euc d, E x • (((cz x * ∫ y, H x y ∂μ : ℝ) : ℂ)) =
      ∫ y, E x • (((cz x * H x y : ℝ) : ℂ)) ∂μ := by
    intro x
    rw [integral_smul]
    congr 1
    rw [integral_complex_ofReal, integral_const_mul]
  have hint : Integrable (Function.uncurry fun (x : Euc d) (y : Y) => E x • (((cz x * H x y : ℝ) : ℂ)))
      (volume.prod μ) := by
    have hbd : Integrable (fun p : Euc d × Y => B * ‖cz p.1‖) (volume.prod μ) :=
      (((hc.integrable_of_hasCompactSupport hcs).norm).const_mul B).comp_fst μ
    refine Integrable.mono' hbd ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact (hEc.measurable.comp measurable_fst).smul (Complex.measurable_ofReal.comp
        ((hc.measurable.comp measurable_fst).mul hm))
    · have h1 := hB p.1 p.2
      show ‖E p.1 • (((cz p.1 * H p.1 p.2 : ℝ) : ℂ))‖ ≤ B * ‖cz p.1‖
      calc ‖E p.1 • (((cz p.1 * H p.1 p.2 : ℝ) : ℂ))‖ = |cz p.1| * |H p.1 p.2| := by
            rw [norm_smul, hEn, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        _ ≤ B * ‖cz p.1‖ := by
            rw [Real.norm_eq_abs]; nlinarith [abs_nonneg (cz p.1)]
  refine (integral_congr_ae (Filter.Eventually.of_forall step1)).trans ?_
  exact integral_integral_swap hint

/-- **Averaging of a family.**  If `H x y` is jointly measurable and bounded and every member
`H · y` has `ulocNormE ≤ U`, then so has the average over a probability measure. -/
theorem ul4_avg_gen (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (μ : Measure Y)
    [IsProbabilityMeasure μ] (H : Euc d → Y → ℝ) (hm : Measurable (Function.uncurry H)) (B : ℝ)
    (hB : ∀ x y, |H x y| ≤ B) (U : ℝ≥0∞) (hU : ∀ y, ulocNormE m χ (fun x => H x y) ≤ U) :
    ulocNormE m χ (fun x => ∫ y, H x y ∂μ) ≤ U := by
  refine iSup_le fun z => ?_
  set cz : Euc d → ℝ := fun x => χ (x - z) with hcz
  have hcc : Continuous cz := hχ.1.continuous.comp (continuous_id.sub continuous_const)
  have hcs : HasCompactSupport cz := hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  set a : Euc d → ℝ := fun x => ∫ y, H x y ∂μ with ha
  have ha_meas : Measurable a :=
    (StronglyMeasurable.integral_prod_right (f := fun (x : Euc d) (y : Y) => H x y) (ν := μ)
      hm.stronglyMeasurable).measurable
  have haB : ∀ x, |a x| ≤ B := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => H x y) (C := B)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB x y)
    simpa [ha, Real.norm_eq_abs] using this
  obtain ⟨hgL2, hgL1⟩ := ul0_memLp_integrable_mul hcc hcs ha_meas.aestronglyMeasurable B haB
  have hHy : ∀ y, Measurable (fun x => H x y) := fun y => hm.comp (measurable_id.prodMk measurable_const)
  have hφ : ∀ y, MemLp (fun x => cz x * H x y) 2 volume ∧ Integrable (fun x => cz x * H x y) volume :=
    fun y => ul0_memLp_integrable_mul hcc hcs (hHy y).aestronglyMeasurable B (fun x => hB x y)
  set Φ : Euc d → Y → ℂ := fun ξ y => 𝓕 (fun x : Euc d => (((cz x * H x y : ℝ)) : ℂ)) ξ with hΦ
  have hΦm : Measurable (fun p : Euc d × Y => Φ p.1 p.2) := by
    have : (fun p : Euc d × Y => Φ p.1 p.2) = fun p => ∫ x : Euc d,
        Complex.exp ((↑(-2 * Real.pi * ⟪x, p.1⟫) * Complex.I)) • (((cz x * H x p.2 : ℝ)) : ℂ) := by
      funext p; simp only [hΦ, Real.fourier_eq']
    rw [this]
    refine StronglyMeasurable.measurable ?_
    refine StronglyMeasurable.integral_prod_right (f := fun (p : Euc d × Y) (x : Euc d) =>
      Complex.exp ((↑(-2 * Real.pi * ⟪x, p.1⟫) * Complex.I)) • (((cz x * H x p.2 : ℝ)) : ℂ)) ?_
    refine Measurable.stronglyMeasurable ?_
    have h1 : Continuous (fun r : Euc d × Euc d =>
        Complex.exp ((↑(-2 * Real.pi * ⟪r.2, r.1⟫) * Complex.I))) := by fun_prop
    have hproj : Measurable (fun q : (Euc d × Y) × Euc d => (q.1.1, q.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h1m : Measurable (fun q : (Euc d × Y) × Euc d =>
        Complex.exp ((↑(-2 * Real.pi * ⟪q.2, q.1.1⟫) * Complex.I))) :=
      by have := h1.measurable.comp hproj; exact this
    have hc2 : Measurable (fun q : (Euc d × Y) × Euc d => cz q.2) := hcc.measurable.comp measurable_snd
    have hq : Measurable (fun q : (Euc d × Y) × Euc d => H q.2 q.1.2) :=
      hm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    have hr : Measurable (fun q : (Euc d × Y) × Euc d => (((cz q.2 * H q.2 q.1.2 : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp (hc2.mul hq)
    exact h1m.smul hr
  have hΦe : Measurable (fun p : Euc d × Y => ‖Φ p.1 p.2‖ₑ) := hΦm.enorm
  have hCS : ∀ ξ : Euc d, ‖𝓕 (fun x : Euc d => (((cz x * a x : ℝ)) : ℂ)) ξ‖ₑ ^ 2 ≤
      ∫⁻ y, ‖Φ ξ y‖ₑ ^ 2 ∂μ := by
    intro ξ
    rw [ul4_fourier_avg cz hcc hcs H hm B hB μ ξ]
    have h1 := enorm_integral_le_lintegral_enorm (μ := μ) (fun y => Φ ξ y)
    have hmeas : Measurable (fun y => ‖Φ ξ y‖ₑ) :=
      (hΦe.comp (measurable_prodMk_left (x := ξ)) : Measurable ((fun p : Euc d × Y => ‖Φ p.1 p.2‖ₑ) ∘ Prod.mk ξ))
    have h2 := HRS.MS.SobMul.sobmul_cs μ (fun y => ‖Φ ξ y‖ₑ) hmeas.aemeasurable
    simp only [measure_univ, one_mul] at h2
    exact (pow_le_pow_left' h1 2).trans h2
  have hpiece : ∀ y, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖Φ ξ y‖ₑ ^ 2 =
      sobolevNormE (m : ℝ) (fun x => cz x * H x y) ^ 2 := by
    intro y
    rw [um_sobE_sq (hφ y).1]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 (hφ y).2 (hφ y).1] with ξ hξ
    rw [hξ, ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hbound : ∀ y, sobolevNormE (m : ℝ) (fun x => cz x * H x y) ≤ U := fun y =>
    (le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * H x y) z).trans (hU y)
  have hmeasW : Measurable (fun p : Euc d × Y => ENNReal.ofReal (wt p.1 ^ (m : ℝ)) * ‖Φ p.1 p.2‖ₑ ^ 2) :=
    (ENNReal.measurable_ofReal.comp ((continuous_wt_rpow (m : ℝ)).measurable.comp measurable_fst)).mul
      (hΦe.pow_const 2)
  have hga : (fun x => χ (x - z) * (fun x => ∫ y, H x y ∂μ) x) = fun x => cz x * a x := rfl
  rw [hga]
  have hmain : sobolevNormE (m : ℝ) (fun x => cz x * a x) ^ 2 ≤ U ^ 2 := by
    rw [um_sobE_sq hgL2]
    calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ) * ‖fourierL2 (fun x => cz x * a x) ξ‖ ^ 2)
        = ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖𝓕 (fun x : Euc d => (((cz x * a x : ℝ)) : ℂ)) ξ‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          filter_upwards [um_L1L2 hgL1 hgL2] with ξ hξ
          rw [hξ, ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _),
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ∫⁻ y, ‖Φ ξ y‖ₑ ^ 2 ∂μ := by
          refine lintegral_mono fun ξ => ?_
          gcongr
          exact hCS ξ
      _ = ∫⁻ ξ, ∫⁻ y, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖Φ ξ y‖ₑ ^ 2 ∂μ := by
          refine lintegral_congr fun ξ => ?_
          rw [lintegral_const_mul]
          exact (hΦe.comp (measurable_prodMk_left (x := ξ))).pow_const 2
      _ = ∫⁻ y, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ (m : ℝ)) * ‖Φ ξ y‖ₑ ^ 2 ∂volume ∂μ :=
          lintegral_lintegral_swap hmeasW.aemeasurable
      _ = ∫⁻ y, sobolevNormE (m : ℝ) (fun x => cz x * H x y) ^ 2 ∂μ :=
          lintegral_congr fun y => hpiece y
      _ ≤ ∫⁻ y, U ^ 2 ∂μ := lintegral_mono fun y => pow_le_pow_left' (hbound y) 2
      _ = U ^ 2 := by simp
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hmain

end AvgGen

/-! ### Time integrals with a singular weight -/

open Classical in
/-- **Minkowski for a weighted time integral.**  If `‖F σ‖_{H^m_uloc} ≤ a σ` for `σ ∈ (0,τ)` with `a`
integrable and bounded below by a positive constant, and `F` is jointly measurable and bounded, then
`‖∫_0^τ F σ dσ‖_{H^m_uloc} ≤ C ∫_0^τ a`. -/
theorem ul4_time_bound (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {τ : ℝ}, 0 < τ → ∀ (F : ℝ → Euc d → ℝ), Measurable (Function.uncurry F) →
      ∀ B : ℝ, (∀ σ ∈ Ioo 0 τ, ∀ x, |F σ x| ≤ B) → ∀ a : ℝ → ℝ, Measurable a → IntervalIntegrable a volume 0 τ →
      ∀ a0 : ℝ, 0 < a0 → (∀ σ ∈ Ioo 0 τ, a0 ≤ a σ) →
      (∀ σ ∈ Ioo 0 τ, ulocNormE m χ (F σ) ≤ ENNReal.ofReal (a σ)) →
      ulocNormE m χ (fun x => ∫ σ in (0 : ℝ)..τ, F σ x) ≤
        ENNReal.ofReal (C * ∫ σ in (0 : ℝ)..τ, a σ) := by
  obtain ⟨Cs, hCs0, hCs⟩ := ul3_scalar m χ
  refine ⟨Cs * Cs, by positivity, fun {τ} hτ F hF B hB a ha hai a0 ha0 hal hF' => ?_⟩
  have hint : IntegrableOn a (Ioo 0 τ) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1 hai).mono_set Ioo_subset_Ioc_self
  have hpos : ∀ σ ∈ Ioo 0 τ, 0 < a σ := fun σ hσ => ha0.trans_le (hal σ hσ)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (τ / 2) ⟨by positivity, by linarith⟩ 0)
  set ν : Measure ℝ := (volume.restrict (Ioo 0 τ)).withDensity (fun σ => ENNReal.ofReal (a σ)) with hν
  set Zr : ℝ := ∫ σ in Ioo 0 τ, a σ with hZr
  have hZnn : ∀ᵐ σ ∂(volume.restrict (Ioo 0 τ)), 0 ≤ a σ :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun σ hσ => (hpos σ hσ).le)
  have hνu : ν Set.univ = ENNReal.ofReal Zr := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hZr,
      ofReal_integral_eq_lintegral_ofReal hint hZnn]
  have hZpos : 0 < Zr := by
    have h1 : ∫ σ in Ioo 0 τ, a0 ≤ ∫ σ in Ioo 0 τ, a σ :=
      setIntegral_mono_on (integrableOn_const (by simp)) hint measurableSet_Ioo fun σ hσ => hal σ hσ
    have h2 : ∫ σ in Ioo 0 τ, a0 = a0 * τ := by
      rw [setIntegral_const]; simp [Real.volume_real_Ioo, hτ.le, mul_comm]
    have : 0 < a0 * τ := by positivity
    linarith
  haveI : IsFiniteMeasure ν := ⟨by rw [hνu]; exact ENNReal.ofReal_lt_top⟩
  set μ : Measure ℝ := (ν Set.univ)⁻¹ • ν with hμ
  haveI : IsProbabilityMeasure μ := ⟨by
    rw [hμ, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by rw [hνu]; simpa using hZpos) (by rw [hνu]; exact ENNReal.ofReal_ne_top)⟩
  set H : Euc d → ℝ → ℝ := fun x σ => if σ ∈ Ioo 0 τ then F σ x / a σ else 0 with hH
  have hHm : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = fun p : Euc d × ℝ => if p.2 ∈ Ioo 0 τ then F p.2 p.1 / a p.2 else 0 := by
      funext p; rfl
    rw [this]
    exact Measurable.ite (measurableSet_Ioo.preimage measurable_snd)
      ((hF.comp measurable_swap).div (ha.comp measurable_snd)) measurable_const
  have hHb : ∀ x σ, |H x σ| ≤ B / a0 := by
    intro x σ
    simp only [hH]
    split_ifs with hσ
    · rw [abs_div, abs_of_pos (hpos σ hσ)]
      exact (div_le_div₀ hB0 (hB σ hσ x) ha0 (hal σ hσ))
    · simp; positivity
  have hHn : ∀ σ, ulocNormE m χ (fun x => H x σ) ≤ ENNReal.ofReal Cs := by
    intro σ
    by_cases hσ : σ ∈ Ioo 0 τ
    · have e : (fun x => H x σ) = fun x => (a σ)⁻¹ * F σ x := by
        funext x; simp only [hH, if_pos hσ]; ring
      rw [e]
      refine (hCs _ _).trans ?_
      calc ENNReal.ofReal (Cs * |(a σ)⁻¹|) * ulocNormE m χ (F σ)
          ≤ ENNReal.ofReal (Cs * |(a σ)⁻¹|) * ENNReal.ofReal (a σ) := by gcongr; exact hF' σ hσ
        _ = ENNReal.ofReal (Cs * |(a σ)⁻¹| * a σ) := (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal Cs := by
            congr 1
            rw [abs_of_pos (inv_pos.2 (hpos σ hσ))]
            field_simp [(hpos σ hσ).ne']
    · have e : (fun x => H x σ) = fun x => (0 : ℝ) * F σ x := by
        funext x; simp only [hH, if_neg hσ, zero_mul]
      rw [e]
      refine (hCs _ _).trans ?_
      simp
  have havg := ul4_avg_gen m χ hχ μ H hHm (B / a0) hHb (ENNReal.ofReal Cs) hHn
  have hint_eq : ∀ x, ∫ σ in (0 : ℝ)..τ, F σ x = Zr * ∫ y, H x y ∂μ := by
    intro x
    rw [intervalIntegral.integral_of_le hτ.le, integral_Ioc_eq_integral_Ioo]
    have h1 : ∫ y, H x y ∂μ = ((ν Set.univ)⁻¹).toReal • ∫ y, H x y ∂ν := by
      rw [hμ, integral_smul_measure]
    have h2 : ∫ y, H x y ∂ν = ∫ σ in Ioo 0 τ, F σ x := by
      rw [hν, integral_withDensity_eq_integral_toReal_smul (f := fun σ => ENNReal.ofReal (a σ))
        (by exact ENNReal.measurable_ofReal.comp ha)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun measurableSet_Ioo fun σ hσ => ?_
      simp only [hH, if_pos hσ, ENNReal.toReal_ofReal (hpos σ hσ).le, smul_eq_mul]
      field_simp [(hpos σ hσ).ne']
    rw [h1, h2, hνu, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZpos.le, smul_eq_mul]
    field_simp
  have hZeq : ∫ σ in (0 : ℝ)..τ, a σ = Zr := by
    rw [intervalIntegral.integral_of_le hτ.le, integral_Ioc_eq_integral_Ioo]
  have hfun : (fun x => ∫ σ in (0 : ℝ)..τ, F σ x) = fun x => Zr * ∫ y, H x y ∂μ :=
    funext hint_eq
  rw [hfun, hZeq]
  refine (hCs _ _).trans ?_
  calc ENNReal.ofReal (Cs * |Zr|) * ulocNormE m χ (fun x => ∫ y, H x y ∂μ)
      ≤ ENNReal.ofReal (Cs * |Zr|) * ENNReal.ofReal Cs := by gcongr
    _ = ENNReal.ofReal (Cs * Cs * Zr) := by
        rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos hZpos]; congr 1; ring

/-! ### Localisation and derivatives in the uniformly local scale -/

/-- `‖u‖_{H^m_uloc} ≤ C ‖u‖_{H^m(ℝ^d)}` -/
theorem ul4_uloc_le_sob (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ, ulocNormE m χ u ≤ ENNReal.ofReal C * sobolevNormE (m : ℝ) u := by
  obtain ⟨C, hC, h⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) χ hχ.1 hχ.2.1
  exact ⟨C, hC, fun u => iSup_le fun z => h z u⟩

/-- one derivative on the Fourier side: `‖∂_j v‖_{H^n} ≤ ‖v‖_{H^{n+1}}` for `v ∈ C_c^1` -/
theorem ul4_sobE_deriv (n : ℕ) {v : Euc d → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    (j : Fin d) :
    sobolevNormE (n : ℝ) (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) ≤
      sobolevNormE ((n + 1 : ℕ) : ℝ) v := by
  set vj : Euc d → ℝ := fun x => fderiv ℝ v x (EuclideanSpace.single j 1) with hvj
  have hvc : Continuous v := hv.continuous
  have hv2 : MemLp v 2 volume := hvc.memLp_of_hasCompactSupport hc
  have hv1 : Integrable v volume := hvc.integrable_of_hasCompactSupport hc
  have hvjc : Continuous vj :=
    (continuous_eval_const (EuclideanSpace.single j (1 : ℝ))).comp (hv.continuous_fderiv one_ne_zero)
  have hvjcs : HasCompactSupport vj :=
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j (1 : ℝ))) (by simp)
  have hvj2 : MemLp vj 2 volume := hvjc.memLp_of_hasCompactSupport hvjcs
  have hvj1 : Integrable vj volume := hvjc.integrable_of_hasCompactSupport hvjcs
  set Fv : Euc d → ℂ := fun w => ((v w : ℝ) : ℂ) with hFv
  have hnorm : ∀ w, ‖𝓕 (fun x => ((vj x : ℝ) : ℂ)) w‖ = 2 * Real.pi * |w j| * ‖𝓕 Fv w‖ := by
    intro w
    have := ul0_fourier_partial_eq (m := 1) hv hc (n := 1) le_rfl (fun _ => j) w
    have e : partialDeriv (fun _ : Fin 1 => j) v = vj := by
      funext x
      simp [partialDeriv, hvj, iteratedFDeriv_one_apply]
    rw [e] at this
    simpa [pow_one, Finset.prod_const, mul_assoc] using this
  have hwt : ∀ ξ : Euc d, wt ξ = 1 + ∑ j : Fin d, (2 * Real.pi * |ξ j|) ^ 2 := by
    intro ξ
    unfold wt
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum]
    ring
  have hsq : sobolevNormE (n : ℝ) vj ^ 2 ≤ sobolevNormE ((n + 1 : ℕ) : ℝ) v ^ 2 := by
    rw [um_sobE_sq hv2, um_sobE_sq hvj2]
    have hA : ∀ s : ℝ, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 v ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖𝓕 Fv ξ‖ ^ 2) := by
      intro s
      refine lintegral_congr_ae ?_
      filter_upwards [um_L1L2 hv1 hv2] with ξ hξ
      rw [hξ]
    rw [hA]
    refine lintegral_mono_ae ?_
    filter_upwards [um_L1L2 hvj1 hvj2] with ξ hξ
    rw [hξ, hnorm ξ]
    apply ENNReal.ofReal_le_ofReal
    have h1 : wt ξ ^ (((n + 1 : ℕ) : ℝ)) = wt ξ ^ (n : ℝ) * wt ξ := by
      rw [Nat.cast_succ, Real.rpow_add (wt_pos ξ), Real.rpow_one]
    have h2 : (2 * Real.pi * |ξ j|) ^ 2 ≤ wt ξ := by
      rw [hwt ξ]
      have := Finset.single_le_sum (f := fun i : Fin d => (2 * Real.pi * |ξ i|) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      linarith
    rw [h1]
    have h3 := Real.rpow_nonneg (wt_pos ξ).le (n : ℝ)
    calc wt ξ ^ (n : ℝ) * (2 * Real.pi * |ξ j| * ‖𝓕 Fv ξ‖) ^ 2
        = wt ξ ^ (n : ℝ) * ((2 * Real.pi * |ξ j|) ^ 2 * ‖𝓕 Fv ξ‖ ^ 2) := by ring
      _ ≤ wt ξ ^ (n : ℝ) * (wt ξ * ‖𝓕 Fv ξ‖ ^ 2) := by gcongr
      _ = _ := by ring
  exact (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).1 hsq

/-- `ulocNormE` is monotone in the order -/
theorem ul4_uloc_mono {n n' : ℕ} (h : n ≤ n') (χ u : Euc d → ℝ) :
    ulocNormE n χ u ≤ ulocNormE n' χ u :=
  iSup_mono fun z => ul0_sobE_mono (by exact_mod_cast h) _

/-- **a derivative costs one order**: `‖∂_j u‖_{H^n_uloc} ≤ C ‖u‖_{H^{n+1}_uloc}` for `u ∈ C¹`. -/
theorem ul4_deriv_uloc (n : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ, ContDiff ℝ 1 u → ∀ j : Fin d,
      ulocNormE n χ (fun x => fderiv ℝ u x (EuclideanSpace.single j 1)) ≤
        ENNReal.ofReal C * ulocNormE (n + 1) χ u := by
  have hcut : ∀ j : Fin d, ∃ C : ℝ, 0 < C ∧ ∀ (z : Euc d) (u : Euc d → ℝ),
      sobolevNormE (n : ℝ) (fun x => -(fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ))) * u x) ≤
        ENNReal.ofReal C * ulocNormE n χ u := fun j =>
    ul3_cutoff_change n χ hχ (fun x => -(fderiv ℝ χ x (EuclideanSpace.single j (1 : ℝ))))
      (ul3_cutoff_deriv hχ j).1.neg (ul3_cutoff_deriv hχ j).2.neg
  choose Cj hCj0 hCj using hcut
  have hsum0 : 0 ≤ ∑ j, Cj j := Finset.sum_nonneg fun j _ => (hCj0 j).le
  refine ⟨1 + ∑ j, Cj j, by positivity, fun u hu j => ?_⟩
  refine iSup_le fun z => ?_
  set χz : Euc d → ℝ := fun x => χ (x - z) with hχz
  have hχzs : ContDiff ℝ ∞ χz := hχ.1.comp (contDiff_id.sub contDiff_const)
  have hχzc : HasCompactSupport χz := hχ.2.1.comp_homeomorph (Homeomorph.subRight z)
  set v : Euc d → ℝ := fun x => χz x * u x with hv
  have hv1 : ContDiff ℝ 1 v := (hχzs.of_le (by exact_mod_cast le_top)).mul hu
  have hvc : HasCompactSupport v := hχzc.mul_right
  have hvd : ∀ x : Euc d, fderiv ℝ v x (EuclideanSpace.single j 1) =
      fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ)) * u x +
        χz x * fderiv ℝ u x (EuclideanSpace.single j 1) := by
    intro x
    have h1 : HasFDerivAt χz (fderiv ℝ χ (x - z)) x := by
      have := (hχ.1.differentiable (by simp) (x - z)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z)
      exact this
    have h2 : HasFDerivAt u (fderiv ℝ u x) x := ((hu.differentiable one_ne_zero) x).hasFDerivAt
    have h3 : fderiv ℝ (fun x => χz x * u x) x = χz x • fderiv ℝ u x + u x • fderiv ℝ χ (x - z) :=
      (h1.mul h2).fderiv
    have e : v = fun x => χz x * u x := rfl
    rw [e, h3]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have e : (fun x => χ (x - z) * fderiv ℝ u x (EuclideanSpace.single j 1)) = fun x =>
      fderiv ℝ v x (EuclideanSpace.single j 1) +
        -(fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ))) * u x := by
    funext x; rw [hvd x]; ring
  rw [e]
  refine (HRS.MS.UlocCut.uc_tri _ _ _).trans ?_
  have t1 : sobolevNormE (n : ℝ) (fun x => fderiv ℝ v x (EuclideanSpace.single j 1)) ≤
      ulocNormE (n + 1) χ u :=
    (ul4_sobE_deriv n hv1 hvc j).trans
      (le_iSup (fun z : Euc d => sobolevNormE ((n + 1 : ℕ) : ℝ) fun x => χ (x - z) * u x) z)
  have t2 : sobolevNormE (n : ℝ) (fun x => -(fderiv ℝ χ (x - z) (EuclideanSpace.single j (1 : ℝ))) * u x) ≤
      ENNReal.ofReal (Cj j) * ulocNormE (n + 1) χ u :=
    (hCj j z u).trans (mul_le_mul' le_rfl (ul4_uloc_mono (Nat.le_succ n) χ u))
  have hle : Cj j ≤ ∑ j, Cj j :=
    Finset.single_le_sum (f := Cj) (fun j _ => (hCj0 j).le) (Finset.mem_univ j)
  calc _ ≤ ulocNormE (n + 1) χ u + ENNReal.ofReal (Cj j) * ulocNormE (n + 1) χ u := add_le_add t1 t2
    _ = ENNReal.ofReal (1 + Cj j) * ulocNormE (n + 1) χ u := by
        rw [ENNReal.ofReal_add zero_le_one (hCj0 j).le, ENNReal.ofReal_one, add_mul, one_mul]
    _ ≤ ENNReal.ofReal (1 + ∑ j, Cj j) * ulocNormE (n + 1) χ u := by
        gcongr

end HRS.MS.Ul
