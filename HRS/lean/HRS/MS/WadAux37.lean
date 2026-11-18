import HRS.MS.WadAux36
import HRS.MS.GapRefAux1

/-!
# S8.3, packet D7 (Route A), part 2: the thermal measure, moments, parametric integrals

`μ = HRS.Whole.withDensityReal ρβ` is a probability measure with all polynomial moments (Gaussian bounds, `s84_GaussReg`);
parametric integrals `r ↦ ∫ F(r,y) dμ(y)` are continuous / differentiable under domination.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_isProb {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := by
  have hint : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  refine ⟨?_⟩
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg), hρ.integral_one]
  simp

theorem s85_moment_integrable {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hg : s84_GaussReg ρ) {p : ℝ}
    (hp : 0 ≤ p) : Integrable (fun y : Euc d => (1 + ‖y‖) ^ p) (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨hdiff, C, c, hC0, hc, hb⟩ := hg
  obtain ⟨KB, hKB0, hKB⟩ := s84_poly_gauss (d := d) (p := p + ((d : ℝ) + 1)) (c := c) (by positivity) hc
  refine HRS.MS.Gap.gap1_integrable_wdr hρ.measurable hρ.nonneg ?_
  have hI : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) :=
    integrable_one_add_norm (by simp)
  refine Integrable.mono' (hI.const_mul (C * KB)) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (hdiff.continuous.mul (by fun_prop)).aestronglyMeasurable
  · have hy : 0 < 1 + ‖y‖ := by positivity
    have h1 := hKB y
    rw [Real.rpow_add hy] at h1
    have hq : 0 < (1 + ‖y‖) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hy _
    have h2 : Real.exp (-c * ‖y‖ ^ 2) * (1 + ‖y‖) ^ p ≤ KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
      rw [Real.rpow_neg hy.le, ← div_eq_mul_inv, le_div_iff₀ hq]
      nlinarith [h1]
    have hpos : 0 ≤ (1 + ‖y‖) ^ p := Real.rpow_nonneg hy.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
    calc |ρ y| * (1 + ‖y‖) ^ p ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (1 + ‖y‖) ^ p :=
          mul_le_mul_of_nonneg_right (hb y).1 hpos
      _ = C * (Real.exp (-c * ‖y‖ ^ 2) * (1 + ‖y‖) ^ p) := by ring
      _ ≤ C * (KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) := mul_le_mul_of_nonneg_left h2 hC0
      _ = C * KB * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by ring

theorem s85_jb_rpow_continuous (M : ℝ) : Continuous fun y : Euc d => jbracket y ^ M := by
  refine Continuous.rpow_const ?_ fun x => Or.inl (s83_jb_pos x).ne'
  unfold jbracket
  fun_prop

theorem s85_jb_integrable {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hg : s84_GaussReg ρ) {M : ℝ}
    (hM : 0 ≤ M) : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρ) := by
  refine Integrable.mono' (s85_moment_integrable hρ hg hM) (s85_jb_rpow_continuous M).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos y).le _)]
  exact Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM

theorem s85_integrable_of_bound {μ : Measure (Euc d)} {h : Euc d → ℝ} (hm : AEStronglyMeasurable h μ)
    {bd : Euc d → ℝ} (hb : Integrable bd μ) (hh : ∀ y, |h y| ≤ bd y) : Integrable h μ :=
  Integrable.mono' hb hm (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hh y)

theorem s85_abs_integral_le {μ : Measure (Euc d)} {h : Euc d → ℝ} {bd : Euc d → ℝ}
    (hb : Integrable bd μ) (hh : ∀ y, |h y| ≤ bd y) : |∫ y, h y ∂μ| ≤ ∫ y, bd y ∂μ := by
  have := norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact hh y)
  rwa [Real.norm_eq_abs] at this

/-- Continuity of a parametric integral under domination. -/
theorem s85_cont_param {μ : Measure (Euc d)} {t : ℝ} {F : ℝ → Euc d → ℝ} {bd : Euc d → ℝ}
    (hbd : Integrable bd μ) (hF : ContinuousOn (fun q : ℝ × Euc d => F q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hb : ∀ r ∈ Set.Icc 0 t, ∀ y, |F r y| ≤ bd y) :
    ContinuousOn (fun r => ∫ y, F r y ∂μ) (Set.Icc 0 t) := by
  refine continuousOn_of_dominated (bound := bd) (fun r hr => ?_) (fun r hr => ?_) hbd
    (Filter.Eventually.of_forall fun y => ?_)
  · have : Continuous fun y : Euc d => F r y :=
      (hF.comp_continuous (Continuous.prodMk continuous_const continuous_id)
        (fun y => ⟨hr, Set.mem_univ _⟩))
    exact this.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb r hr y
  · exact hF.comp (Continuous.prodMk continuous_id continuous_const).continuousOn
      (fun r hr => ⟨hr, Set.mem_univ _⟩)

/-- Differentiation of a parametric integral under domination. -/
theorem s85_deriv_param {μ : Measure (Euc d)} {t r : ℝ} (hr : r ∈ Set.Ioo 0 t) {F F' : ℝ → Euc d → ℝ}
    {bd bF : Euc d → ℝ} (hbd : Integrable bd μ) (hbF : Integrable bF μ)
    (hFc : ∀ r' ∈ Set.Ioo 0 t, Continuous (F r')) (hF'c : Continuous (F' r))
    (hFb : ∀ y, |F r y| ≤ bF y)
    (hb : ∀ r' ∈ Set.Ioo 0 t, ∀ y, |F' r' y| ≤ bd y)
    (hd : ∀ y, ∀ r' ∈ Set.Ioo 0 t, HasDerivAt (fun r'' => F r'' y) (F' r' y) r') :
    HasDerivAt (fun r' => ∫ y, F r' y ∂μ) (∫ y, F' r y ∂μ) r := by
  have hs : Set.Ioo 0 t ∈ 𝓝 r := Ioo_mem_nhds hr.1 hr.2
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (bound := bd) hs ?_ ?_
    hF'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y r' hr' => ?_) hbd
    (Filter.Eventually.of_forall fun y r' hr' => hd y r' hr')).2
  · exact Filter.eventually_of_mem hs fun r' hr' => (hFc r' hr').aestronglyMeasurable
  · exact s85_integrable_of_bound (hFc r hr).aestronglyMeasurable hbF hFb
  · rw [Real.norm_eq_abs]; exact hb r' hr' y

end HRS.MS.Wad
