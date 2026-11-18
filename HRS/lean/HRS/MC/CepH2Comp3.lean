import HRS.MC.CepH2Comp2

/-!
# CEPH2, the mollified measures `ν_v = u_v dx|_cell` and their narrow convergence
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The measure on the cell with density the mollified density. -/
def h2_molMeas (v : ℝ) (μ : Measure (Ch N)) : Measure (Ch N) :=
  ((volume : Measure (Ch N)).restrict (cep_cell N)).withDensity (fun x => ENNReal.ofReal (h2_mu v μ x))

theorem h2_molMeas_prob {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (h2_molMeas v μ) := by
  refine ⟨?_⟩
  unfold h2_molMeas
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h2_lintegral_cell_mu_one hv μ

theorem h2_molMeas_compl {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    h2_molMeas v μ (cep_cell N)ᶜ = 0 := by
  unfold h2_molMeas
  rw [withDensity_apply _ h2_cell_measurable.compl, Measure.restrict_restrict h2_cell_measurable.compl,
    compl_inter_self]
  simp

theorem h2_molMeas_inner {v : ℝ} (hv : 0 < v) {ψ : Ch N → ℝ} (hψ : Continuous ψ) {C : ℝ} (hC : ∀ z, |ψ z| ≤ C)
    (y : Ch N) :
    ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * ENNReal.ofReal (ψ x + C) =
      ENNReal.ofReal ((∫ z, h2_g v z * ψ (z + y)) + C) := by
  have hgi := h2_integrable_g (N := N) hv
  have hnn : ∀ z : Ch N, 0 ≤ ψ (z + y) + C := fun z => by linarith [(abs_le.1 (hC (z + y))).1]
  have hf : Integrable (fun z : Ch N => h2_g v z * (ψ (z + y) + C)) := by
    refine Integrable.mono' (hgi.mul_const (2 * C)) ?_ (ae_of_all _ fun z => ?_)
    · exact ((h2_continuous_g _).mul ((hψ.comp (continuous_id.add continuous_const)).add
        continuous_const)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h2_g_pos hv z).le (hnn z))]
      refine mul_le_mul_of_nonneg_left ?_ (h2_g_pos hv z).le
      linarith [(abs_le.1 (hC (z + y))).2]
  have hψi : Integrable (fun z : Ch N => h2_g v z * ψ (z + y)) := by
    refine Integrable.mono' (hgi.mul_const C) ?_ (ae_of_all _ fun z => ?_)
    · exact ((h2_continuous_g _).mul (hψ.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (h2_g_pos hv z)]
      exact mul_le_mul_of_nonneg_left (hC _) (h2_g_pos hv z).le
  rw [h2_lintegral_gauss_shift (v := v) (fun x => ENNReal.ofReal (ψ x + C)) y]
  have e : ∀ z : Ch N, ENNReal.ofReal (h2_g v z) * ENNReal.ofReal (ψ (z + y) + C) =
      ENNReal.ofReal (h2_g v z * (ψ (z + y) + C)) := fun z =>
    (ENNReal.ofReal_mul (h2_g_pos hv z).le).symm
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun z => mul_nonneg (h2_g_pos hv z).le (hnn z))]
  congr 1
  have : ∀ z : Ch N, h2_g v z * (ψ (z + y) + C) = h2_g v z * ψ (z + y) + C * h2_g v z := fun z => by ring
  simp_rw [this]
  rw [integral_add hψi (hgi.const_mul C), integral_const_mul, h2_g_integral hv, mul_one]

/-- Narrow convergence of the mollified measures. -/
theorem h2_molMeas_tendsto (μ : Measure (Ch N)) [IsProbabilityMeasure μ] {v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (hv0 : Tendsto v atTop (𝓝 0)) {ψ : Ch N → ℝ} (hψ : Continuous ψ) (hper : ∀ z, ψ (z + cep_diag N) = ψ z)
    {C : ℝ} (hC : ∀ z, |ψ z| ≤ C) :
    Tendsto (fun n => ∫ z, ψ z ∂(h2_molMeas (v n) μ)) atTop (𝓝 (∫ z, ψ z ∂μ)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hnn : ∀ z : Ch N, 0 ≤ ψ z + C := fun z => by linarith [(abs_le.1 (hC z)).1]
  set w : Ch N → ℝ≥0∞ := fun x => ENNReal.ofReal (ψ x + C) with hw
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp (hψ.add continuous_const).measurable
  have hwper : ∀ x, w (x + cep_diag N) = w x := fun x => by simp only [hw, hper]
  -- the lintegral against the mollified measure
  have h1 : ∀ n, ∫⁻ x, w x ∂(h2_molMeas (v n) μ) = ∫⁻ y, ENNReal.ofReal ((∫ z, h2_g (v n) z * ψ (z + y)) + C) ∂μ := by
    intro n
    unfold h2_molMeas
    rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun x => ENNReal.ofReal (h2_mu (v n) μ x))
      (ENNReal.measurable_ofReal.comp (h2_continuous_mu (hv n) μ).measurable) hwm]
    simp only [Pi.mul_apply]
    rw [h2_lintegral_cell_mu_weight (hv n) μ hwm hwper]
    refine lintegral_congr fun y => ?_
    exact h2_molMeas_inner (hv n) hψ hC y
  -- convergence of the lintegrals
  have h2 : Tendsto (fun n => ∫⁻ y, ENNReal.ofReal ((∫ z, h2_g (v n) z * ψ (z + y)) + C) ∂μ) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (ψ y + C) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (2 * C)) ?_ ?_ ?_ ?_
    · intro n
      refine ENNReal.measurable_ofReal.comp ?_
      have : Measurable fun y => ∫ z, h2_g (v n) z * ψ (z + y) := by
        have hc : Continuous (Function.uncurry fun (y : Ch N) (z : Ch N) => h2_g (v n) z * ψ (z + y)) :=
          ((h2_continuous_g _).comp continuous_snd).mul (hψ.comp (continuous_snd.add continuous_fst))
        exact (hc.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
      exact this.add_const C
    · intro n
      refine Eventually.of_forall fun y => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hgi := h2_integrable_g (N := N) (hv n)
      have : |∫ z, h2_g (v n) z * ψ (z + y)| ≤ C := by
        calc |∫ z, h2_g (v n) z * ψ (z + y)| ≤ ∫ z, |h2_g (v n) z * ψ (z + y)| := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => h2_g (v n) z * ψ (z + y))
          _ ≤ ∫ z, h2_g (v n) z * C := by
              refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) (hgi.mul_const C)
                (ae_of_all _ fun z => ?_)
              show |h2_g (v n) z * ψ (z + y)| ≤ _
              rw [abs_mul, abs_of_pos (h2_g_pos (hv n) z)]
              exact mul_le_mul_of_nonneg_left (hC _) (h2_g_pos (hv n) z).le
          _ = C := by rw [integral_mul_const, h2_g_integral (hv n), one_mul]
      linarith [(abs_le.1 this).2]
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
    · refine Eventually.of_forall fun y => ?_
      exact (ENNReal.continuous_ofReal.tendsto _).comp
        (((h2_mollify_tendsto hψ hC y hv hv0)).add_const C)
  -- conversion to real integrals
  have hconv : ∀ (ρ : Measure (Ch N)) [IsProbabilityMeasure ρ], ∫⁻ x, w x ∂ρ = ENNReal.ofReal (∫ z, ψ z ∂ρ + C) := by
    intro ρ _
    have hi : Integrable ψ ρ := Integrable.of_bound hψ.aestronglyMeasurable C
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)
    have := ofReal_integral_eq_lintegral_ofReal (f := fun x => ψ x + C) (hi.add (integrable_const C))
      (ae_of_all _ hnn)
    simp only [hw]
    rw [← this, integral_add hi (integrable_const C)]
    simp
  haveI : ∀ n, IsProbabilityMeasure (h2_molMeas (v n) μ) := fun n => h2_molMeas_prob (hv n) μ
  have h3 : Tendsto (fun n => ENNReal.ofReal (∫ z, ψ z ∂(h2_molMeas (v n) μ) + C)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, ψ z ∂μ + C))) := by
    have := h2
    simp_rw [← h1, hconv] at this
    rwa [hconv μ] at this
  have h4 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h3
  have e : ∀ (ρ : Measure (Ch N)) [IsProbabilityMeasure ρ], (ENNReal.ofReal (∫ z, ψ z ∂ρ + C)).toReal = ∫ z, ψ z ∂ρ + C := by
    intro ρ _
    rw [ENNReal.toReal_ofReal]
    have hi : Integrable ψ ρ := Integrable.of_bound hψ.aestronglyMeasurable C
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC z)
    have := integral_mono (integrable_const (-C)) hi (fun z => (abs_le.1 (hC z)).1)
    simp at this
    linarith
  simp only [Function.comp_def, e] at h4
  simpa using h4.sub_const C

end HRS.MC.CepH2
