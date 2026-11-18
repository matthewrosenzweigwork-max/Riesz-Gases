import HRS.MC.CepH2Mom2

/-!
# CEPH2, S2a (part 3): `cepH2_moment_init`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_cylWeight_measurable {U : Ch N → ℝ} (hU : Continuous U) (θ : ℝ) :
    Measurable (cep_cylWeight θ U) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ((hU.neg).div_const θ)).measurable

theorem h2_cylRef_apply {U : Ch N → ℝ} (hU : Continuous U) (θ : ℝ) {s : Set (Ch N)} (hs : MeasurableSet s) :
    cep_cylRef θ U s = (cep_cylPartition θ U)⁻¹ * ∫⁻ z in s ∩ cep_cell N, cep_cylWeight θ U z := by
  unfold cep_cylRef
  rw [Measure.smul_apply, withDensity_apply _ hs, Measure.restrict_restrict hs, smul_eq_mul]

theorem h2_cylRef_prob {U : Ch N → ℝ} (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) : IsProbabilityMeasure (cep_cylRef θ U) := by
  refine ⟨?_⟩
  rw [h2_cylRef_apply hU θ MeasurableSet.univ, univ_inter]
  exact ENNReal.inv_mul_cancel (h2_partition_pos hU θ).ne' (h2_partition_lt_top hconf hθ).ne

theorem h2_cylRef_compl {U : Ch N → ℝ} (hU : Continuous U) (θ : ℝ) : cep_cylRef θ U (cep_cell N)ᶜ = 0 := by
  rw [h2_cylRef_apply hU θ h2_cell_measurable.compl, compl_inter_self]
  simp

/-- Lintegral against the Gibbs reference. -/
theorem h2_lintegral_cylRef {U : Ch N → ℝ} (hU : Continuous U) (θ : ℝ) {f : Ch N → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(cep_cylRef θ U) =
      (cep_cylPartition θ U)⁻¹ * ∫⁻ z in cep_cell N, cep_cylWeight θ U z * f z := by
  unfold cep_cylRef
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ (h2_cylWeight_measurable hU θ) hf]
  rfl

theorem h2_relEntropy_ne_top {U : Ch N → ℝ} {θ : ℝ} {μ : Measure (Ch N)}
    (h : cep_cylEntropy θ U μ < ⊤) : relEntropy μ (cep_cylRef θ U) ≠ ⊤ := by
  intro htop
  unfold cep_cylEntropy at h
  rw [htop] at h
  simp at h

/-- **S2a**. -/
theorem cepH2_moment_init_proof {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {μ : Measure (Ch N)} [IsProbabilityMeasure μ]
    (h : cep_cylEntropy θ U μ < ⊤) : μ (cep_cell N)ᶜ = 0 ∧ ∫⁻ z, ENNReal.ofReal (‖h2_perp z‖ ^ 2) ∂μ < ⊤ := by
  have hUc : Continuous U := hU.continuous
  haveI := h2_cylRef_prob hUc hconf hθ
  have hrel := h2_relEntropy_ne_top h
  unfold relEntropy at hrel
  have hac : μ ≪ cep_cylRef θ U := by
    by_contra hna
    exact hrel (klDiv_of_not_ac hna)
  refine ⟨hac (h2_cylRef_compl hUc θ), ?_⟩
  obtain ⟨κ₀, hκ₀, hfin⟩ := h2_weight_exp_finite hconf hθ
  set ref := cep_cylRef θ U with href
  set r : Ch N → ℝ := fun z => ‖h2_perp z‖ with hr
  have hrc : Continuous r := h2_continuous_perp.norm
  set g : Ch N → ℝ := fun z => κ₀ * r z ^ 2 with hg
  have hgc : Continuous g := continuous_const.mul (hrc.pow 2)
  have hg0 : ∀ z, 0 ≤ g z := fun z => by positivity
  -- exponential moment against the reference
  have hE : ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂ref < ⊤ := by
    rw [h2_lintegral_cylRef hUc θ (f := fun z => ENNReal.ofReal (Real.exp (g z)))
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hgc).measurable)]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (h2_partition_pos hUc θ)) ?_
    refine lt_of_le_of_lt (le_of_eq ?_) (hfin κ₀ hκ₀.le le_rfl)
    refine lintegral_congr fun z => ?_
    simp only [cep_cylWeight]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  set E : ℝ := (∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂ref).toReal with hEdef
  set k : ℝ := (klDiv μ ref).toReal with hk
  have hkfin : klDiv μ ref ≠ ⊤ := hrel
  -- truncations
  set φ : ℕ → Ch N → ℝ := fun n z => min (g z) n with hφ
  have hφc : ∀ n, Continuous (φ n) := fun n => hgc.min continuous_const
  have hφb : ∀ n z, |φ n z| ≤ n := fun n z => by
    rw [abs_of_nonneg (le_min (hg0 z) (Nat.cast_nonneg _))]; exact min_le_right _ _
  have hφint : ∀ n, Integrable (φ n) μ := fun n =>
    Integrable.of_bound (hφc n).aestronglyMeasurable n (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hφb n z)
  have hexpint : ∀ n, Integrable (fun z => Real.exp (φ n z)) ref := fun n =>
    Integrable.of_bound (Real.continuous_exp.comp (hφc n)).aestronglyMeasurable (Real.exp n)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (min_le_right _ _))
  have hEbd : ∀ n, ∫ z, Real.exp (φ n z) ∂ref ≤ E := by
    intro n
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => (Real.exp_pos _).le)
      (Real.continuous_exp.comp (hφc n)).aestronglyMeasurable]
    exact ENNReal.toReal_mono hE.ne (lintegral_mono fun z =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (min_le_left _ _)))
  have hkey : ∀ n, ∫⁻ z, ENNReal.ofReal (φ n z) ∂μ ≤ ENNReal.ofReal (k + Real.log E) := by
    intro n
    have hG := b15dv_gibbs μ ref (φ n) (hφint n) (hexpint n)
    have h1 : ∫ z, φ n z ∂μ - Real.log (∫ z, Real.exp (φ n z) ∂ref) ≤ k := by
      have := (ENNReal.ofReal_le_iff_le_toReal hkfin).1 hG
      exact this
    have hpos : 0 < ∫ z, Real.exp (φ n z) ∂ref :=
      integral_exp_pos (hexpint n)
    have h2 : Real.log (∫ z, Real.exp (φ n z) ∂ref) ≤ Real.log E := Real.log_le_log hpos (hEbd n)
    rw [← ofReal_integral_eq_lintegral_ofReal (hφint n)
      (ae_of_all _ fun z => le_min (hg0 z) (Nat.cast_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmono : Monotone fun n : ℕ => fun z => ENNReal.ofReal (φ n z) := by
    intro n m hnm z
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hnm))
  have hsup : ∀ z, (⨆ n : ℕ, ENNReal.ofReal (φ n z)) = ENNReal.ofReal (g z) := by
    intro z
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (g z)
    exact le_iSup_of_le n (le_of_eq (by simp only [hφ, min_eq_left hn]))
  have hgint : ∫⁻ z, ENNReal.ofReal (g z) ∂μ ≤ ENNReal.ofReal (k + Real.log E) := by
    have : ∫⁻ z, ENNReal.ofReal (g z) ∂μ = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (φ n z) ∂μ := by
      rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (φ n z))
        (fun n => ENNReal.measurable_ofReal.comp (hφc n).measurable) hmono]
      exact lintegral_congr fun z => (hsup z).symm
    rw [this]
    exact iSup_le hkey
  have hr2 : ∀ z, ENNReal.ofReal (r z ^ 2) = ENNReal.ofReal κ₀⁻¹ * ENNReal.ofReal (g z) := fun z => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hg]; field_simp
  simp_rw [show (fun z => ENNReal.ofReal (‖h2_perp z‖ ^ 2)) = fun z => ENNReal.ofReal (r z ^ 2) from rfl, hr2]
  rw [lintegral_const_mul (f := fun z => ENNReal.ofReal (g z)) _
    (ENNReal.measurable_ofReal.comp hgc.measurable)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hgint ENNReal.ofReal_lt_top)

end HRS.MC.CepH2
