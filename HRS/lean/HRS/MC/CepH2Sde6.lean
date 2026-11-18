import HRS.MC.CepH2Sde5

/-!
# CEPH2, S2b (part 3): transverse second moments along the flow (`cepH2_moment_flow`)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **S2b**. -/
theorem cepH2_moment_flow_proof [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) {θ : ℝ} (hθ : 0 < θ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * θ)) (fun z => -(gradient U z)) z₀ Z)
    (hm0 : ∫⁻ ω, ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) ∂P < ⊤) (T : ℝ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∫⁻ ω, ENNReal.ofReal (‖h2_perp (Z t ω)‖ ^ 2) ∂P ≤ M := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := h2_grad_growth hUper hK
  set σ' := Real.sqrt (2 * θ) with hσ'
  have hσ0 : 0 ≤ σ' := Real.sqrt_nonneg _
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hB : Continuous (fun z : Ch N => -(gradient U z)) := (h2_continuous_gradient hU1).neg
  have hBb : ∀ z, ‖-(gradient U z)‖ ≤ a + b * ‖h2_perp z‖ := fun z => by
    rw [norm_neg]; exact hab z
  have hZc : ∀ ω, Continuous fun t => Z t ω := hZ.1
  have hz0m : Measurable z₀ := hz₀.mono (ℱ.le 0) le_rfl
  set T' : ℝ := max T 0 + 1 with hT'
  have hT'0 : 0 < T' := by rw [hT']; linarith [le_max_right T 0]
  have hTT : ∀ t ∈ Icc (0 : ℝ) T, t ∈ Icc (0 : ℝ) T' := fun t ht =>
    ⟨ht.1, ht.2.trans (by rw [hT']; linarith [le_max_left T 0])⟩
  -- the pathwise inequality
  have hpath : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T,
      ‖h2_perp (Z t ω)‖ ^ 2 ≤ 6 * Real.exp (b * T') ^ 2 * ‖h2_perp (z₀ ω)‖ ^ 2 +
        6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2 +
        6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T') * (∫ s in (0 : ℝ)..T', h2_q W' s ω) +
        2 * σ' ^ 2 * h2_q W' t ω := by
    filter_upwards [hZ.2.2] with ω hω t ht
    have hn0 : cep_noise π W' 0 ω = 0 := by
      ext k; simp [cep_noise, hW'.zero]
    have h0 := hω 0 le_rfl
    rw [intervalIntegral.integral_same, hn0, smul_zero, add_zero, add_zero] at h0
    have hZeq : ∀ t : ℝ, 0 ≤ t → Z t ω = Z 0 ω + (∫ s in Icc (0 : ℝ) t, -(gradient U (Z s ω))) +
        σ' • cep_noise π W' t ω := by
      intro t ht
      rw [h0, hω t ht, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    have := h2_pathwise_sq (hZc ω) (h2_continuous_noise hW'.cont ω) hσ0 ha hb hB hBb hZeq hT'0
      (h2_continuous_q hW'.cont ω) (fun s => h2_noise_sq π W' s ω) t (hTT t ht)
    rw [h0] at this
    exact this
  -- measurability
  have hqm : ∀ s, Measurable (h2_q W' s) := h2_measurable_q hW'
  have hQm : Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω) :=
    (ENNReal.measurable_ofReal.comp ((h2_measurable_q_uncurry hW').comp measurable_swap)).lintegral_prod_right'
  have hQeq : ∀ ω, ENNReal.ofReal (∫ s in (0 : ℝ)..T', h2_q W' s ω) =
      ∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω) := by
    intro ω
    rw [intervalIntegral.integral_of_le hT'0.le, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      ((h2_continuous_q hW'.cont ω).integrableOn_Icc)
      (ae_of_all _ fun s => Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hQint : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω)) ∂P ≤
      ENNReal.ofReal (N * T') * ENNReal.ofReal T' := by
    rw [lintegral_lintegral_swap]
    · calc ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ ω, ENNReal.ofReal (h2_q W' s ω) ∂P
          ≤ ∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (N * T') := by
            refine setLIntegral_mono measurable_const fun s hs => ?_
            rw [h2_lintegral_q hW' hs.1]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs.2 (Nat.cast_nonneg _))
        _ = ENNReal.ofReal (N * T') * ENNReal.ofReal T' := by
            rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    · exact ((ENNReal.measurable_ofReal.comp ((h2_measurable_q_uncurry hW').comp measurable_swap)).aemeasurable)
  refine ⟨ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) * ∫⁻ ω, ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) ∂P +
    ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2) +
    ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T')) *
      (ENNReal.ofReal (N * T') * ENNReal.ofReal T') +
    ENNReal.ofReal (2 * σ' ^ 2) * ENNReal.ofReal (N * T'), ?_, fun t ht => ?_⟩
  · refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
      ENNReal.ofReal_lt_top hm0, ENNReal.ofReal_lt_top⟩, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)⟩,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  · have ht0 := ht.1
    calc ∫⁻ ω, ENNReal.ofReal (‖h2_perp (Z t ω)‖ ^ 2) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) * ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) +
            ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2) +
            ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T')) *
              (∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω)) +
            ENNReal.ofReal (2 * σ' ^ 2) * ENNReal.ofReal (h2_q W' t ω)) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpath] with ω hω
          refine (ENNReal.ofReal_le_ofReal (hω t ht)).trans (le_of_eq ?_)
          have q0 : 0 ≤ h2_q W' t ω := Finset.sum_nonneg fun k _ => sq_nonneg _
          have Q0 : 0 ≤ ∫ s in (0 : ℝ)..T', h2_q W' s ω := by
            refine intervalIntegral.integral_nonneg hT'0.le fun s _ => Finset.sum_nonneg fun k _ => sq_nonneg _
          have e1 : ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T') *
              ∫ s in (0 : ℝ)..T', h2_q W' s ω) = ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 *
              ((b * σ') ^ 2 * T')) * ENNReal.ofReal (∫ s in (0 : ℝ)..T', h2_q W' s ω) :=
            ENNReal.ofReal_mul (by positivity)
          have e2 : ENNReal.ofReal (2 * σ' ^ 2 * h2_q W' t ω) =
              ENNReal.ofReal (2 * σ' ^ 2) * ENNReal.ofReal (h2_q W' t ω) := ENNReal.ofReal_mul (by positivity)
          have e3 : ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ‖h2_perp (z₀ ω)‖ ^ 2) =
              ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) * ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) :=
            ENNReal.ofReal_mul (by positivity)
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), e1, e2, e3, hQeq ω]
        _ = ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) * ∫⁻ ω, ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) ∂P +
            ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2) +
            ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T')) *
              ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω)) ∂P +
            ENNReal.ofReal (2 * σ' ^ 2) * ENNReal.ofReal (N * t) := by
          have m1 : Measurable fun ω => ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) *
              ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) :=
            measurable_const.mul (ENNReal.measurable_ofReal.comp
              ((h2_continuous_perp.norm.measurable.comp hz0m).pow_const 2))
          have hmz : Measurable fun ω => ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) :=
            ENNReal.measurable_ofReal.comp ((h2_continuous_perp.norm.measurable.comp hz0m).pow_const 2)
          have hmq : Measurable fun ω => ENNReal.ofReal (h2_q W' t ω) :=
            ENNReal.measurable_ofReal.comp (hqm t)
          have m2 : Measurable fun _ : Ω => ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2) :=
            measurable_const
          have m3 : Measurable fun ω => ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T')) *
              (∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω)) := measurable_const.mul hQm
          have m4 : Measurable fun ω => ENNReal.ofReal (2 * σ' ^ 2) * ENNReal.ofReal (h2_q W' t ω) :=
            measurable_const.mul (ENNReal.measurable_ofReal.comp (hqm t))
          rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) *
              ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) +
              ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2) +
              ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * ((b * σ') ^ 2 * T')) *
              (∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal (h2_q W' s ω))) ((m1.add m2).add m3),
            lintegral_add_left (f := fun ω => ENNReal.ofReal (6 * Real.exp (b * T') ^ 2) *
              ENNReal.ofReal (‖h2_perp (z₀ ω)‖ ^ 2) +
              ENNReal.ofReal (6 * Real.exp (b * T') ^ 2 * (a * T') ^ 2)) (m1.add m2),
            lintegral_add_left m1, lintegral_const_mul _ hmz, lintegral_const, measure_univ,
            mul_one, lintegral_const_mul _ hQm, lintegral_const_mul _ hmq, h2_lintegral_q hW' ht0]
        _ ≤ _ := by
          refine add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hQint)) (mul_le_mul' le_rfl ?_)
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hTT t ht).2 (Nat.cast_nonneg _))

end HRS.MC.CepH2
