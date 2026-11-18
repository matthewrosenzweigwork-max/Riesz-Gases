import HRS.MS.S21F_S18a

/-!
# S21F, packet R26-T3.S18: fixed-particle collision cutoff boundary estimate

With `ψ = dQ/dμ₀^{⊗N} ∈ L^8` (S05), `g = (1+∑‖X_k‖)² ∈ L^8(μ₀^{⊗N})` (Gaussian tails) and `ν(‖X_i-X_j‖ ≤ 2η) ≲ η^d` (part a), the change of measure
`‖X‖_{L¹(Q)} ≤ ‖ψ‖_{L^8} ‖X‖_{L^{8/7}(ν)}` (`s92_eLpNorm_withDensity_le_real`) for `X = g 1_{A_η}` and
`‖X‖_{L^{8/7}} ≤ ‖g‖_{L^8} ν(A_η)^{3/4}` give `η⁻¹ ∫_{A_η} g dQ ≲ η^{3d/4-1} → 0` since `d ≥ 2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_Lp_cut {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] {ψ : α → ℝ≥0∞}
    (hψ : Measurable ψ) {C8 : ℝ} (hC8 : 0 ≤ C8) (hψ8 : (∫⁻ x, ψ x ^ (8 : ℝ) ∂ν) ^ (1 / (8 : ℝ)) ≤ ENNReal.ofReal C8)
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgL : eLpNorm g (ENNReal.ofReal 8) ν < ⊤)
    (hint : Integrable g (ν.withDensity ψ)) {A : Set α} (hA : MeasurableSet A) :
    ∫ x in A, g x ∂(ν.withDensity ψ) ≤
      C8 * ((eLpNorm g (ENNReal.ofReal 8) ν).toReal * ((ν A).toReal) ^ (3 / 4 : ℝ)) := by
  set K := (eLpNorm g (ENNReal.ofReal 8) ν).toReal with hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hXm : Measurable (A.indicator g) := hg.indicator hA
  have hnu : ν A ≠ ⊤ := measure_ne_top _ _
  have hXb : eLpNorm (A.indicator g) (ENNReal.ofReal (1 * Real.conjExponent 8)) ν ≤
      ENNReal.ofReal (K * ((ν A).toReal) ^ (3 / 4 : ℝ)) := by
    have hce : Real.conjExponent 8 = 8 / 7 := by norm_num [Real.conjExponent]
    rw [hce, eLpNorm_indicator_eq_eLpNorm_restrict hA]
    have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict A) (f := g)
      (p := ENNReal.ofReal (1 * (8 / 7))) (q := ENNReal.ofReal 8)
      (ENNReal.ofReal_le_ofReal (by norm_num)) hg.aestronglyMeasurable
    refine h1.trans ?_
    have e1 : (1 / (ENNReal.ofReal (1 * (8 / 7))).toReal - 1 / (ENNReal.ofReal 8).toReal) = 3 / 4 := by
      rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]; norm_num
    rw [e1, Measure.restrict_apply_univ]
    calc eLpNorm g (ENNReal.ofReal 8) (ν.restrict A) * (ν A) ^ (3 / 4 : ℝ)
        ≤ eLpNorm g (ENNReal.ofReal 8) ν * (ν A) ^ (3 / 4 : ℝ) :=
          mul_le_mul_left (eLpNorm_mono_measure _ Measure.restrict_le_self) _
      _ = ENNReal.ofReal (K * ((ν A).toReal) ^ (3 / 4 : ℝ)) := by
          rw [ENNReal.ofReal_mul hK0, hK, ENNReal.ofReal_toReal hgL.ne,
            ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hnu]
  have hs := HRS.MS.R2Mt.s92_eLpNorm_withDensity_le_real ν hψ hXm (r := 1) (a := 8) one_pos (by norm_num)
    hC8 hψ8 hXb
  have hX1 : eLpNorm (A.indicator g) (ENNReal.ofReal 1) (ν.withDensity ψ) = ∫⁻ x, ENNReal.ofReal (A.indicator g x)
      ∂(ν.withDensity ψ) := by
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm (hXm.aestronglyMeasurable)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (by by_cases hx : x ∈ A <;> simp [hx, hg0])]
  rw [hX1] at hs
  have hI : ∫ x in A, g x ∂(ν.withDensity ψ) = ∫ x, A.indicator g x ∂(ν.withDensity ψ) :=
    (integral_indicator hA).symm
  have hI0 : 0 ≤ ∫ x, A.indicator g x ∂(ν.withDensity ψ) :=
    integral_nonneg fun x => by by_cases hx : x ∈ A <;> simp [hx, hg0]
  rw [hI]
  have hofr : ENNReal.ofReal (∫ x, A.indicator g x ∂(ν.withDensity ψ)) =
      ∫⁻ x, ENNReal.ofReal (A.indicator g x) ∂(ν.withDensity ψ) :=
    ofReal_integral_eq_lintegral_ofReal (hint.indicator hA)
      (Eventually.of_forall fun x => by by_cases hx : x ∈ A <;> simp [hx, hg0])
  rw [← hofr] at hs
  have hbound0 : 0 ≤ C8 ^ (1 / (1 : ℝ)) * (K * ((ν A).toReal) ^ (3 / 4 : ℝ)) := by positivity
  have := (ENNReal.ofReal_le_ofReal_iff hbound0).1 hs
  simpa using this

theorem r26t3_collision_boundary {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (N : ℕ) (hN : 2 ≤ N) :
    ∀ i j : Fin N, i ≠ j →
      Tendsto (fun η : ℝ => η⁻¹ * (∫ X in {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η},
        (1 + ∑ k, ‖X k‖) ^ 2 ∂(r26t3_Q R N))) (𝓝[>] 0) (𝓝 0) := by
  intro i j hij
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c0, S, hc0, hTc⟩ := href 0
  have hd := p.hd
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hM : ∀ x, R.ρ 0 x ≤ |M₀| := fun x =>
    calc R.ρ 0 x ≤ M₀ * Real.exp (-c0 * ‖x‖ ^ 2) := hTc.gauss x
      _ ≤ |M₀| * Real.exp (-c0 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |M₀| * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])) (abs_nonneg _)
      _ = |M₀| := mul_one _
  obtain ⟨hQprob, hLr⟩ := r26t3_static_pressure hδ hδh R hγ
  obtain ⟨C8, hC8⟩ := hLr 8 (by norm_num)
  have hint2 := (r26t3_infinity_boundary hδ hδh R hγ N hN 2).1
  set ν : Measure (EucConfig p.d N) := Measure.pi fun _ : Fin N => r26t3_mu R 0 with hν
  have : IsProbabilityMeasure (r26t3_mu R 0) := hP
  have := hQprob N hN
  set Q := r26t3_Q R N with hQ
  have hac : Q ≪ ν := by
    show HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) N p.γ (r26t3_mu R 0) ≪ ν
    unfold HRS.Whole.modulatedGibbs
    exact Measure.AbsolutelyContinuous.smul_left (withDensity_absolutelyContinuous _ _) _
  set ψ : EucConfig p.d N → ℝ≥0∞ := Q.rnDeriv ν with hψdef
  have hψm : Measurable ψ := Measure.measurable_rnDeriv Q ν
  have hQeq : Q = ν.withDensity ψ := (Measure.withDensity_rnDeriv_eq Q ν hac).symm
  set C8' := max C8 0 with hC8'
  have hψ8 : (∫⁻ x, ψ x ^ (8 : ℝ) ∂ν) ^ (1 / (8 : ℝ)) ≤ ENNReal.ofReal C8' := by
    have h := hC8 N hN
    have hm : Measurable fun X : EucConfig p.d N => (ψ X).toReal := hψm.ennreal_toReal
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (by norm_num)] at h
    refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top Q ν] with X hX
    rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hX.ne]
  have hgm : Measurable fun X : EucConfig p.d N => (1 + ∑ k, ‖X k‖) ^ 2 :=
    (measurable_const.add (Finset.measurable_sum _ fun i _ => (measurable_norm.comp (measurable_pi_apply i)))).pow_const 2
  have hgL : eLpNorm (fun X : EucConfig p.d N => (1 + ∑ k, ‖X k‖) ^ 2) (ENNReal.ofReal 8) ν < ⊤ := by
    have hI := s21f_config_sq (N := N) (μ := r26t3_mu R 0) (fun m => s21f_moment_mu hTc hc0 m) 8
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top hgm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (by norm_num)]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
    have := hI.lintegral_lt_top
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun X => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity)
      (by norm_num)]
    congr 1
    rw [← pow_mul, show ((1 + ∑ k, ‖X k‖) ^ 2) ^ (8 : ℝ) = ((1 + ∑ k, ‖X k‖) ^ 2) ^ (8 : ℕ) from
      Real.rpow_natCast _ 8, ← pow_mul]
  set K := (eLpNorm (fun X : EucConfig p.d N => (1 + ∑ k, ‖X k‖) ^ 2) (ENNReal.ofReal 8) ν).toReal with hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  set c1 := (volume (ball (0 : Euc p.d) 1)).toReal with hc1
  have hc1_0 : 0 ≤ c1 := ENNReal.toReal_nonneg
  set cc : ℝ := |M₀| * (2 ^ p.d * c1) with hcc
  have hcc0 : 0 ≤ cc := by positivity
  -- the bound for every η > 0
  have hbound : ∀ η : ℝ, 0 < η → 0 ≤ η⁻¹ * (∫ X in {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η},
        (1 + ∑ k, ‖X k‖) ^ 2 ∂Q) ∧ η⁻¹ * (∫ X in {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η},
        (1 + ∑ k, ‖X k‖) ^ 2 ∂Q) ≤ (C8' * (K * cc ^ (3 / 4 : ℝ))) * η ^ ((3 * p.d : ℝ) / 4 - 1) := by
    intro η hη
    have hA : MeasurableSet {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η} :=
      measurableSet_le ((measurable_pi_apply i).sub (measurable_pi_apply j)).norm measurable_const
    refine ⟨mul_nonneg (inv_nonneg.2 hη.le) (setIntegral_nonneg hA fun X _ => by positivity), ?_⟩
    have h1 := s21f_Lp_cut ν hψm (le_max_right _ _) hψ8 hgm (fun X => by positivity) hgL
      (by rw [← hQeq]; exact hint2) hA
    rw [← hQeq] at h1
    have h2 := s21f_pair_ball (N := N) hTc.prob hM i j hij hη.le
    have h3 : (ν {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η}).toReal ≤ cc * η ^ p.d := by
      have hfin : ENNReal.ofReal |M₀| * (ENNReal.ofReal ((2 * η) ^ p.d) * volume (ball (0 : Euc p.d) 1)) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          measure_ball_lt_top.ne)
      refine (ENNReal.toReal_mono hfin h2).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
        ENNReal.toReal_ofReal (by positivity), ← hc1, hcc, mul_pow]
      ring
    have h4 : ((ν {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η}).toReal) ^ (3 / 4 : ℝ) ≤
        (cc * η ^ p.d) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow ENNReal.toReal_nonneg h3 (by norm_num)
    have h5 : (cc * η ^ p.d) ^ (3 / 4 : ℝ) = cc ^ (3 / 4 : ℝ) * η ^ ((3 * p.d : ℝ) / 4) := by
      rw [Real.mul_rpow hcc0 (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      congr 2; ring
    have h6 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hη.le)
    refine h6.trans ?_
    have h7 : η⁻¹ * (C8' * (K * ((ν {X : EucConfig p.d N | ‖X i - X j‖ ≤ 2 * η}).toReal) ^ (3 / 4 : ℝ))) ≤
        η⁻¹ * (C8' * (K * ((cc * η ^ p.d) ^ (3 / 4 : ℝ)))) := by
      gcongr
    refine h7.trans (le_of_eq ?_)
    rw [h5, Real.rpow_sub_one hη.ne']
    field_simp
  have hexp : 0 < (3 * p.d : ℝ) / 4 - 1 := by
    have : (2 : ℝ) ≤ p.d := by exact_mod_cast hd
    linarith
  have hlim : Tendsto (fun η : ℝ => (C8' * (K * cc ^ (3 / 4 : ℝ))) * η ^ ((3 * p.d : ℝ) / 4 - 1))
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun η : ℝ => η ^ ((3 * p.d : ℝ) / 4 - 1)) (𝓝 0) (𝓝 (0 ^ ((3 * p.d : ℝ) / 4 - 1))) :=
      (Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)).tendsto
    rw [Real.zero_rpow hexp.ne'] at h0
    simpa using (h0.mono_left nhdsWithin_le_nhds).const_mul (C8' * (K * cc ^ (3 / 4 : ℝ)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη using (hbound η hη).1
  · filter_upwards [self_mem_nhdsWithin] with η hη using (hbound η hη).2

end HRS.MS.R26T3
