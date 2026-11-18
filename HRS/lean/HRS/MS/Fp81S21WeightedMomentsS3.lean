import HRS.MS.Fp81S21WeightedMomentsS
import HRS.MS.Fp81S21WeightedMomentsS2
import HRS.MS.Fp81S21WeightedMoments10

/-! Strong-chart particle moment producer for the empirical fluctuation. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111
open HRS.MS.R2Interp

private theorem fp81s21_strong_weightedMeasure_integrable_of_densityMoment
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    {Pw : ℝ} (hPw : 0 ≤ Pw)
    (hHigher : Integrable
      (fun x : Euc d => ρ x * jbracket x ^ (2 * Pw)) volume) :
    Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.withDensityReal ρ) := by
  have hjb : Continuous (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  have hweight : Measurable (fun x : Euc d => jbracket x ^ Pw) :=
    (hjb.rpow_const fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne').measurable
  have hρtoReal : Measurable (fun x : Euc d => (ENNReal.ofReal (ρ x)).toReal) :=
    (ENNReal.measurable_ofReal.comp hρ.measurable).ennreal_toReal
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine hHigher.mono' ?_ ?_
  · exact (hρtoReal.smul hweight).aestronglyMeasurable
  · filter_upwards [] with x
    have hρx : 0 ≤ ρ x := hρ.nonneg x
    have hbase : 1 ≤ jbracket x := HRS.MS.R2Poly.s95_one_le_jb x
    have hpower : jbracket x ^ Pw ≤ jbracket x ^ (2 * Pw) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    rw [smul_eq_mul, ENNReal.toReal_ofReal hρx]
    rw [Real.norm_of_nonneg (mul_nonneg hρx
      (Real.rpow_nonneg (by positivity) _))]
    exact mul_le_mul_of_nonneg_left hpower hρx

private theorem fp81s21_strong_moving_density_clip_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous (fun q : ℝ × Euc p.d =>
      R.ρ ((max q.1 0).toNNReal) q.2) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x :=
    fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  have hjoint := HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass
  have hmap : Continuous (fun q : ℝ × Euc p.d =>
      ((max q.1 0).toNNReal, q.2)) := by
    fun_prop
  exact hjoint.comp hmap


private theorem fp81s21_strong_weighted_reference_integrable
    {d : ℕ} {ρ : Euc d → ℝ} {C₀ c₀ Pw : ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hc₀ : 0 < c₀) (hPw : 0 ≤ Pw)
    (hG : HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ) :
    Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC₀, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hc₀
    (Pw := Pw / 2) (by linarith)
  have hpow : ∀ x : Euc d, (jbracket x ^ (Pw / 2)) ^ 2 = jbracket x ^ Pw := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one
      (HRS.MS.R2Poly.s95_one_le_jb x)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    ring
  have hbound :
      (∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
        ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((jbracket x ^ (Pw / 2)) ^ 2)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [hpow]
      _ ≤ ENNReal.ofReal C := hC ρ hρ hG.2
  have hjb : Continuous (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  have hmeas : Measurable (fun x : Euc d => jbracket x ^ Pw) :=
    (hjb.rpow_const fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne').measurable
  have hnonneg : ∀ x : Euc d, 0 ≤ jbracket x ^ Pw := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc
    ∫⁻ x, ‖jbracket x ^ Pw‖ₑ ∂(HRS.Whole.withDensityReal ρ) =
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    _ ≤ ENNReal.ofReal C := hbound
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- A uniform coefficient second moment and the requested `MomentRep` for
the moving empirical fluctuation. The representative is built from the
configuration Riesz map and the jointly measurable particle modification. -/
theorem fp81s21_particle_eta_momentRep_strong (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 6)
              ((p.d : ℝ) + 4),
            ∃ qη : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep E A.P
                (fp81s21_particleEmpField R N A) qη M := by
  obtain ⟨δ0, hδ0, hδ0half, hUniform⟩ := fp81s21_uniform_density_moments p
  have hPw : 0 ≤ (p.d : ℝ) + 4 := by positivity
  have hChartCond : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  obtain ⟨Cw, hCw, hCompare⟩ := fp81s21_dualNormE_le_r2NegSobNorm
    (d := p.d) (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4) hChartCond
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hReferenceMoment, hParticle⟩ :=
      hUniform δ hδ hδle R
  have hPwStrong : 0 ≤ (p.d : ℝ) + 4 := by positivity
  have hChartCondStrong : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  have hOrderStrong : (p.d : ℝ) + 3 + (p.d : ℝ) / 2 <
      ((2 * p.d + 6 : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (2 : ℝ) ≤ p.d by exact_mod_cast p.hd]
  obtain ⟨D, hD, hNegMoment⟩ := fp81s21_emp_r2wfm_singleLaw_gen
    p (r := 2 * p.d + 6) (Pw := (p.d : ℝ) + 4)
    (M := M) (L := L) (C₀ := C₀) (c₀ := c₀) (pinf := pinf) (K := K)
    hPwStrong hOrderStrong hc₀ hpinf
  let Mrep : ℝ := Cw ^ 2 * D
  have hMrep : 0 ≤ Mrep := by positivity
  refine ⟨Mrep, hMrep, ?_⟩
  intro N hN A E
  let clip : ℝ → ℝ := fun u => ((max u 0).toNNReal : ℝ)
  have hclipEq : clip = fun u => max u 0 := by
    funext u
    dsimp [clip]
    exact Real.coe_toNNReal _ (le_max_right _ _)
  have hclip_nonneg : ∀ u, 0 ≤ clip u := by
    intro u
    rw [hclipEq]
    exact le_max_right _ _
  let μclip : ℝ → Measure (Euc p.d) :=
    fun u => HRS.Whole.withDensityReal (R.ρ (clip u))
  have hρjoint : Measurable (fun q : ℝ × Euc p.d => R.ρ (clip q.1) q.2) := by
    simpa [clip] using
      (fp81s21_strong_moving_density_clip_continuous p R hδ
        (hδle.trans hδ0half)).measurable
  have hρnonneg : ∀ u x, 0 ≤ R.ρ (clip u) x := by
    intro u x
    exact (hRound2 (clip u) (hclip_nonneg u)).prob.nonneg x
  have hReferenceIntegrable : ∀ u,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4)) (μclip u) := by
    intro u
    exact fp81s21_strong_weighted_reference_integrable
      (hRound2 (clip u) (hclip_nonneg u)).prob hc₀ hPwStrong
      (hGaussian (clip u) (hclip_nonneg u))
  have hm : ∀ j, Measurable (fun u =>
      HRS.Whole.pair (μclip u) (E.test j)) := by
    intro j
    have htest : Measurable (fun q : ℝ × Euc p.d => E.test j q.2) :=
      ((E.test_smooth j).1.continuous.measurable).comp measurable_snd
    have hint : Measurable (fun u =>
        ∫ x, E.test j x ∂μclip u) := by
      simpa [μclip] using
        fp81s21_moving_spatial_integral_meas hρjoint hρnonneg htest
    simpa [HRS.Whole.pair] using hint
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 6 : ℕ) := by
    push_cast
    nlinarith
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hN
  obtain ⟨z, hzMeas, hzRep⟩ := fp81s21_emp_config_rep
    (d := p.d) (r := 2 * p.d + 6) (N := N) (Pw := (p.d : ℝ) + 4)
    hd1 hPw hr hChartCond E hNpos μclip hReferenceIntegrable hm

  have hXmeas : ∀ t, Measurable (A.X t) :=
    (A.strong (1 : ℝ)).adapted
  have hXcont := (A.strong (1 : ℝ)).cont
  obtain ⟨Y, hYmeas, hYae⟩ := HRS.MS.R2S11.s11_X_joint hXmeas hXcont
  let qη : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    z (clip u) (Y (clip u, ω))
  have hclipMeas : Measurable clip := by
    rw [hclipEq]
    fun_prop
  have hYclip : Measurable (fun q : ℝ × A.Ω => Y (clip q.1, q.2)) :=
    hYmeas.comp ((hclipMeas.comp measurable_fst).prodMk measurable_snd)
  have hqMeas : Measurable (Function.uncurry qη) := by
    exact hzMeas.comp ((hclipMeas.comp measurable_fst).prodMk hYclip)
  refine ⟨qη, hqMeas, ?_⟩
  intro u hu
  let t : NNReal := Real.toNNReal u
  have hclipu : clip u = u := by
    rw [hclipEq]
    change max u 0 = u
    exact max_eq_left hu
  have hActual := (hParticle N hN A u hu).1
  change HRS.Whole.HasR2ActualDensity p.s p.β pinf K
    (HRS.Whole.withDensityReal (R.ρ u)) (A.P.map (A.X t)) at hActual
  have hLower := hNegMoment (R.ρ u) (hRound2 u hu) (hGaussian u hu)
    N hN (A.P.map (A.X t)) hActual
  let Pactual : Measure (EucConfig p.d N) := A.P.map (A.X t)
  let T : EucConfig p.d N → (Euc p.d → ℝ) → ℝ :=
    fun X => HRS.Whole.r2EmpDistr (HRS.Whole.withDensityReal (R.ρ u)) X
  have hTRep : ∀ X, fp81s21_TestRep E (T X) (z u X) := by
    intro X
    have h := hzRep u X
    simpa [T, μclip, hclipu, HRS.MS.R26T3.r26t3_mu] using h
  have hZU : Measurable (z u) := hzMeas.comp
    (measurable_const.prodMk measurable_id)
  have hIu : Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4))
      (HRS.Whole.withDensityReal (R.ρ u)) := by
    simpa [μclip, hclipu] using hReferenceIntegrable u
  have hHom : ∀ X c f, IsR2Test f → T X (c • f) = c * T X f := by
    intro X c f hf
    have hZ := HRS.MS.R2Interp.s102_Z_fluct hd1 hPw
      (2 * p.d + 6) hr hNpos X
      (HRS.Whole.withDensityReal (R.ρ u)) hIu (Real.sqrt N)
    have hwt : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f :=
      (weightedTestSubmodule_iff).1
        (weighted_test_of_compact_smooth hChartCond hf)
    simpa [T, HRS.Whole.r2EmpDistr] using hZ.smul c f hwt
  have hTransfer := fp81s21_rep_secondMoment E Pactual T (z u)
    hZU hTRep Cw D hCw hD
    (fun X => hCompare (T X) (fun c f hf => hHom X c f hf)) hLower
  have hqAE : qη u =ᵐ[A.P] (fun ω => z u (A.X t ω)) := by
    filter_upwards [hYae] with ω hω
    simp [qη, hclipu, hω u, t]
  have hcompMem : MemLp (fun ω => z u (A.X t ω)) 2 A.P :=
    (memLp_map_measure_iff hTransfer.1.aestronglyMeasurable
      (hXmeas t).aemeasurable).1 hTransfer.1
  have hqMem : MemLp (qη u) 2 A.P :=
    (memLp_congr_ae hqAE).2 hcompMem
  have hIntZ : Integrable (fun X => ‖z u X‖ ^ 2) Pactual := by
    have hi := (integrable_norm_rpow_iff hTransfer.1.aestronglyMeasurable
      (by norm_num) (by norm_num)).2 hTransfer.1
    simpa using hi
  have hnormAE : (fun ω => ‖qη u ω‖ ^ 2) =ᵐ[A.P]
      (fun ω => ‖z u (A.X t ω)‖ ^ 2) := by
    filter_upwards [hqAE] with ω hω
    rw [hω]
  have hIntegralMap :
      (∫ X, ‖z u X‖ ^ 2 ∂Pactual) =
        ∫ ω, ‖z u (A.X t ω)‖ ^ 2 ∂A.P :=
    integral_map (hXmeas t).aemeasurable hIntZ.aestronglyMeasurable
  have hMoment : (∫ ω, ‖qη u ω‖ ^ 2 ∂A.P) ≤ Mrep := by
    calc
      _ = ∫ ω, ‖z u (A.X t ω)‖ ^ 2 ∂A.P := integral_congr_ae hnormAE
      _ = ∫ X, ‖z u X‖ ^ 2 ∂Pactual := hIntegralMap.symm
      _ ≤ Cw ^ 2 * D := hTransfer.2
  have hRepAE : ∀ᵐ ω ∂A.P,
      (∀ f, IsR2Test f →
        fp81s21_chartAction E (qη u ω) f =
          fp81s21_particleEmpField R N A u ω f) ∧
      dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_particleEmpField R N A u ω) = ENNReal.ofReal ‖qη u ω‖ := by
    filter_upwards [hYae] with ω hω
    have h := hzRep u (A.X t ω)
    have hqeq : qη u ω = z u (A.X t ω) := by
      simp [qη, hclipu, hω u, t]
    have hFieldEq : fp81s21_particleEmpField R N A u ω =
        HRS.Whole.r2EmpDistr (μclip u) (A.X t ω) := by
      funext f
      simp [fp81s21_particleEmpField, μclip, hclipu, t,
        HRS.MS.R26T3.r26t3_mu]
    rw [hqeq]
    refine ⟨?_, ?_⟩
    · intro f hf
      simpa [hFieldEq] using h.1 f hf
    · rw [hFieldEq]
      simpa using h.2.2
  exact ⟨hqMem, hMoment, hRepAE⟩


#print axioms HRS.Fp81.S21.fp81s21_particle_eta_momentRep_strong

end HRS.Fp81.S21

end
