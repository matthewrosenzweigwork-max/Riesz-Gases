import HRS.MS.Fp81S21Radius
import HRS.MS.S21F_D02
import HRS.MS.S21H2_W13
import HRS.MS.R2InterpAux105

/-!
# HRS S2.1(iii), SOL26 packet 4: all-time density and moment constants

The constants below are selected after the resulting trajectory, and before every
physical time, particle count, and particle realization.  The finite-horizon fields
in `Fp81S21MovingInputs2` are therefore unnecessary for this all-time extraction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA
open HRS.MS.R26T3 HRS.MS.R2Interp

private theorem fp81s21_uniform_gaussian_weighted_moment
    {d : ℕ} {C₀ c₀ a : ℝ} (hc₀ : 0 < c₀) (ha : 0 ≤ a) :
    ∃ Mρ : ℝ, ∀ {ρ : Euc d → ℝ},
      (hρ : HRS.Whole.IsProbDensity ρ) →
      (hG : HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ) →
      Integrable (fun x : Euc d => ρ x * jbracket x ^ a) ∧
        (∫ x : Euc d, ρ x * jbracket x ^ a) ≤ Mρ := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hc₀
    (Pw := a / 2) (by linarith)
  refine ⟨C, ?_⟩
  intro ρ hρ hG
  have hpow : ∀ x : Euc d, (jbracket x ^ (a / 2)) ^ 2 = jbracket x ^ a := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one (HRS.MS.R2Poly.s95_one_le_jb x)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    ring
  have hpowBound :
      (∫⁻ x, ENNReal.ofReal (jbracket x ^ a) ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((jbracket x ^ (a / 2)) ^ 2) ∂(HRS.Whole.withDensityReal ρ) := by
        refine lintegral_congr fun x => ?_
        rw [hpow]
      _ ≤ ENNReal.ofReal C := hC ρ hρ hG.2
  have hgm : Measurable (fun x : Euc d => jbracket x ^ a) := by
    unfold jbracket
    fun_prop
  have h1 :
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ a) ∂(HRS.Whole.withDensityReal ρ)) =
        ∫⁻ x, ENNReal.ofReal (ρ x * jbracket x ^ a) := by
    unfold HRS.Whole.withDensityReal
    have hf : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
      ENNReal.measurable_ofReal.comp hρ.measurable
    have hg : Measurable (fun y => ENNReal.ofReal (jbracket y ^ a)) :=
      ENNReal.measurable_ofReal.comp hgm
    rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x))
      (g := fun y => ENNReal.ofReal (jbracket y ^ a)) volume hf hg]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hρ.nonneg x)]
  rw [h1] at hpowBound
  have hga : ∀ x : Euc d, 0 ≤ jbracket x ^ a := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) a
  have hint : Integrable (fun x : Euc d => ρ x * jbracket x ^ a) := by
    refine ⟨(hρ.measurable.mul hgm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc
      ∫⁻ x, ‖ρ x * jbracket x ^ a‖ₑ =
          ∫⁻ x, ENNReal.ofReal (ρ x * jbracket x ^ a) := by
        refine lintegral_congr fun x => ?_
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (hρ.nonneg x) (hga x))]
      _ ≤ ENNReal.ofReal C := hpowBound
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => mul_nonneg (hρ.nonneg x) (hga x))
    (hρ.measurable.mul hgm).aestronglyMeasurable]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpowBound
  rwa [ENNReal.toReal_ofReal hC0] at hreal

private theorem fp81s21_uniform_pair_withDensityReal
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (f : Euc d → ℝ) :
    HRS.Whole.pair (HRS.Whole.withDensityReal ρ) f = ∫ x, ρ x * f x := by
  unfold HRS.Whole.pair HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
  · exact (hρ.measurable.ennreal_ofReal).aemeasurable
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private theorem fp81s21_uniform_log_integrable
    {d : ℕ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hmom : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ) := by
  have hρi : Integrable ρ volume := HRS.Whole.Q34.integrable_of_isProbDensity hρ
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hcont : Continuous fun x : Euc d => Real.log (2 + ‖x‖) :=
    (continuous_const.add continuous_norm).log (fun x => by
      show (2 + ‖x‖) ≠ 0
      positivity)
  have hdom : Integrable
      (fun x : Euc d => (3 / 2 : ℝ) * ρ x + (1 / 2 : ℝ) * (‖x‖ ^ 2 * ρ x)) :=
    (hρi.const_mul _).add (hmom.const_mul _)
  refine hdom.mono'
    ((hρ.measurable.ennreal_ofReal.ennreal_toReal.smul hcont.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hx := hρ.nonneg x
  have hr := norm_nonneg x
  have hlog0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith)
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul,
    Real.norm_of_nonneg (mul_nonneg hx hlog0)]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
  nlinarith [mul_nonneg hx (sq_nonneg (‖x‖ - 1))]

/-- All-time Gaussian, reference-density, reference-moment, and particle-marginal
moment constants.  `C₀,c₀,M,L,Mρ` depend at most on the fixed trajectory; `pinf,K`
come from the unconditional actual-density producer.  Every displayed time bound is
for all `t ≥ 0`, and `Cm` is uniform in both `N` and `A`. -/
theorem fp81s21_uniform_density_moments (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        ∃ pinf K C₀ c₀ M L Mρ Cm : ℝ,
          1 < pinf ∧
          0 < c₀ ∧
          (∀ t : ℝ, 0 ≤ t → HRS.Whole.HasR2GaussianUpper C₀ c₀ (R.ρ t)) ∧
          (∀ t : ℝ, 0 ≤ t → HRS.Whole.IsRound2Density p.d p.s M L (R.ρ t)) ∧
          (∀ t : ℝ, 0 ≤ t →
            Integrable (fun x : Euc p.d => R.ρ t x * jbracket x ^ (2 * ((p.d : ℝ) + 2))) ∧
            (∫ x : Euc p.d, R.ρ t x * jbracket x ^ (2 * ((p.d : ℝ) + 2))) ≤ Mρ) ∧
          (∀ N : ℕ, ∀ (hN : 2 ≤ N) (A : Particle R N) (t : ℝ), 0 ≤ t →
            HasR2ActualDensity p.s p.β pinf K (r26t3_mu R t)
                (law A.P (A.X t.toNNReal)) ∧
              Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
                (HRS.Whole.meanEmpirical (law A.P (A.X t.toNNReal))) ∧
              (∫ x : Euc p.d, jbracket x ^ ((p.d : ℝ) + 2)
                ∂(HRS.Whole.meanEmpirical (law A.P (A.X t.toNNReal)))) ≤ Cm) := by
  obtain ⟨δcommon, Co, co, hδcommon, hcommonHalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δactual, pinf, K, η, gapConst, hδactual, hδactualHalf, hpinf,
    -, -, -, -, -, hactual, -⟩ := fp81s21_uniform_thermal_package p
  let δ0 : ℝ := min δcommon δactual
  have hδ0 : 0 < δ0 := lt_min hδcommon hδactual
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hcommonHalf
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0Half
  have hδactual' : δ ≤ δactual := hδle.trans (min_le_right _ _)
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hmono := HRS.MS.S21A.s21a_cls_mono p.hd p.hs0 hsd p.ha p.hβ R.thermal
    (hle := hδactual') R.admissible R.resulting
  let Rdens : Trajectory p δactual :=
    { ρβ := R.ρβ
      thermal := R.thermal
      ε := R.ε
      ψ := R.ψ
      admissible := hmono.1
      ρ := R.ρ
      resulting := hmono.2 }
  obtain ⟨-, -, hreference, -⟩ := HRS.MS.R26T3.r26t3_reference_data p δ hδ hδhalf R
  obtain ⟨cgauss, C₀, hcgauss, hC₀, hCgauss⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 (by linarith [p.hs]) p.ha p.hβ δ p.c₁ p.C₁ 0 (by norm_num)
    R.thermal R.resulting
  have hc₀ : 0 < cgauss := hcgauss
  obtain ⟨M2, hM2⟩ := fp81s21_uniform_gaussian_weighted_moment
    (d := p.d) (C₀ := C₀) (c₀ := cgauss) (a := (2 : ℝ)) hc₀
    (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨Mρ, hMρ⟩ := fp81s21_uniform_gaussian_weighted_moment
    (d := p.d) (C₀ := C₀) (c₀ := cgauss)
    (a := 2 * ((p.d : ℝ) + 2)) hc₀ (by positivity)
  obtain ⟨Cm, hCm⟩ := HRS.MS.R2Interp.s102_marginal_moment_bound
    p.hd p.hs0 p.hs C₀ (3 / 2 + M2 / 2) C₀ cgauss p.β pinf K hc₀ p.hβ hpinf
    (Pw := (p.d : ℝ) + 2) (by positivity)
  have hactualAll : ∀ N : ℕ, ∀ (hN : 2 ≤ N) (A : Particle R N) (t : ℝ), 0 ≤ t →
      HasR2ActualDensity p.s p.β pinf K (r26t3_mu R t)
        (law A.P (A.X t.toNNReal)) := by
    intro N hN A t ht
    let Adens : Particle Rdens N :=
      { A with initial := by simpa [Rdens, r26t3_Q, r26t3_mu] using A.initial }
    simpa [Rdens, r26t3_mu] using hactual Rdens N hN Adens t ht
  have hgaussianAll : ∀ t : ℝ, 0 ≤ t →
      HRS.Whole.HasR2GaussianUpper C₀ cgauss (R.ρ t) := by
    intro t ht
    refine ⟨hcgauss, ?_⟩
    intro x
    have h := (hCgauss t ht).2 0 (by omega) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg ((hreference t ht).2 x).le] at h
    exact h
  have hround2All : ∀ t : ℝ, 0 ≤ t →
      HRS.Whole.IsRound2Density p.d p.s C₀ (3 / 2 + M2 / 2) (R.ρ t) := by
    intro t ht
    have hT : 0 < t + 1 := by linarith
    let hsol := R.resulting.global (t + 1)
    have htT : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
    have hρ := (hreference t ht).1
    have hbd : ∀ x, R.ρ t x ≤ C₀ := by
      intro x
      have h := (hgaussianAll t ht).2 x
      have hexp : Real.exp (-cgauss * ‖x‖ ^ 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg ‖x‖, hcgauss]
      calc
        R.ρ t x ≤ C₀ * Real.exp (-cgauss * ‖x‖ ^ 2) := h
        _ ≤ C₀ := by
          nlinarith [hC₀, Real.exp_pos (-cgauss * ‖x‖ ^ 2)]
    have hsecond := hsol.second_moment t htT
    have hsecondBound :
        (∫ x : Euc p.d, ‖x‖ ^ 2 * R.ρ t x) ≤ M2 := by
      have hupper : ∀ x : Euc p.d,
          ‖x‖ ^ 2 * R.ρ t x ≤ R.ρ t x * jbracket x ^ (2 : ℝ) := by
        intro x
        have hjb : jbracket x ^ (2 : ℝ) = 1 + ‖x‖ ^ 2 := by
          calc
            jbracket x ^ (2 : ℝ) = jbracket x ^ (2 : ℕ) := Real.rpow_natCast _ _
            _ = 1 + ‖x‖ ^ 2 := HRS.MS.R2Poly.s95_jb_sq x
        rw [hjb]
        nlinarith [sq_nonneg ‖x‖, hρ.nonneg x]
      exact (integral_mono hsecond (hM2 hρ (hgaussianAll t ht)).1 hupper).trans
        (hM2 hρ (hgaussianAll t ht)).2
    let μ : Measure (Euc p.d) := r26t3_mu R t
    haveI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
    have hlog := fp81s21_uniform_log_integrable hρ hsecond
    have hnorm2 : Integrable (fun x : Euc p.d => ‖x‖ ^ 2) μ := by
      change Integrable (fun x : Euc p.d => ‖x‖ ^ 2)
        (HRS.Whole.withDensityReal (R.ρ t))
      unfold HRS.Whole.withDensityReal
      rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      refine hsecond.congr (Eventually.of_forall fun x => ?_)
      simp [ENNReal.toReal_ofReal (hρ.nonneg x), mul_comm]
    have hpair :
        (∫ x : Euc p.d, ‖x‖ ^ 2 ∂μ) =
          ∫ x : Euc p.d, R.ρ t x * ‖x‖ ^ 2 := by
      calc
        _ = HRS.Whole.pair μ (fun x : Euc p.d => ‖x‖ ^ 2) := rfl
        _ = _ := by
          simpa [HRS.Whole.pair, μ, r26t3_mu] using
            fp81s21_uniform_pair_withDensityReal hρ (fun x : Euc p.d => ‖x‖ ^ 2)
    have hlogBound :
        (∫ x : Euc p.d, Real.log (2 + ‖x‖) ∂μ) ≤ 3 / 2 + M2 / 2 := by
      have hconst : Integrable (fun _ : Euc p.d => (3 / 2 : ℝ)) μ :=
        integrable_const _
      have hquad : Integrable (fun x : Euc p.d => (1 / 2 : ℝ) * ‖x‖ ^ 2) μ :=
        hnorm2.const_mul _
      have hupperInt : Integrable
          (fun x : Euc p.d => (3 / 2 : ℝ) + (1 / 2 : ℝ) * ‖x‖ ^ 2) μ :=
        hconst.add hquad
      calc
        _ ≤ ∫ x : Euc p.d, (3 / 2 : ℝ) + (1 / 2 : ℝ) * ‖x‖ ^ 2 ∂μ :=
          integral_mono hlog hupperInt
            (f := fun x : Euc p.d => Real.log (2 + ‖x‖))
            (g := fun x : Euc p.d => (3 / 2 : ℝ) + (1 / 2 : ℝ) * ‖x‖ ^ 2)
            (fun x => by
            calc
              Real.log (2 + ‖x‖) ≤ 2 + ‖x‖ - 1 :=
                Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
              _ = 1 + ‖x‖ := by ring
              _ ≤ 3 / 2 + (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
                nlinarith [sq_nonneg (‖x‖ - 1)])
        _ = 3 / 2 + (1 / 2 : ℝ) * (∫ x : Euc p.d, ‖x‖ ^ 2 ∂μ) := by
          rw [integral_add (integrable_const _) (hnorm2.const_mul _), integral_const,
            integral_const_mul]
          simp
        _ = 3 / 2 + (1 / 2 : ℝ) *
            (∫ x : Euc p.d, R.ρ t x * ‖x‖ ^ 2) := by rw [hpair]
        _ ≤ 3 / 2 + M2 / 2 := by
          have hsecondBound' :
              (∫ x : Euc p.d, R.ρ t x * ‖x‖ ^ 2) ≤ M2 := by
            simpa only [mul_comm] using hsecondBound
          nlinarith [hsecondBound']
    refine { prob := hρ, bdd := hbd, logMoment := ?_ }
    intro hs0
    exact ⟨hlog, hlogBound⟩
  have hreferenceMoment : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x : Euc p.d => R.ρ t x * jbracket x ^
        (2 * ((p.d : ℝ) + 2))) ∧
      (∫ x : Euc p.d, R.ρ t x * jbracket x ^
        (2 * ((p.d : ℝ) + 2))) ≤ Mρ := by
    intro t ht
    exact hMρ (hreference t ht).1 (hgaussianAll t ht)
  have hparticleMoment : ∀ N : ℕ, ∀ (hN : 2 ≤ N) (A : Particle R N) (t : ℝ), 0 ≤ t →
      HasR2ActualDensity p.s p.β pinf K (r26t3_mu R t)
          (law A.P (A.X t.toNNReal)) ∧
        Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
          (HRS.Whole.meanEmpirical (law A.P (A.X t.toNNReal))) ∧
        (∫ x : Euc p.d, jbracket x ^ ((p.d : ℝ) + 2)
          ∂(HRS.Whole.meanEmpirical (law A.P (A.X t.toNNReal)))) ≤ Cm := by
    intro N hN A t ht
    have hAD := hactualAll N hN A t ht
    have hρR := hround2All t ht
    have hG := hgaussianAll t ht
    have hP := hAD
    have hInt := HRS.MS.R2Interp.s102_marginal_moment
      p.hd p.hs0 p.hs C₀ (3 / 2 + M2 / 2) C₀ cgauss p.β pinf K hcgauss p.hβ hpinf
      (Pw := (p.d : ℝ) + 2) (by positivity) hρR hG.2 hN hP
    have hBound := hCm hρR (fun x => hG.2 x) hN hP
    exact ⟨hAD, hInt, hBound⟩
  refine ⟨pinf, K, C₀, cgauss, C₀, 3 / 2 + M2 / 2, Mρ, Cm,
    hpinf, hcgauss, hgaussianAll, hround2All, hreferenceMoment, hparticleMoment⟩

#print axioms HRS.Fp81.S21.fp81s21_uniform_density_moments

end HRS.Fp81.S21
