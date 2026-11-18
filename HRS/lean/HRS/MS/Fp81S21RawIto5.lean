import HRS.MS.Fp81S21RawIto4
import HRS.MH.DualityRdB3
import HRS.MH.DualityRdB3Aux

/-! Pointwise conversion of the raw generator drift to the empirical-minus-mean-field
weak drift, with the fluctuation residual identified as the deleted-diagonal pair energy. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd
open HRS.MS.R26T3 HRS.MS.R2Interp

theorem fp81s21_particle_raw_drift_linearization
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (Fp : FilteredParticle A)
    {T : ℝ} (hT : 0 < T)
    (hphys : Fp81MovingPhysicalInputs R hN A T)
    {f : Euc p.d → ℝ} (hf : IsR2Test f) :
    ∀ᵐ ζ ∂A.P, ∀ u ∈ Set.Icc (0 : ℝ) T,
      fp81s21_particle_raw_physicalDrift p A f u ζ =
      Real.sqrt N * (
        (Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ))
          (driftTestRd (quadraticGradientDyn p.d p.s p.a p.β)
            (fun _ => f) (fun _ _ => 0) u) +
          interactionPairingW (quadraticGradientDyn p.d p.s p.a p.β) f
            (Whole.empirical (Fp.X u.toNNReal ζ)) (Whole.empirical (Fp.X u.toNNReal ζ))) -
        (Whole.pair (r26t3_mu R u)
          (driftTestRd (quadraticGradientDyn p.d p.s p.a p.β)
            (fun _ => f) (fun _ _ => 0) u) +
          interactionPairingW (quadraticGradientDyn p.d p.s p.a p.β) f
            (r26t3_mu R u) (r26t3_mu R u))) := by
  classical
  filter_upwards [Fp.indist, (Fp.strong T).no_collision] with ζ hind hno
  intro u hu
  let D : WholeDyn p.d := quadraticGradientDyn p.d p.s p.a p.β
  let g0 : Euc p.d → ℝ := fun x =>
    D.invβ * Laplacian.laplacian f x - inner ℝ (gradient D.V x) (gradient f x)
  let hfun : Euc p.d → ℝ := fun x =>
    -generatorW (r26t3_coeff R) u f x + g0 x
  have hfMemCb : MemCb 2 f := HRS.MH.DualityRd.db1_memCb_of_compact
    (hf.1.of_le (by norm_num)) hf.2
  obtain ⟨Λ, hreg⟩ := hphys.regular
  have hsol : IsWholeMeanFieldSolution D T R.ρ := by
    simpa [D] using R.resulting.global T
  have hQ : (p.a • (1 : Matrix (Fin p.d) (Fin p.d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 2
  have hVD : VHypRd 2 ΛV G₀ D.V := by
    show VHypRd 2 ΛV G₀ (confinement p.a)
    rw [HRS.MS.S21.s21_confinement_eq]
    exact hV
  have hinv : 0 ≤ D.invβ := (inv_pos.2 p.hβ).le
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hdpos : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hM : MFData p.s Λ T ΛV G₀ D R.ρ := by
    exact ⟨rfl, p.hs0, hsd, hinv, hVD, hsol, hreg⟩
  have hρ : Whole.IsProbDensity (R.ρ u) := hsol.density u hu
  have hρslice : RegSliceRd (R.ρ u) :=
    ⟨hρ, (hreg.1 u hu).1, (hreg.1 u hu).2.1⟩
  let ftime : ℝ → Euc p.d → ℝ := fun _ => f
  let ft : ℝ → Euc p.d → ℝ := fun _ _ => 0
  have hfC12 : IsC12TestRd T ftime ft := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact hf.1.of_le (by norm_num)
    · intro j hj
      obtain ⟨B, hB⟩ := hfMemCb.2 j hj
      exact ⟨B, fun r hr x => by simpa [ftime] using hB (Set.mem_range_self x)⟩
    · intro j hj
      have hc : Continuous (iteratedFDeriv ℝ j f) :=
        hf.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
      simpa [ftime, Function.comp_def] using hc.comp continuous_snd
    · intro x r hr
      simpa [ftime, ft] using (hasDerivAt_const r (f x))
    · exact continuous_const
    · exact ⟨0, fun r hr x => by simp [ft]⟩
  have h2 : Integrable (fun x => R.ρ u x * ‖x‖ ^ 2) := (db1_slice hM hu).2.2.1
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (by norm_num)
  have hV2 : ContDiff ℝ 2 D.V := hVD.1.of_le (by norm_num)
  have hg0cont : Continuous g0 := by
    dsimp [g0]
    exact (continuous_const.mul (HRS.MH.DualityRd.db1_laplacian_continuous hf2)).sub
      ((HRS.MH.DualityRd.db1_gradient_continuous hV2).inner
        (HRS.MH.DualityRd.db1_gradient_continuous hf2))
  obtain ⟨K, hK⟩ := HRS.MH.DualityRd.db3_phi_growth hVD hfC12
  have hg0int : Integrable (fun x => R.ρ u x * g0 x) :=
    HRS.MH.DualityRd.db3_int_lin hρ h2 hg0cont (by
      intro x
      simpa [g0, ftime, ft, driftTestRd] using hK u hu x)
  obtain ⟨hA1, hA2, hA3, hA4⟩ := HRS.MH.DualityRd.pairing_expansion_rd_proof
    D hd1 p.hs0 hsd hρslice hfMemCb
  have hcoeff : r26t3_coeff R = D.coeff R.ρ := rfl
  have hh : ∀ x, hfun x =
      -(inner ℝ (gradient f x)
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad p.d D.s) (R.ρ u) x))) +
        nlTermRd D (R.ρ u) f x := by
    intro x
    dsimp [hfun, g0]
    rw [hcoeff, generatorW_coeff, meanFieldDriftW, inner_sub_left,
      real_inner_comm (gradient f x)
        (Torus.matVec D.M (convGradConvW (rieszKernelGrad p.d D.s) (R.ρ u) x))]
    dsimp [r26t3_coeff, D]
    ring
  have hhInt : Integrable (fun x => R.ρ u x * hfun x) := by
    have heq : (fun x => R.ρ u x * hfun x) =
        fun x => -(R.ρ u x * inner ℝ (gradient f x)
          (Torus.matVec D.M (convGradConvW (rieszKernelGrad p.d D.s) (R.ρ u) x))) +
          R.ρ u x * nlTermRd D (R.ρ u) f x := by
      funext x
      rw [hh x]
      ring
    rw [heq]
    exact hA3.neg.add hA4
  have hnegGInt : Integrable (fun x => R.ρ u x * (-generatorW (r26t3_coeff R) u f x)) := by
    have heq : (fun x => R.ρ u x * (-generatorW (r26t3_coeff R) u f x)) =
        fun x => R.ρ u x * hfun x - R.ρ u x * g0 x := by
      funext x
      dsimp [hfun]
      ring
    rw [heq]
    exact hhInt.sub hg0int
  have hPairDens := HRS.MH.DualityRd.db3_pair_add hnegGInt hg0int hρ
  have hPairDensNeg :
      Whole.pair (r26t3_mu R u) (fun x => -generatorW (r26t3_coeff R) u f x) =
        -Whole.pair (r26t3_mu R u) (generatorW (r26t3_coeff R) u f) := by
    rw [r26t3_mu, Whole.Q09A.pair_withDensityReal hρ,
      Whole.Q09A.pair_withDensityReal hρ]
    have heq : (fun x => R.ρ u x * -generatorW (r26t3_coeff R) u f x) =
        fun x => -(R.ρ u x * generatorW (r26t3_coeff R) u f x) := by
      funext x
      ring
    rw [heq, integral_neg]
  have hPairDensNeg' :
      Whole.pair (Whole.withDensityReal (R.ρ u))
          (fun x => -generatorW (r26t3_coeff R) u f x) =
        -Whole.pair (Whole.withDensityReal (R.ρ u))
          (generatorW (r26t3_coeff R) u f) := by
    simpa [r26t3_mu] using hPairDensNeg
  have hPairEmp :
      Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) hfun =
        Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ))
          (fun x => -generatorW (r26t3_coeff R) u f x) +
        Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) g0 := by
    rw [HRS.MH.DualityRd.dc2_pair_emp, HRS.MH.DualityRd.dc2_pair_emp,
      HRS.MH.DualityRd.dc2_pair_emp]
    simp only [hfun, Finset.sum_add_distrib]
    rw [mul_add]
  have hPairEmpNeg :
      Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ))
          (fun x => -generatorW (r26t3_coeff R) u f x) =
        -Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ))
          (generatorW (r26t3_coeff R) u f) := by
    rw [HRS.MH.DualityRd.dc2_pair_emp, HRS.MH.DualityRd.dc2_pair_emp,
      Finset.sum_neg_distrib]
    ring
  have hXeq : Fp.X u.toNNReal ζ = A.X u.toNNReal ζ := hind (u.toNNReal)
  have htime : ((u.toNNReal : ℝ)) ≤ T := by
    rw [Real.coe_toNNReal _ hu.1]
    exact hu.2
  have hnoU : Fp.X u.toNNReal ζ ∉ eucCollisionSet p.d N := hno (u.toNNReal) htime
  have hfluc := HRS.MH.DualityRd.fluc_pointwise_rd_proof D
    hd1 p.hs0 hsd R.ρ
    (show RegSliceRd (R.ρ u) from hρslice) hfMemCb (Fp.X u.toNNReal ζ)
  have hfunEq : (fun x => -(generatorW (D.coeff R.ρ) u f x) +
        D.invβ * Laplacian.laplacian f x - inner ℝ (gradient D.V x) (gradient f x)) = hfun := by
    funext x
    dsimp [hfun, g0]
    rw [hcoeff]
    ring
  rw [hfunEq] at hfluc
  have hfluc2 := fp81s21_particle_flucInteraction_eq_neg_pairEnergy
    p R hN A Fp hphys hf hu ζ hnoU
  have hDrift : driftTestRd D (fun _ => f) (fun _ _ => 0) u = g0 := by
    funext x
    simp [driftTestRd, g0, D]
  have hlin :
      (Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) g0 +
        interactionPairingW D f (Whole.empirical (Fp.X u.toNNReal ζ))
          (Whole.empirical (Fp.X u.toNNReal ζ))) -
      (Whole.pair (r26t3_mu R u) g0 +
        interactionPairingW D f (r26t3_mu R u) (r26t3_mu R u)) =
        Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ))
          (generatorW (r26t3_coeff R) u f) -
        Whole.pair (r26t3_mu R u) (generatorW (r26t3_coeff R) u f) +
        flucInteractionRd D f (Fp.X u.toNNReal ζ) (R.ρ u) := by
    have hpoint := hfluc
    rw [hPairEmp, hPairDens, hPairEmpNeg, hPairDensNeg'] at hpoint
    have hpoint' :
        (-Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ))
            (generatorW (r26t3_coeff R) u f) +
          Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) g0 +
          interactionPairingW D f (Whole.empirical (Fp.X u.toNNReal ζ))
            (Whole.empirical (Fp.X u.toNNReal ζ))) -
        (-Whole.pair (r26t3_mu R u)
            (generatorW (r26t3_coeff R) u f) +
          Whole.pair (r26t3_mu R u) g0 +
          interactionPairingW D f (r26t3_mu R u) (r26t3_mu R u)) =
          flucInteractionRd D f (Fp.X u.toNNReal ζ) (R.ρ u) := by
      simpa [r26t3_mu] using hpoint
    linarith [hpoint']
  have hEta := fp81s21_particleEmpField_eq_sqrt_pair p R A u ζ
    (generatorW (r26t3_coeff R) u f)
  have hB := fp81s21_particleQuadRawField_eq_N_pairEnergy p R A u ζ f
  rw [← hXeq] at hEta hB
  have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := by
    calc
      Real.sqrt N * Real.sqrt N = (Real.sqrt N) ^ 2 := by ring
      _ = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hroot : Real.sqrt N ≠ 0 := by
    apply ne_of_gt
    exact Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
  change fp81s21_particleEmpField R N A u ζ (generatorW (r26t3_coeff R) u f) -
      fp81s21_particle_raw_cN N * fp81s21_particleQuadRawField R N A u ζ f = _
  rw [hDrift]
  rw [hfluc2] at hlin
  rw [hEta, hB]
  rw [fp81s21_particle_raw_cN]
  have hcN : (Real.sqrt N)⁻¹ * (N : ℝ) = Real.sqrt N := by
    field_simp [hroot]
    nlinarith [hsq]
  rw [← mul_assoc, hcN]
  linear_combination -(Real.sqrt N) * hlin

theorem fp81s21_particle_raw_compact_ito
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (Fp : FilteredParticle A)
    {T : ℝ} (hT : 0 < T)
    (hphys : Fp81MovingPhysicalInputs R hN A T)
    {f : Euc p.d → ℝ} (hf : IsR2Test f) :
    ∀ᵐ ζ ∂A.P,
      IntegrableOn (fun v => fp81s21_particle_raw_physicalDrift p A f v ζ)
        (Set.Icc (0 : ℝ) T) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) T,
        fp81s21_particleEmpField R N A u ζ f =
          fp81s21_particleEmpField R N A 0 ζ f +
            (∫ v in Set.Icc (0 : ℝ) u,
              fp81s21_particle_raw_physicalDrift p A f v ζ) +
            (fp81s21_particle_raw_testIto p A Fp f u ζ -
              fp81s21_particle_raw_testIto p A Fp f 0 ζ) := by
  classical
  let D : WholeDyn p.d := quadraticGradientDyn p.d p.s p.a p.β
  obtain ⟨Λ, hreg⟩ := hphys.regular
  have hsol : IsWholeMeanFieldSolution D T R.ρ := by
    simpa [D] using R.resulting.global T
  have hQ : (p.a • (1 : Matrix (Fin p.d) (Fin p.d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 2
  have hVD : VHypRd 2 ΛV G₀ D.V := by
    show VHypRd 2 ΛV G₀ (confinement p.a)
    rw [HRS.MS.S21.s21_confinement_eq]
    exact hV
  have hinv : 0 ≤ D.invβ := (inv_pos.2 p.hβ).le
  have hd1 : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have hdpos : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith [p.hs]
  have hM : MFData p.s Λ T ΛV G₀ D R.ρ :=
    ⟨rfl, p.hs0, hsd, hinv, hVD, hsol, hreg⟩
  have hfMemCb : MemCb 2 f := HRS.MH.DualityRd.db1_memCb_of_compact
    (hf.1.of_le (by norm_num)) hf.2
  let ftime : ℝ → Euc p.d → ℝ := fun _ => f
  let ft : ℝ → Euc p.d → ℝ := fun _ _ => 0
  have hfC12 : IsC12TestRd T ftime ft := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      exact hf.1.of_le (by norm_num)
    · intro j hj
      obtain ⟨B, hB⟩ := hfMemCb.2 j hj
      exact ⟨B, fun r hr x => by simpa [ftime] using hB (Set.mem_range_self x)⟩
    · intro j hj
      have hc : Continuous (iteratedFDeriv ℝ j f) :=
        hf.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
      simpa [ftime, Function.comp_def] using hc.comp continuous_snd
    · intro x r hr
      simpa [ftime, ft] using (hasDerivAt_const r (f x))
    · exact continuous_const
    · exact ⟨0, fun r hr x => by simp [ft]⟩
  have hTmem : T ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hT, le_rfl⟩
  have hemp := fp81s21_particle_empirical_compact_ito p R A Fp hT hf
  have hmf := HRS.MH.DualityRd.mf_time_dependent_proof hM hTmem hfC12
  have hlin := fp81s21_particle_raw_drift_linearization p R hN A Fp hT hphys hf
  have htrunc := fp81s21_particle_raw_truncation_congr p R hN A Fp hT hf
  filter_upwards [hemp, hlin, htrunc, Fp.indist] with ζ he hl ht hind
  have hEI := (he T hTmem).1
  have hMI := (hmf T hTmem).1
  let empWeak : ℝ → ℝ := fun v =>
    Whole.pair (Whole.empirical (Fp.X v.toNNReal ζ))
        (driftTestRd D ftime ft v) +
      interactionPairingW D (ftime v) (Whole.empirical (Fp.X v.toNNReal ζ))
        (Whole.empirical (Fp.X v.toNNReal ζ))
  let mfWeak : ℝ → ℝ := fun v =>
    Whole.pair (r26t3_mu R v) (driftTestRd D ftime ft v) +
      interactionPairingW D (ftime v) (r26t3_mu R v) (r26t3_mu R v)
  have hEI' : IntegrableOn empWeak (Set.Icc (0 : ℝ) T) := by
    simpa [empWeak, ftime, ft, D] using hEI
  have hMI' : IntegrableOn mfWeak (Set.Icc (0 : ℝ) T) := by
    simpa [mfWeak, ftime, ft, D, r26t3_mu] using hMI
  have hDriftInt :
      IntegrableOn (fun v => fp81s21_particle_raw_physicalDrift p A f v ζ)
        (Set.Icc (0 : ℝ) T) := by
    have hdiff : IntegrableOn (fun v => Real.sqrt N * (empWeak v - mfWeak v))
        (Set.Icc (0 : ℝ) T) := (hEI'.sub hMI').const_mul (Real.sqrt N)
    exact hdiff.congr_fun (fun v hv => (hl v hv).symm) measurableSet_Icc
  refine ⟨hDriftInt, ?_⟩
  intro u hu
  obtain ⟨hEIu, hEeq⟩ := he u hu
  obtain ⟨hMIu, hMeq⟩ := hmf u hu
  have hEIu' : IntegrableOn empWeak (Set.Icc (0 : ℝ) u) := by
    simpa [empWeak, ftime, ft, D] using hEIu
  have hMIu' : IntegrableOn mfWeak (Set.Icc (0 : ℝ) u) := by
    simpa [mfWeak, ftime, ft, D, r26t3_mu] using hMIu
  have hIeq :
      (∫ v in Set.Icc (0 : ℝ) u, fp81s21_particle_raw_physicalDrift p A f v ζ) =
        Real.sqrt N * ((∫ v in Set.Icc (0 : ℝ) u, empWeak v) -
          ∫ v in Set.Icc (0 : ℝ) u, mfWeak v) := by
    calc
      (∫ v in Set.Icc (0 : ℝ) u, fp81s21_particle_raw_physicalDrift p A f v ζ) =
          ∫ v in Set.Icc (0 : ℝ) u, Real.sqrt N * (empWeak v - mfWeak v) := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro v hv
            have hvT : v ∈ Set.Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hu.2⟩
            simpa [empWeak, mfWeak, ftime, ft, D] using hl v hvT
      _ = Real.sqrt N * ∫ v in Set.Icc (0 : ℝ) u, empWeak v - mfWeak v := by
            rw [integral_const_mul]
      _ = Real.sqrt N * ((∫ v in Set.Icc (0 : ℝ) u, empWeak v) -
            ∫ v in Set.Icc (0 : ℝ) u, mfWeak v) := by
            rw [integral_sub hEIu' hMIu']
  have hEmpEq :
      Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) f =
        Whole.pair (Whole.empirical (Fp.X 0 ζ)) f +
          (∫ v in Set.Icc (0 : ℝ) u, empWeak v) +
          (Real.sqrt (2 * D.invβ) / (N : ℝ)) *
            itoIntegral A.P Fp.ℱ Fp.Wc
              (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ := by
    simpa [empWeak, ftime, ft, D] using hEeq
  have hMfEq :
      Whole.pair (r26t3_mu R u) f =
        Whole.pair (r26t3_mu R 0) f + ∫ v in Set.Icc (0 : ℝ) u, mfWeak v := by
    simpa [mfWeak, ftime, ft, D, r26t3_mu] using hMeq
  have hXU : Fp.X u.toNNReal ζ = A.X u.toNNReal ζ := hind (u.toNNReal)
  have hX0 : Fp.X (Real.toNNReal (0 : ℝ)) ζ = A.X (Real.toNNReal (0 : ℝ)) ζ :=
    hind (Real.toNNReal 0)
  have hEtaU := fp81s21_particleEmpField_eq_sqrt_pair p R A u ζ f
  have hEta0 := fp81s21_particleEmpField_eq_sqrt_pair p R A 0 ζ f
  rw [← hXU] at hEtaU
  rw [← hX0] at hEta0
  have hEta0' : fp81s21_particleEmpField R N A 0 ζ f =
      Real.sqrt N * (Whole.pair (Whole.empirical (Fp.X 0 ζ)) f -
        Whole.pair (r26t3_mu R 0) f) := by
    simpa using hEta0
  have hItoNoise := ht u hu
  have hScale :
      Real.sqrt N * (Real.sqrt (2 * D.invβ) / (N : ℝ)) =
        fp81s21_b6i_scale N p.β := by
    dsimp [D, quadraticGradientDyn, fp81s21_b6i_scale]
    ring
  have hScaledIto :
      Real.sqrt N * ((Real.sqrt (2 * D.invβ) / (N : ℝ)) *
        itoIntegral A.P Fp.ℱ Fp.Wc
          (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ) =
        fp81s21_particle_raw_testIto p A Fp f u ζ -
          fp81s21_particle_raw_testIto p A Fp f 0 ζ := by
    calc
      _ = (Real.sqrt N * (Real.sqrt (2 * D.invβ) / (N : ℝ))) *
          itoIntegral A.P Fp.ℱ Fp.Wc
            (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ := by ring
      _ = fp81s21_b6i_scale N p.β *
          itoIntegral A.P Fp.ℱ Fp.Wc
            (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ := by rw [hScale]
      _ = fp81s21_particle_raw_testIto p A Fp f u ζ -
          fp81s21_particle_raw_testIto p A Fp f 0 ζ := hItoNoise
  have hDiff :
      Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) f - Whole.pair (r26t3_mu R u) f =
        (Whole.pair (Whole.empirical (Fp.X 0 ζ)) f - Whole.pair (r26t3_mu R 0) f) +
          ((∫ v in Set.Icc (0 : ℝ) u, empWeak v) -
            ∫ v in Set.Icc (0 : ℝ) u, mfWeak v) +
          (Real.sqrt (2 * D.invβ) / (N : ℝ)) *
            itoIntegral A.P Fp.ℱ Fp.Wc
              (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ := by
    rw [hEmpEq, hMfEq]
    ring
  have hScaledDiff :
      Real.sqrt N * (Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) f -
          Whole.pair (r26t3_mu R u) f) =
        Real.sqrt N * (Whole.pair (Whole.empirical (Fp.X 0 ζ)) f -
          Whole.pair (r26t3_mu R 0) f) +
        Real.sqrt N * ((∫ v in Set.Icc (0 : ℝ) u, empWeak v) -
          ∫ v in Set.Icc (0 : ℝ) u, mfWeak v) +
        Real.sqrt N * ((Real.sqrt (2 * D.invβ) / (N : ℝ)) *
          itoIntegral A.P Fp.ℱ Fp.Wc
            (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ) := by
    rw [hDiff]
    ring
  rw [hEtaU, hEta0']
  calc
    Real.sqrt N * (Whole.pair (Whole.empirical (Fp.X u.toNNReal ζ)) f -
        Whole.pair (r26t3_mu R u) f) =
      Real.sqrt N * (Whole.pair (Whole.empirical (Fp.X 0 ζ)) f -
        Whole.pair (r26t3_mu R 0) f) +
      Real.sqrt N * ((∫ v in Set.Icc (0 : ℝ) u, empWeak v) -
        ∫ v in Set.Icc (0 : ℝ) u, mfWeak v) +
      Real.sqrt N * ((Real.sqrt (2 * D.invβ) / (N : ℝ)) *
        itoIntegral A.P Fp.ℱ Fp.Wc
          (HRS.MH.DualityRd.truncGradIntegrand T (fun _ => f) Fp.X) u ζ) := hScaledDiff
    _ = Real.sqrt N * (Whole.pair (Whole.empirical (Fp.X 0 ζ)) f -
        Whole.pair (r26t3_mu R 0) f) +
      (∫ v in Set.Icc (0 : ℝ) u, fp81s21_particle_raw_physicalDrift p A f v ζ) +
      (fp81s21_particle_raw_testIto p A Fp f u ζ -
        fp81s21_particle_raw_testIto p A Fp f 0 ζ) := by
      rw [hIeq, hScaledIto]

#print axioms HRS.Fp81.S21.fp81s21_particle_raw_drift_linearization
#print axioms HRS.Fp81.S21.fp81s21_particle_raw_compact_ito

end HRS.Fp81.S21
