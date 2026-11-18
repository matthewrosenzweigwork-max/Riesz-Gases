import HRS.PDE.MovCAux8

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_init_tendsto (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hT : 0 ≤ T) (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν]
    (hfin : relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤) :
    (∀ n, relEntropy ν (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) ≠ ⊤) ∧
      Tendsto (fun n => (relEntropy ν (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)).toReal) atTop
        (𝓝 (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal) := by
  have hr : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hd : 1 ≤ d := b15_one_le_d D
  have hρ : IsProbDensity (ρ 0) := h.mf.density 0 hr
  have hcont : Continuous (ρ 0) := b15_continuous_of_isCk (h.ck 0 hr)
  haveI hμ : IsProbabilityMeasure (withDensityReal (ρ 0)) := isProb_withDensityReal hρ
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 h.pos_temp
  have hN1 : 1 ≤ N := by omega
  -- measurability of the singular energy
  obtain ⟨Bg, hBg⟩ := b15_periodicRiesz_lower D
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d D.s z + (Bg + 1) := fun z _ => by
    have := hBg z; linarith
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ 0 x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨hgR, -⟩ := rowOK_g_h hd D.s D.hs0 D.hsd (Bg + 1) hw 0 hMρ0 hρΛ
    (h := fun _ _ => 0) measurable_const (fun x y => by simp)
  have hFm : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d D.s) X
      (withDensityReal (ρ 0))) := measurable_modulatedEnergy hgR
  have hFnm : ∀ n, Measurable (fun X : Config d N => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X
      (withDensityReal (ρ 0))) := fun n =>
    measurable_modulatedEnergyKernel (movc_gReg_measurable hd D.hs0 D.hsd (M n)) _
  obtain ⟨c, hc⟩ := movc_energy_lower hd D.hs0 D.hsd hN1 hρ hcont (N := N)
  have hae := Repulsive.ae_notMem_collisionSet hd (rfl : withDensityReal (ρ 0) = withDensityReal (ρ 0)) hρ N
  have hlim : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ 0)),
      Tendsto (fun n => modulatedEnergyKernel (b15c_gReg d D.s (M n)) X (withDensityReal (ρ 0))) atTop
        (𝓝 (modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal (ρ 0)))) :=
    hae.mono fun X hX => movc_energy_tendsto hd D.hs0 D.hsd hρ hcont hM hM0 hX
  set a : ℝ := -D.invβ⁻¹ * N with ha
  have ha0 : a ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  set Pm : Measure (Config d N) := Measure.pi fun _ : Fin N => withDensityReal (ρ 0) with hPm
  set Fn : ℕ → Config d N → ℝ := fun n X =>
    modulatedEnergyKernel (b15c_gReg d D.s (M n)) X (withDensityReal (ρ 0)) with hFn
  set F : Config d N → ℝ := fun X => modulatedEnergyKernel (periodicRiesz d D.s) X
    (withDensityReal (ρ 0)) with hF
  obtain ⟨hZn, hZ, hZt⟩ := movc_gibbs_Z Pm a Fn F hFnm hFm c (fun n X => hc (M n) (hM0 n) X) hlim ha0
  set Zn : ℕ → ℝ := fun n => ∫ y, Real.exp (a * Fn n y) ∂Pm with hZndef
  set Z : ℝ := ∫ y, Real.exp (a * F y) ∂Pm with hZdef
  have hQn : ∀ n, movT_Q (b15c_gReg d D.s (M n)) D N ρ 0 =
      Pm.withDensity fun X => ENNReal.ofReal (Real.exp (a * Fn n X) / Zn n) := fun n => by
    unfold movT_Q modulatedGibbs gibbsNormalizer
    exact movc_smul_withDensity Pm (fun X => Real.exp (a * Fn n X)) (hZn n)
  have hQ : movT_Q (periodicRiesz d D.s) D N ρ 0 =
      Pm.withDensity fun X => ENNReal.ofReal (Real.exp (a * F X) / Z) := by
    unfold movT_Q modulatedGibbs gibbsNormalizer
    exact movc_smul_withDensity Pm (fun X => Real.exp (a * F X)) hZ
  haveI hQp : IsProbabilityMeasure (movT_Q (periodicRiesz d D.s) D N ρ 0) := by
    have hint : Integrable (fun y => Real.exp (a * F y)) Pm := by
      by_contra hni
      have := hZ
      rw [hZdef, integral_undef hni] at this
      exact lt_irrefl _ this
    refine ⟨?_⟩
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hint.div_const Z)
        (Eventually.of_forall fun X => (div_pos (Real.exp_pos _) hZ).le), integral_div]
    change ENNReal.ofReal (Z / Z) = 1
    rw [div_self hZ.ne']; simp
  haveI hQnp : ∀ n, IsProbabilityMeasure (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) :=
    fun n => movT_QReg_isProb D h (M n) hr
  obtain ⟨C, -, hC⟩ := exists_abs_bound hcont
  set I : ℕ → ℝ := fun n => ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s (M n) z| with hI
  have hIt : Tendsto I atTop (𝓝 0) := movc_gReg_L1_tendsto hd D.hs0 D.hsd hM hM0
  set cn : ℕ → ℝ := fun n => Z / Zn n * Real.exp (a * ((3 / 2) * (C * I n))) with hcn
  have hcnt : Tendsto cn atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => Z / Zn n) atTop (𝓝 (Z / Z)) :=
      (tendsto_const_nhds (x := Z)).div hZt hZ.ne'
    rw [div_self hZ.ne'] at h1
    have h2 : Tendsto (fun n => Real.exp (a * ((3 / 2) * (C * I n)))) atTop
        (𝓝 (Real.exp (a * ((3 / 2) * (C * 0))))) :=
      (Real.continuous_exp.tendsto _).comp
        ((((hIt.const_mul C).const_mul (3 / 2)).const_mul a))
    simp only [mul_zero, Real.exp_zero] at h2
    simpa using h1.mul h2
  have hcn0 : ∀ n, 0 < cn n := fun n => mul_pos (div_pos hZ (hZn n)) (Real.exp_pos _)
  have hle : ∀ n, ∀ᵐ X ∂Pm, cn n * (Real.exp (a * F X) / Z) ≤ Real.exp (a * Fn n X) / Zn n := by
    intro n
    filter_upwards [hae] with X hX
    have hdiff := movc_energy_diff_le hd D.hs0 D.hsd hρ hcont hC (hM0 n) hX hN1
    have h1 : a * ((3 / 2) * (C * I n)) + a * F X ≤ a * Fn n X := by
      have : Fn n X - F X ≤ (3 / 2) * (C * I n) := hdiff
      nlinarith
    have h2 : Real.exp (a * ((3 / 2) * (C * I n))) * Real.exp (a * F X) ≤ Real.exp (a * Fn n X) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 h1
    have hZn' := hZn n
    calc cn n * (Real.exp (a * F X) / Z)
        = (Real.exp (a * ((3 / 2) * (C * I n))) * Real.exp (a * F X)) / Zn n := by
          simp only [hcn]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right h2 hZn'.le
  have hw' : ∀ φ : Config d N → ℝ, Continuous φ → Tendsto (fun n =>
      ∫ x, φ x ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)) atTop
      (𝓝 (∫ x, φ x ∂(movT_Q (periodicRiesz d D.s) D N ρ 0))) := fun φ hφ =>
    movc_Q_tendsto_weak hN h hM hM0 hr hφ
  have := movc_klDiv_conv Pm (ν := ν) (Q := movT_Q (periodicRiesz d D.s) D N ρ 0)
    (Qn := fun n => movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)
    (fun X => Real.exp (a * F X) / Z) (fun n X => Real.exp (a * Fn n X) / Zn n)
    ((Real.measurable_exp.comp (measurable_const.mul hFm)).div_const _)
    (fun n => (Real.measurable_exp.comp (measurable_const.mul (hFnm n))).div_const _)
    (fun X => div_pos (Real.exp_pos _) hZ) (fun n X => div_pos (Real.exp_pos _) (hZn n))
    hQ hQn cn hcnt hcn0 hle hw' hfin
  exact this

end HRS
