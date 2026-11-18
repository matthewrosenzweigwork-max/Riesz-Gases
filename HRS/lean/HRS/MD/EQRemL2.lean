import HRS.MD.EQRemSetup
import HRS.Main.EqMargFinal
import HRS.Equilibrium.MarginalKernel

/-!
# EQ-REM (a), part 1: the `L²(μ_β)` bound of `ψ = H_{μ,φ} - H_{m_N,φ}`

`‖H_{μ,φ} - H_{m_N,φ}‖_{L²(μ)} ≤ C δ_N ‖φ‖_{C²}` (TeX L4029-4032): Schur/Young for the radial majorant of the pair kernel
and `equilibrium_marginal_L2` for `‖dm_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29

variable {d : ℕ} {s : ℝ}

/-- `∫⁻ ‖f‖ₑ² = ‖f‖_{L²}²`. -/
theorem eqrem_lintegral_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (μ := μ) (q := 2) (by norm_num)
  rw [eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.rpow_two] at h
  simpa using h

/-- A lintegral bound gives an `L²` bound. -/
theorem eqrem_eLpNorm_two_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {E : ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hE : 0 ≤ E) (h : ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal E) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt E) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofNat_ne_top hf, eLpNorm'_eq_lintegral_enorm]
  simp only [ENNReal.toReal_ofNat]
  have h2 : (∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ) ≤ ENNReal.ofReal E := by
    simpa only [ENNReal.rpow_two] using h
  calc (∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal E) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt E) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hE (by norm_num), Real.sqrt_eq_rpow]

/-- Pointwise bound of `ψ = H_μ - H_m` through the radial majorant. -/
theorem eqrem_psi_pointwise {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {m : Measure (Torus d)}
    [IsFiniteMeasure m] [IsFiniteMeasure (withDensityReal ρ)] (hmac : m ≪ withDensityReal ρ) {h : Torus d → Torus d → ℝ} (x : Torus d)
    (hIμ : Integrable (fun y => h x y) (withDensityReal ρ)) (hIm : Integrable (fun y => h x y) m)
    {A : ℝ} (hb : ∀ y, |h x y| ≤ A * (‖x - y‖ ^ (-s) + 1))
    (hhm : Measurable (fun y => h x y)) :
    ‖kernelField h (withDensityReal ρ) x - kernelField h m x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (A * (‖x - y‖ ^ (-s) + 1)) *
        ‖(1 - (m.rnDeriv (withDensityReal ρ) y).toReal) * ρ y‖ₑ := by
  set μ := withDensityReal ρ with hμ
  set f : Torus d → ℝ := fun y => (m.rnDeriv μ y).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv m μ).ennreal_toReal
  have e1 : ∫ y, h x y ∂m = ∫ y, f y * h x y ∂μ := (integral_toReal_rnDeriv_mul hmac).symm
  have e2 : Integrable (fun y => f y * h x y) μ := (integrable_toReal_rnDeriv_mul_iff hmac).2 hIm
  have e3 : kernelField h μ x - kernelField h m x = ∫ y, (1 - f y) * h x y ∂μ := by
    unfold kernelField
    rw [e1, ← integral_sub hIμ e2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  rw [e3]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hgm : Measurable fun y => ENNReal.ofReal (A * (‖x - y‖ ^ (-s) + 1)) * ‖1 - f y‖ₑ := by
    refine Measurable.mul ?_ (measurable_const.sub hfm).enorm
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    exact ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).add measurable_const
  calc ∫⁻ y, ‖(1 - f y) * h x y‖ₑ ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal (A * (‖x - y‖ ^ (-s) + 1)) * ‖1 - f y‖ₑ ∂μ := by
        refine lintegral_mono fun y => ?_
        rw [enorm_mul, mul_comm]
        refine mul_le_mul' ?_ le_rfl
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hb y)
    _ = ∫⁻ y, ENNReal.ofReal (A * (‖x - y‖ ^ (-s) + 1)) * ‖(1 - f y) * ρ y‖ₑ := by
        rw [hμ, withDensityReal, lintegral_withDensity_eq_lintegral_mul _
          (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ.measurable) hgm]
        refine lintegral_congr fun y => ?_
        simp only [Pi.mul_apply, enorm_mul]
        rw [Real.enorm_eq_ofReal_abs (ρ y), abs_of_nonneg (hρ.nonneg y)]
        ring


/-- **`L²(μ_β)` bound of `ψ = H_{μ,φ} - H_{m_N,φ}`**: `‖ψ‖²_{L²(μ)} ≤ C ‖φ‖²_{C²} δ_N²`, uniform in `β ∈ [β₋,β₊]`. -/
theorem eqrem_psi_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ Cψ : ℝ, 0 ≤ Cψ ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N → ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ →
      ∫⁻ x, ‖kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
          kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x‖ₑ ^ 2
          ∂(withDensityReal ρβ) ≤
        ENNReal.ofReal (Cψ * Torus.cbNorm 2 φ ^ 2 * deltaN d s N ^ 2) := by
  obtain ⟨Lam, hLam⟩ := EQStat.eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Cm, hCm0, hCm⟩ := Main.equilibrium_marginal_L2_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨A0, hA00, hAb⟩ := eqrem_pairKernel_bound hd hs0 hsd
  obtain ⟨C₁, hC₁, hL1⟩ := eqrem_kernel_L1 hd hs0 hsd
  have hrad := eqrem_radial_integrable hd hsd
  set K0 : ℝ := ∫ z : Torus d, (‖z‖ ^ (-s) + 1) with hK0
  have hK00 : 0 ≤ K0 := integral_nonneg fun z => add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one
  set Λ : ℝ := max Lam 0 with hΛdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  refine ⟨Λ ^ 2 * (A0 * K0) ^ 2 * Cm ^ 2, by positivity, ?_⟩
  intro β hβ ρβ hρ N hN φ hφ
  obtain ⟨hρs, hΛ', hP⟩ := hLam β hβ ρβ hρ
  have hΛ : ∀ x, ρβ x ≤ Λ := fun x => (hΛ' x).trans (le_max_left _ _)
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨Mp, hMp0, hMp⟩ := eqrem_marginal_le hd hs0 hsd V hV hβ0 hρ
  obtain ⟨hmac, hL2⟩ := hCm β hβ ρβ hρ N hN
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set μ := withDensityReal ρβ with hμdef
  set m := firstMarginal G with hmdef
  have hdens := hρs.density
  have hμvol : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := eqrem_mu_le_vol hΛ
  have hμfin : IsFiniteMeasure μ := Commutator.absConv_isFiniteMeasure hΛ
  have hmle : m ≤ ENNReal.ofReal Mp • μ := hMp N hN
  have hmfin : IsFiniteMeasure m := by
    refine ⟨?_⟩
    have h := Measure.le_iff'.1 hmle Set.univ
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
  have hmvol : m ≤ ENNReal.ofReal (Mp * Λ) • (volume : Measure (Torus d)) := by
    refine hmle.trans ?_
    calc ENNReal.ofReal Mp • μ ≤ ENNReal.ofReal Mp • (ENNReal.ofReal Λ • (volume : Measure (Torus d))) := by
          refine Measure.le_iff'.2 fun A => ?_
          have := Measure.le_iff'.1 hμvol A
          rw [Measure.smul_apply, smul_eq_mul] at this
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
          exact mul_le_mul' le_rfl this
      _ = ENNReal.ofReal (Mp * Λ) • (volume : Measure (Torus d)) := by
          rw [smul_smul, ENNReal.ofReal_mul hMp0]
  set L : ℝ := Torus.cbNorm 2 φ with hLdef
  have hL0 : 0 ≤ L := eqrem_cbNorm_nonneg 2 φ
  set A : ℝ := A0 * L with hAdef
  have hA0 : 0 ≤ A := mul_nonneg hA00 hL0
  set f : Torus d → ℝ := fun y => (m.rnDeriv μ y).toReal with hf
  have hfm : Measurable f := (Measure.measurable_rnDeriv m μ).ennreal_toReal
  set Fn : Torus d → ℝ := fun y => (1 - f y) * ρβ y with hFn
  have hFm : Measurable Fn := (measurable_const.sub hfm).mul hdens.measurable
  set k : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (A * (‖z‖ ^ (-s) + 1)) with hk
  have hkm : Measurable k := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
    exact (measurable_norm.pow_const _).add measurable_const
  -- pointwise bound of `ψ`
  have hpt : ∀ x : Torus d,
      ‖kernelField (pairKernel d s φ) μ x - kernelField (pairKernel d s φ) m x‖ₑ ≤ ∫⁻ y, k (x - y) * ‖Fn y‖ₑ := by
    intro x
    have hmeas : Measurable (fun y => pairKernel d s φ x y) :=
      (eqrem_pairKernel_meas hsd hφ).comp (measurable_const.prodMk measurable_id)
    exact eqrem_psi_pointwise hdens hmac x (hL1 φ hφ μ Λ hΛ0 hμvol x).1
      (hL1 φ hφ m (Mp * Λ) (mul_nonneg hMp0 hΛ0) hmvol x).1
      (fun y => by simpa [hAdef, mul_assoc] using hAb φ hφ x y) hmeas
  -- Young
  have hkint : ∫⁻ z, k z = ENNReal.ofReal (A * K0) := by
    have := ofReal_integral_eq_lintegral_ofReal (hrad.const_mul A)
      (Filter.Eventually.of_forall fun z => mul_nonneg hA0 (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) zero_le_one))
    rw [integral_const_mul] at this
    exact this.symm
  have hY := MarginalAux.young1 k Fn hkm hFm
  -- the `L²` norm of `Fn`
  have hF2 : ∫⁻ y, ‖Fn y‖ₑ ^ 2 ≤ ENNReal.ofReal Λ * ENNReal.ofReal (Cm * deltaN d s N) ^ 2 := by
    have hstep : ∫⁻ y, ‖Fn y‖ₑ ^ 2 ≤ ENNReal.ofReal Λ * ∫⁻ y, ‖f y - 1‖ₑ ^ 2 ∂μ := by
      have h1 : ∫⁻ y, ‖f y - 1‖ₑ ^ 2 ∂μ = ∫⁻ y, ENNReal.ofReal (ρβ y) * ‖f y - 1‖ₑ ^ 2 := by
        rw [hμdef, withDensityReal, lintegral_withDensity_eq_lintegral_mul _
          (f := fun x => ENNReal.ofReal (ρβ x)) (g := fun y => ‖f y - 1‖ₑ ^ 2)
          (ENNReal.measurable_ofReal.comp hdens.measurable)
          ((hfm.sub measurable_const).enorm.pow_const 2)]
        rfl
      rw [h1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun y => ?_
      have : ‖Fn y‖ₑ = ‖1 - f y‖ₑ * ENNReal.ofReal (ρβ y) := by
        simp only [hFn, enorm_mul]
        rw [Real.enorm_eq_ofReal_abs (ρβ y), abs_of_nonneg (hdens.nonneg y)]
      rw [this, mul_pow, enorm_sub_rev (1 : ℝ) (f y)]
      have hr : ENNReal.ofReal (ρβ y) ≤ ENNReal.ofReal Λ := ENNReal.ofReal_le_ofReal (hΛ y)
      calc ‖f y - 1‖ₑ ^ 2 * ENNReal.ofReal (ρβ y) ^ 2
          = (‖f y - 1‖ₑ ^ 2 * ENNReal.ofReal (ρβ y)) * ENNReal.ofReal (ρβ y) := by ring
        _ ≤ (‖f y - 1‖ₑ ^ 2 * ENNReal.ofReal (ρβ y)) * ENNReal.ofReal Λ := mul_le_mul' le_rfl hr
        _ = ENNReal.ofReal Λ * (ENNReal.ofReal (ρβ y) * ‖f y - 1‖ₑ ^ 2) := by ring
    refine hstep.trans (mul_le_mul' le_rfl ?_)
    have hsq := eqrem_lintegral_sq_eq (μ := μ) (f := fun y => f y - 1)
      (hfm.sub measurable_const).aestronglyMeasurable
    rw [hsq]
    exact pow_le_pow_left' hL2 2
  -- assemble
  have hδ0 : 0 ≤ deltaN d s N := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact (inv_nonneg.2 hN0.le).trans (MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega))
  calc ∫⁻ x, ‖kernelField (pairKernel d s φ) μ x - kernelField (pairKernel d s φ) m x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, ‖kernelField (pairKernel d s φ) μ x - kernelField (pairKernel d s φ) m x‖ₑ ^ 2
          ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) := lintegral_mono' hμvol le_rfl
    _ = ENNReal.ofReal Λ * ∫⁻ x, ‖kernelField (pairKernel d s φ) μ x - kernelField (pairKernel d s φ) m x‖ₑ ^ 2 := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Λ * ∫⁻ x, (∫⁻ y, k (x - y) * ‖Fn y‖ₑ) ^ 2 := by
        refine mul_le_mul' le_rfl (lintegral_mono fun x => ?_)
        exact pow_le_pow_left' (hpt x) 2
    _ ≤ ENNReal.ofReal Λ * ((∫⁻ z, k z) ^ 2 * ∫⁻ y, ‖Fn y‖ₑ ^ 2) := mul_le_mul' le_rfl hY
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal (A * K0) ^ 2 *
          (ENNReal.ofReal Λ * ENNReal.ofReal (Cm * deltaN d s N) ^ 2)) := by
        rw [hkint]; exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hF2)
    _ = ENNReal.ofReal (Λ ^ 2 * (A0 * K0) ^ 2 * Cm ^ 2 * L ^ 2 * deltaN d s N ^ 2) := by
        have e : Λ ^ 2 * (A0 * K0) ^ 2 * Cm ^ 2 * L ^ 2 * deltaN d s N ^ 2 =
            Λ * ((A * K0) ^ 2 * (Λ * (Cm * deltaN d s N) ^ 2)) := by
          simp only [hAdef]; ring
        rw [e, ENNReal.ofReal_mul hΛ0, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul hΛ0,
          ENNReal.ofReal_pow (mul_nonneg hA0 hK00), ENNReal.ofReal_pow (mul_nonneg hCm0.le hδ0)]

end HRS.MD.EQRem

end
