import HRS.MS.S113EndAux30
import HRS.MS.WrPressAux1
import HRS.MS.WrEntAux2

/-!
# S11.3 endpoint (worker S11X), part 31: S11.6 (a) for the Gaussian-bounded class: bounded negative-temperature normalizers

`s113x_X4_generic`: for the logarithmic kernel (`s = 0`), there are `a_* > 0` and `B` (depending only on `d, C₀, a₀`) such that every density
`0 ≤ ρ ≤ C₀ e^{-a₀|x|²}` of mass one satisfies `0 < K_{N,θ}(ρ) ` and `|log K_{N,θ}(ρ)| ≤ B` for `N ≥ 2`, `θ ∈ [-a_*, 0]`.
Upper bound: the abstract partition theorem `DGRHS.Attractive.source_uniform_partition` (Delgadino-Gvalani-Rosenzweig Thm 2.6) with the row estimate
`r2_log_row_whole`; lower bound: Jensen with `N E[F_N] = -½∬g`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s113x_ang_le (x : Euc d) : q33b_ang x ≤ 1 + ‖x‖ := by
  unfold q33b_ang
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x]

set_option maxHeartbeats 1600000 in
theorem s113x_X4_generic (hd : 1 ≤ d) (C₀ a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∃ astar B : ℝ, 0 < astar ∧ 0 ≤ B ∧ ∀ ρ : Euc d → ℝ, Measurable ρ →
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₀ * Real.exp (-a₀ * ‖x‖ ^ 2)) → ∫ x, ρ x = 1 →
      ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (-astar) (0 : ℝ),
        0 < HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ (HRS.Whole.withDensityReal ρ))| ≤ B := by
  obtain ⟨ε₁, Crow, hε₁, hWall⟩ := HRS.Whole.r2_log_row_whole hd C₀ a₀ ha₀
  set C₁ : ℝ := max C₀ 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  set C1 : ℝ := max 1 Crow * ε₁⁻¹ with hC1def
  have hC1pos : 0 < C1 := by
    have : 0 < max 1 Crow := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  set κ : ℝ := DGRHS.Attractive.attractiveMomentConstant with hκdef
  have hκ : 0 < κ := DGRHS.Attractive.attractiveMomentConstant_pos
  set astar : ℝ := min (1 / 2) (1 / (2 * (κ * C1))) with hastar
  have hastar0 : 0 < astar := lt_min (by norm_num) (by positivity)
  set Φi : ℝ := ∫ x : Euc d, q33b_Phi C₁ a₀ x with hΦi
  have hΦi0 : 0 ≤ Φi := integral_nonneg fun x => q33b_Phi_nonneg hC₁ x
  set M0 : ℝ := 2 * Φi with hM0
  set Kq : ℝ := s113x_Kq d C₁ a₀ with hKq
  have hKq0 : 0 ≤ Kq := s113x_Kq_nonneg
  set Gb : ℝ := 2 * (2 * Kq) + 2 * M0 with hGb
  have hGb0 : 0 ≤ Gb := by positivity
  set Mom : ℝ := ∫ x : Euc d, (1 + ‖x‖) * (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) with hMom
  have hMom0 : 0 ≤ Mom := integral_nonneg fun x => by positivity
  set U : ℝ := Real.exp (astar * (Gb / 2)) * 2 * Real.sqrt (Real.exp M0 * Mom) with hU
  refine ⟨astar, |Real.log U| + astar * (Gb / 2), hastar0, by positivity, fun ρ hm hρ hint N hN θ hθ => ?_⟩
  have hρ' : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2) := fun x =>
    ⟨(hρ x).1, (hρ x).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)⟩
  obtain ⟨hprob, hrows, hconvm, hpot, hG2⟩ := s113x_X4_facts hd hC₁ ha₀ hm hρ' hint
  obtain ⟨hmomI, hmomB⟩ := s113x_moment_integrable hC₁ ha₀ hm hρ' hd
  obtain ⟨hI, -, hfact⟩ := hWall ρ hm hρ hint
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set g := rieszKernel d 0 with hg
  have hev : ∀ z : Euc d, g (-z) = g z := fun z => rieszKernel_neg z
  have hN0 : 0 < N := by omega
  set β : ℝ := -θ with hβdef
  have hβ0 : 0 ≤ β := by have := hθ.2; linarith
  have hβa : β ≤ astar := by have := hθ.1; linarith
  have hβhalf : β ≤ 1 / 2 := hβa.trans (min_le_left _ _)
  have hsmall' : β * (κ * C1) ≤ 1 / 2 := by
    calc β * (κ * C1) ≤ (1 / (2 * (κ * C1))) * (κ * C1) :=
          mul_le_mul_of_nonneg_right (hβa.trans (min_le_right _ _)) (by positivity)
      _ = 1 / 2 := by field_simp
  have hsmall : β * (κ * C1) < 1 := by linarith
  have hWm : StronglyMeasurable (Function.uncurry (s113x_Wk g)) :=
    ((HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) 0).neg).stronglyMeasurable
  have hWi : Integrable (Function.uncurry (s113x_Wk g)) (μ.prod μ) := hI.neg
  -- row factorial moments
  have hmeasC : Measurable (fun p : Euc d × Euc d => DGRHS.centeredKernel μ (s113x_Wk g) p.1 p.2) :=
    (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ (Function.uncurry (s113x_Wk g)) hWm).measurable
  have hE2 : HRS.Whole.energyPairing g μ μ = 2 * ((1 / 2) * ∫ z, HRS.Whole.convMeasure g μ z ∂μ) := by
    show ∫ x, HRS.Whole.convMeasure g μ x ∂μ = _
    ring
  have hrowFM : DGRHS.Attractive.RowFactorialMoments μ (fun p => DGRHS.centeredKernel μ (s113x_Wk g) p.1 p.2) C1 := by
    refine DGRHS.Attractive.rowFactorialMoments_of_lintegral μ _ hmeasC C1 hC1pos.le ?_
    intro p hp y
    have h1 := hfact p y
    have h2 : ∀ x, |DGRHS.centeredKernel μ (s113x_Wk g) x y| =
        |g (x - y) - HRS.Whole.convMeasure g μ x - HRS.Whole.convMeasure g μ y +
          2 * ((1 / 2) * ∫ z, HRS.Whole.convMeasure g μ z ∂μ)| := fun x => by
      rw [s113x_centeredKernel_eq hev hI, abs_neg, hE2]
    simp only [h2]
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmax : 1 ≤ max 1 Crow := le_max_left _ _
    have hpow : max 1 Crow ≤ (max 1 Crow) ^ p := by
      calc max 1 Crow = (max 1 Crow) ^ 1 := (pow_one _).symm
        _ ≤ (max 1 Crow) ^ p := pow_le_pow_right₀ hmax hp
    have hf : (0 : ℝ) ≤ p.factorial := Nat.cast_nonneg _
    have hi : 0 ≤ ε₁⁻¹ ^ p := by positivity
    calc Crow * (p.factorial : ℝ) * ε₁⁻¹ ^ p = (Crow * ε₁⁻¹ ^ p) * p.factorial := by ring
      _ ≤ ((max 1 Crow) ^ p * ε₁⁻¹ ^ p) * p.factorial := by
          gcongr
          exact (le_max_right _ _).trans hpow
      _ = C1 ^ p * p.factorial := by rw [hC1def, mul_pow]
  -- tail integrability
  have hpotm : Measurable (DGRHS.potential μ (s113x_Wk g)) := by
    have : DGRHS.potential μ (s113x_Wk g) = fun x => -HRS.Whole.convMeasure g μ x := funext s113x_potential_eq
    rw [this]; exact hconvm.neg
  have hexpB : ∀ x, Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x) ≤ Real.exp M0 * (1 + ‖x‖) := fun x => by
    rw [s113x_potential_eq]
    have h1 : 2 * β * (-HRS.Whole.convMeasure g μ x) ≤ 2 * β * (q33b_ell x + M0) :=
      mul_le_mul_of_nonneg_left (hpot x) (by linarith)
    have h2 : Real.exp (2 * β * (q33b_ell x + M0)) = q33b_ang x ^ (2 * β) * Real.exp (2 * β * M0) := by
      rw [mul_add, Real.exp_add]
      congr 1
      unfold q33b_ell
      rw [Real.rpow_def_of_pos (q33b_ang_pos x)]
      congr 1; ring
    have h3 : q33b_ang x ^ (2 * β) ≤ q33b_ang x := by
      calc q33b_ang x ^ (2 * β) ≤ q33b_ang x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (q33b_ang_ge_one x) (by linarith)
        _ = q33b_ang x := Real.rpow_one _
    have h4 : Real.exp (2 * β * M0) ≤ Real.exp M0 := Real.exp_le_exp.2 (by
      have : 0 ≤ M0 := by positivity
      nlinarith)
    calc Real.exp (2 * β * (-HRS.Whole.convMeasure g μ x)) ≤ Real.exp (2 * β * (q33b_ell x + M0)) :=
          Real.exp_le_exp.2 h1
      _ = q33b_ang x ^ (2 * β) * Real.exp (2 * β * M0) := h2
      _ ≤ (1 + ‖x‖) * Real.exp M0 := mul_le_mul (h3.trans (s113x_ang_le x)) h4 (Real.exp_pos _).le (by positivity)
      _ = Real.exp M0 * (1 + ‖x‖) := mul_comm _ _
  have htail : Integrable (fun x => Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x)) μ := by
    refine (hmomI.const_mul (Real.exp M0)).mono' (hpotm.const_mul (2 * β) |>.exp).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hexpB x
  have htailB : ∫ x, Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x) ∂μ ≤ Real.exp M0 * Mom := by
    calc ∫ x, Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x) ∂μ ≤ ∫ x, Real.exp M0 * (1 + ‖x‖) ∂μ :=
          integral_mono htail (hmomI.const_mul _) hexpB
      _ = Real.exp M0 * ∫ x, (1 + ‖x‖) ∂μ := integral_const_mul _ _
      _ ≤ Real.exp M0 * Mom := mul_le_mul_of_nonneg_left hmomB (Real.exp_pos _).le
  obtain ⟨hint', hbd⟩ := DGRHS.Attractive.source_uniform_partition (μ := μ) (s113x_Wk g) hWm hWi
    (s113x_Wk_symm hev) C1 β hrowFM hβ0 hsmall htail N hN0
  -- the normalizer as the DGRHS partition function
  have hfun : (fun X : EucConfig d N => Real.exp (-θ * N * HRS.Whole.modulatedEnergy g X μ)) =
      fun X => Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ (s113x_Wk g) p.1 p.2) (DGRHS.potential μ (s113x_Wk g))
        (DGRHS.interactionEnergy μ (s113x_Wk g)) N X) := by
    funext X
    rw [s113x_modulatedEnergy_eq hev hI hN0 X]
    congr 1
    simp only [hβdef]
    ring
  have hKeq : HRS.Whole.gibbsNormalizer g N θ μ = ∫ X : EucConfig d N, Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ (s113x_Wk g) p.1 p.2)
        (DGRHS.potential μ (s113x_Wk g)) (DGRHS.interactionEnergy μ (s113x_Wk g)) N X) ∂(Measure.pi fun _ : Fin N => μ) := by
    unfold HRS.Whole.gibbsNormalizer
    rw [← hfun]
  have hKint : Integrable (fun X : EucConfig d N => Real.exp (-θ * N * HRS.Whole.modulatedEnergy g X μ))
      (Measure.pi fun _ : Fin N => μ) := by
    rw [hfun]; exact hint'
  have hKpos : 0 < HRS.Whole.gibbsNormalizer g N θ μ := by
    rw [hKeq]; exact integral_exp_pos hint'
  -- upper bound
  have hIE : |DGRHS.interactionEnergy μ (s113x_Wk g)| ≤ Gb / 2 := by
    rw [s113x_interactionEnergy_eq hI, abs_mul]
    have : |(-(1 / 2) : ℝ)| = 1 / 2 := by norm_num
    rw [this]
    have := hG2
    simp only [hGb, hKq, hM0, hΦi]
    linarith [abs_nonneg (HRS.Whole.energyPairing g μ μ)]
  have hKle : HRS.Whole.gibbsNormalizer g N θ μ ≤ U := by
    rw [hKeq]
    refine hbd.trans ?_
    have h1 : Real.exp (β * |DGRHS.interactionEnergy μ (s113x_Wk g)|) ≤ Real.exp (astar * (Gb / 2)) :=
      Real.exp_le_exp.2 (mul_le_mul hβa hIE (abs_nonneg _) hastar0.le)
    have h2 : Real.sqrt (2 / (1 - (β * (κ * C1)) ^ 2)) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have hp : 0 ≤ β * (κ * C1) := by positivity
      have : (β * (κ * C1)) ^ 2 ≤ 1 / 4 := by nlinarith
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have h3 : Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x) ∂μ) ≤
        Real.sqrt (Real.exp M0 * Mom) := Real.sqrt_le_sqrt htailB
    have hp1 : 0 ≤ Real.sqrt (2 / (1 - (β * (κ * C1)) ^ 2)) := Real.sqrt_nonneg _
    have hp2 : 0 ≤ Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x) ∂μ) := Real.sqrt_nonneg _
    calc Real.exp (β * |DGRHS.interactionEnergy μ (s113x_Wk g)|) *
          Real.sqrt (2 / (1 - (β * (κ * C1)) ^ 2)) *
          Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ (s113x_Wk g) x) ∂μ)
        ≤ Real.exp (astar * (Gb / 2)) * 2 * Real.sqrt (Real.exp M0 * Mom) := by gcongr
      _ = U := rfl
  -- lower bound by Jensen
  have hok : HRS.MS.Wr.Wr8Ok μ (fun x y => g (x - y)) :=
    ⟨HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) 0, hrows, hI⟩
  have hFint := HRS.MS.Wr.wr8_integrable_modEnergyE (N := N) hok
  have hFmean := HRS.MS.Wr.wr8_integral_mul_modEnergyE (N := N) hok (by omega)
  have hpair : ∫ p : Euc d × Euc d, g (p.1 - p.2) ∂(μ.prod μ) = HRS.Whole.energyPairing g μ μ := by
    unfold HRS.Whole.energyPairing
    rw [integral_prod _ hI]
  have hmod : ∀ X : EucConfig d N, -θ * (N : ℝ) * HRS.Whole.modulatedEnergy g X μ =
      (-θ) * ((N : ℝ) * HRS.MS.Wr.modEnergyE (fun x y => g (x - y)) X μ) := fun X => by
    show -θ * (N : ℝ) * HRS.MS.Wr.modEnergyE (fun x y => g (x - y)) X μ = _
    ring
  have hφint : Integrable (fun X : EucConfig d N => -θ * (N : ℝ) * HRS.Whole.modulatedEnergy g X μ)
      (Measure.pi fun _ : Fin N => μ) := by
    simp only [hmod]
    exact (hFint.const_mul (N : ℝ)).const_mul (-θ)
  have hjensen := (convexOn_exp).map_integral_le (μ := Measure.pi fun _ : Fin N => μ) Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _) hφint (by exact hKint)
  have hφmean : ∫ X : EucConfig d N, -θ * (N : ℝ) * HRS.Whole.modulatedEnergy g X μ ∂(Measure.pi fun _ : Fin N => μ) =
      θ * HRS.Whole.energyPairing g μ μ / 2 := by
    simp only [hmod]
    rw [integral_const_mul, hFmean, hpair]
    ring
  rw [hφmean] at hjensen
  have hKlow : Real.exp (θ * HRS.Whole.energyPairing g μ μ / 2) ≤ HRS.Whole.gibbsNormalizer g N θ μ := by
    simpa [HRS.Whole.gibbsNormalizer, Function.comp] using hjensen
  refine ⟨hKpos, ?_⟩
  have hlogU : Real.log (HRS.Whole.gibbsNormalizer g N θ μ) ≤ |Real.log U| :=
    (Real.log_le_log hKpos hKle).trans (le_abs_self _)
  have hlow : θ * HRS.Whole.energyPairing g μ μ / 2 ≤ Real.log (HRS.Whole.gibbsNormalizer g N θ μ) := by
    have := Real.log_le_log (Real.exp_pos _) hKlow
    rwa [Real.log_exp] at this
  have hθG : |θ * HRS.Whole.energyPairing g μ μ / 2| ≤ astar * (Gb / 2) := by
    rw [abs_div, abs_mul]
    have h1 : |θ| ≤ astar := by rw [abs_of_nonpos hθ.2]; linarith [hθ.1]
    have h2 : |HRS.Whole.energyPairing g μ μ| ≤ Gb := by simpa [hGb, hKq, hM0, hΦi] using hG2
    have : |θ| * |HRS.Whole.energyPairing g μ μ| ≤ astar * Gb := mul_le_mul h1 h2 (abs_nonneg _) hastar0.le
    rw [show |(2 : ℝ)| = 2 by norm_num]
    linarith
  rw [abs_le]
  constructor
  · have := (abs_le.1 hθG).1
    have h0 := abs_nonneg (Real.log U)
    linarith
  · have h0 : 0 ≤ astar * (Gb / 2) := by positivity
    linarith

end HRS.MS.S113BD

end
