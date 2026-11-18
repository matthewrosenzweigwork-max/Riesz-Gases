import HRS.MS.WsPrepI2

/-!
# S21T packet 3: the Gibbs initial comparison (`β₀ > 0`) for the window start `bw`, given the static bundle at `μ₀`

* `S21iStatic`: the static bundle at the initial reference `μ₀ = ρ⁰ dx` for the modulated Gibbs law `P = ℚ_{N,β₀}(μ₀)`: linear variance
  bound, marginal bias `|ν(f) - μ₀(f)| ≤ ‖f‖_∞ C_s δ_N` and the static field conclusion (exactly centred, `ν = firstMarginal P`);
  this is what the merged S4.7 (`tilt_static`) proves, for a FIXED perturbation `ψ`.  `S21iTiltClass` is the version with constants
  uniform over the admissible class `‖εψ‖_{C_b^{100d+1001}} + ‖ε√ρ_β ψ‖_Σ ≤ ε_*` that S2.1 (ii) needs (see the handoff, defect D5).
* `s21i_nu_prob`, `s21i_particle_coord`, `s21i_shift`, `s21i_w1_shift`, `s21i_smooth_shift`: reference-generic forms of the stationary
  packet-H lemmas (first marginal, coordinate second moments of the particle feature law, mean-field centring shift `√N C_s δ_N S`).
* `s21i_gibbs`: for the window start `bw` the law of `K_bw` under `ℚ_{N,β₀}(μ₀)` is within `C(√N δ_N + √δ_N)` (smooth) and
  `C(√N δ_N + δ_N^{3/20})` (`W_1`) of `γ₀ = Φ_σ_* γ`, `γ` the Gaussian of the susceptibility covariance of the window tests, uniformly in `bw`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

/-- The static bundle at the initial reference. -/
structure S21iStatic (d : ℕ) (s : ℝ) (N : ℕ) (β₀ : ℝ) (μ0 : Measure (Euc d)) (J : ℕ) (Cst Cs : ℝ) : Prop where
  prob : IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ μ0)
  exch : HRS.Whole.IsExchangeable (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ μ0)
  linear : ∀ f : Euc d → ℝ, MemLp f 2 μ0 →
    evariance (HRS.Whole.linStat f) (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ μ0) ≤
      ENNReal.ofReal (Cs / N * ∫ x, f x ^ 2 ∂μ0)
  bias : ∀ f : Euc d → ℝ, Measurable f → ∀ Bf : ℝ, (∀ x, |f x| ≤ Bf) →
    |HRS.Whole.pair (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ μ0)) f -
        HRS.Whole.pair μ0 f| ≤ Bf * (Cs * HRS.deltaN d s N)
  static : ∀ φ : ℕ → Euc d → ℝ, IsSummableFeatureFamily J φ → ∀ γ : Measure SeqL2,
    IsCenteredGaussianSeq γ (fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) μ0 β₀ (φ i) (φ j)) →
    StaticFieldConclusion d s N (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ μ0)
      (HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ μ0)) J φ γ Cst

/-- The tilt class: the static bundle at `(1+εψ)ρ_β` with constants uniform over the admissible perturbations (all `N ≥ 2`). -/
def S21iTiltClass (d : ℕ) (s a β β₀ : ℝ) (J : ℕ) (εstar : ℝ) : Prop :=
  ∃ Cst Cs : ℝ, 0 ≤ Cst ∧ 0 ≤ Cs ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
    IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ N : ℕ, 2 ≤ N →
      S21iStatic d s N β₀ (HRS.Whole.withDensityReal (perturbedDensity ρβ ε ψ)) J Cst Cs

theorem s21i_nu_prob {N : ℕ} (hN : 2 ≤ N) {P : Measure (EucConfig d N)} (hP : IsProbabilityMeasure P) :
    IsProbabilityMeasure (HRS.Whole.firstMarginal P) := by
  have : HRS.Whole.firstMarginal P = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
    unfold HRS.Whole.firstMarginal; rw [dif_pos (by omega)]
  rw [this]
  constructor
  rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
  simp

/-- Coordinate second moments of the exactly centred particle feature law. -/
theorem s21i_particle_coord {μ0 : Measure (Euc d)} [IsProbabilityMeasure μ0] {Cs : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hCs : 0 ≤ Cs) {P : Measure (EucConfig d N)} [IsProbabilityMeasure P]
    (hexch : HRS.Whole.IsExchangeable P)
    (hlin : ∀ f : Euc d → ℝ, Measurable f → MemLp f 2 μ0 →
      evariance (HRS.Whole.linStat f) P ≤ ENNReal.ofReal (Cs / N * ∫ x, f x ^ 2 ∂μ0))
    {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) (k : ℕ) :
    ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂(P.map (featureVec φ (HRS.Whole.firstMarginal P))) ≤
      ENNReal.ofReal (Cs * cbNorm J (φ k) ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  haveI hν : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := s21i_nu_prob hN inferInstance
  have hfm : Measurable (featureVec φ (HRS.Whole.firstMarginal P) : EucConfig d N → SeqL2) :=
    S45.s45_feature_measurable hN1 hφ
  set f := φ k with hf
  set B := cbNorm J f with hB
  have hfb : ∀ x, |f x| ≤ B := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 k) x
    rwa [Real.norm_eq_abs] at this
  have hfm2 : MemLp f 2 μ0 := HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 k)
  have hfmeas : Measurable f := (hφ.1 k).1.continuous.measurable
  have hlin' := hlin f hfmeas hfm2
  have hmeas : Measurable fun v : SeqL2 => ENNReal.ofReal (SeqL2.coord v k ^ 2) :=
    ENNReal.measurable_ofReal.comp ((s21h_continuous_coord k).pow 2).measurable
  rw [lintegral_map hmeas hfm]
  have hEl : ∫ X, linStat f X ∂P = HRS.Whole.pair (HRS.Whole.firstMarginal P) f :=
    HRS.Whole.S78.s78_integral_linStat hN1 hexch hfmeas hfb
  have hcoord : ∀ X : EucConfig d N, SeqL2.coord (featureVec φ (HRS.Whole.firstMarginal P) X) k =
      Real.sqrt N * (linStat f X - ∫ X', linStat f X' ∂P) := by
    intro X
    unfold featureVec
    rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN1 hφ X), hEl]
    rfl
  have hev : ∀ X : EucConfig d N, ENNReal.ofReal (SeqL2.coord (featureVec φ (HRS.Whole.firstMarginal P) X) k ^ 2) =
      ENNReal.ofReal N * ‖linStat f X - ∫ X', linStat f X' ∂P‖ₑ ^ 2 := by
    intro X
    rw [hcoord, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    congr 1
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [hev]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hlin'' : ∫⁻ X, ‖linStat f X - ∫ X', linStat f X' ∂P‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (Cs / N * ∫ x, f x ^ 2 ∂μ0) := hlin'
  refine (mul_le_mul' le_rfl hlin'').trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfb 0)
  have hI : ∫ x, f x ^ 2 ∂μ0 ≤ B ^ 2 := by
    calc ∫ x, f x ^ 2 ∂μ0 ≤ ∫ _x, B ^ 2 ∂μ0 := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_const _)
            (ae_of_all _ fun x => ?_)
          exact (sq_abs (f x)).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (hfb x) 2)
      _ = B ^ 2 := by simp
  rw [← ENNReal.ofReal_mul hN0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (N : ℝ) * (Cs / N * ∫ x, f x ^ 2 ∂μ0) = Cs * ∫ x, f x ^ 2 ∂μ0 := by field_simp
    _ ≤ Cs * B ^ 2 := mul_le_mul_of_nonneg_left hI hCs

/-- The mean-field centring shift: `‖Y_N - X_N‖_{ℓ²} ≤ √N B_s S`. -/
theorem s21i_shift {μ0 : Measure (Euc d)} [IsProbabilityMeasure μ0] {N : ℕ} (hN : 2 ≤ N)
    {P : Measure (EucConfig d N)} [IsProbabilityMeasure P] {J : ℕ} {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {Bs : ℝ}
    (hbias : ∀ f : Euc d → ℝ, Measurable f → ∀ Bf : ℝ, (∀ x, |f x| ≤ Bf) →
      |HRS.Whole.pair (HRS.Whole.firstMarginal P) f - HRS.Whole.pair μ0 f| ≤ Bf * Bs) (X : EucConfig d N) :
    ‖featureVec φ μ0 X - featureVec φ (HRS.Whole.firstMarginal P) X‖ ≤
      Real.sqrt N * Bs * featureSum J φ := by
  have hN1 : 1 ≤ N := by omega
  haveI hν : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := s21i_nu_prob hN inferInstance
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hb : Summable fun j => Real.sqrt N * Bs * cbNorm J (φ j) := hφ.2.mul_left _
  have h1 := S45.s45_norm_le_tsum (z := featureVec φ μ0 X - featureVec φ (HRS.Whole.firstMarginal P) X) hb
    (fun j => by
      have e1 : SeqL2.coord (featureVec φ μ0 X) j =
          Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) - HRS.Whole.pair μ0 (φ j)) := by
        unfold featureVec
        rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN1 hφ X)]
      have e2 : SeqL2.coord (featureVec φ (HRS.Whole.firstMarginal P) X) j =
          Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) -
            HRS.Whole.pair (HRS.Whole.firstMarginal P) (φ j)) := by
        unfold featureVec
        rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN1 hφ X)]
      have e3 : SeqL2.coord (featureVec φ μ0 X - featureVec φ (HRS.Whole.firstMarginal P) X) j =
          SeqL2.coord (featureVec φ μ0 X) j - SeqL2.coord (featureVec φ (HRS.Whole.firstMarginal P) X) j := rfl
      rw [e3, e1, e2]
      have hbj : ∀ x, |φ j x| ≤ cbNorm J (φ j) := fun x => by
        have := HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 j) x
        rwa [Real.norm_eq_abs] at this
      have hb1 := hbias (φ j) (hφ.1 j).1.continuous.measurable (cbNorm J (φ j)) hbj
      have : Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) - HRS.Whole.pair μ0 (φ j)) -
          Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (φ j) -
            HRS.Whole.pair (HRS.Whole.firstMarginal P) (φ j)) =
          Real.sqrt N * (HRS.Whole.pair (HRS.Whole.firstMarginal P) (φ j) - HRS.Whole.pair μ0 (φ j)) := by
        ring
      rw [this, abs_mul, abs_of_nonneg hsN]
      calc Real.sqrt N * |HRS.Whole.pair (HRS.Whole.firstMarginal P) (φ j) - HRS.Whole.pair μ0 (φ j)|
          ≤ Real.sqrt N * (cbNorm J (φ j) * Bs) := mul_le_mul_of_nonneg_left hb1 hsN
        _ = _ := by ring)
  refine h1.trans (le_of_eq ?_)
  rw [tsum_mul_left]
  unfold featureSum
  ring

section Shift

variable {Ω : Type*} [MeasurableSpace Ω] {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]

/-- `W_1` between the push-forwards of two random elements of `E` at distance `≤ B`, through a bounded linear map. -/
theorem s21i_w1_shift (ι : E →L[ℝ] X) (P : Measure Ω) [IsProbabilityMeasure P] {f g : Ω → E}
    (hf : Measurable f) (hg : Measurable g) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ zz, ‖f zz - g zz‖ ≤ B) :
    wassersteinE 1 ((P.map f).map ι) ((P.map g).map ι) ≤ ENNReal.ofReal (‖ι‖ * B) := by
  have hιm : Measurable ι := ι.continuous.measurable
  rw [Measure.map_map hιm hf, Measure.map_map hιm hg]
  have h := HRS.wassersteinE_le_of_coupling P 1 le_rfl (fun zz => ι (f zz)) (fun zz => ι (g zz))
    (hιm.comp hf).aemeasurable (hιm.comp hg).aemeasurable
  have key : ∫⁻ zz, ENNReal.ofReal ‖ι (f zz) - ι (g zz)‖ ∂P ≤ ENNReal.ofReal (‖ι‖ * B) := by
    calc ∫⁻ zz, ENNReal.ofReal ‖ι (f zz) - ι (g zz)‖ ∂P ≤ ∫⁻ _zz, ENNReal.ofReal (‖ι‖ * B) ∂P := by
          refine lintegral_mono fun zz => ENNReal.ofReal_le_ofReal ?_
          rw [← map_sub]
          exact (ι.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hB zz) (norm_nonneg _))
      _ = ENNReal.ofReal (‖ι‖ * B) := by simp
  refine h.trans ?_
  simpa only [Real.rpow_one, div_one, ENNReal.rpow_one] using key

theorem s21i_smooth_shift (ι : E →L[ℝ] X) (P : Measure Ω) [IsProbabilityMeasure P] {f g : Ω → E}
    (hf : Measurable f) (hg : Measurable g) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ zz, ‖f zz - g zz‖ ≤ B) :
    smoothDist 2 ((P.map f).map ι) ((P.map g).map ι) ≤ ‖ι‖ * B := by
  have hιm : Measurable ι := ι.continuous.measurable
  haveI : IsProbabilityMeasure (P.map f) := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (P.map g) := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure ((P.map f).map ι) :=
    (Measure.isProbabilityMeasure_map_iff hιm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure ((P.map g).map ι) :=
    (Measure.isProbabilityMeasure_map_iff hιm.aemeasurable).2 inferInstance
  have h := s21i_w1_shift ι P hf hg hB0 hB
  have h1 := smoothDist_one_le_wasserstein ((P.map f).map ι) ((P.map g).map ι)
  have h2 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _) hB0)).1 (h1.trans h)
  exact (smoothDist_succ_le 1 _ _).trans h2

end Shift

set_option maxHeartbeats 3200000 in
/-- The Gibbs initial comparison at the window start `bw` (`β₀ > 0`), constants uniform in everything but the data
`(d, s, T, C_orb, C_st, C_s)`. -/
theorem s21i_gibbs (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β₀ : ℝ} (hβ₀ : 0 < β₀) {T : ℝ} (hT : 0 < T)
    {Corb Cst Cs : ℝ} (hCorb : 0 ≤ Corb) (hCst : 0 ≤ Cst) (hCs : 0 ≤ Cs) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (C : WholeCoeff d), S21iOrb d T C Corb →
      ∀ (ρ0 : Euc d → ℝ), HRS.Whole.IsProbDensity ρ0 → ∀ M L : ℝ, (∀ x, ρ0 x ≤ M) →
      (s = 0 → HasLogMoment2 (HRS.Whole.withDensityReal ρ0) L) → ∀ N : ℕ, 2 ≤ N →
      S21iStatic d s N β₀ (HRS.Whole.withDensityReal ρ0) (4 * d + 42) Cst Cs → ∀ bw : ℝ, 0 ≤ bw →
      ∃ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 ∧
        (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
          (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ0) β₀
            (propagatorW C 0 (bw + ts i) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
            (propagatorW C 0 (bw + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))).PosSemidef ∧
          γ0.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i =>
              OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
            multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
              (HRS.Whole.withDensityReal ρ0) β₀
              (propagatorW C 0 (bw + ts i) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
              (propagatorW C 0 (bw + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) ∧
        smoothDist 2 ((HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal ρ0)).map
            (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal ρ0) bw)) γ0 ≤
          Cg * (Real.sqrt N * HRS.deltaN d s N + Real.sqrt (HRS.deltaN d s N)) ∧
        wassersteinE 1 ((HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal ρ0)).map
            (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal ρ0) bw)) γ0 ≤
          ENNReal.ofReal (Cg * (Real.sqrt N * HRS.deltaN d s N + HRS.deltaN d s N ^ ((3 : ℝ) / 20))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨σ⟩ := s11p_exists_equiv (d := d)
  have hγ0 : 5 * (d : ℝ) / 4 < 3 * (d : ℝ) + 30 := by linarith
  obtain ⟨K, τ₀, hK, hτ₀, hbox⟩ := s21h_box_osc hd1 σ hγ0 (fun k => s21iW d Corb (σ k))
    (fun k => s21i_W_nonneg hCorb (σ k)) (A := Corb) (fun k => by
      have e : s21iB d (σ k).2 = oscEigenvalue d (σ k).2 ^ (-(3 * (d : ℝ) + 30)) := by
        unfold s21iB; congr 1; push_cast; ring
      unfold s21iW; rw [e]; exact le_of_eq (by ring))
  set cJ : ℝ := s11p_cJ T with hcJ
  have hcJ0 : 0 < cJ := s11p_cJ_pos T
  set S0 : ℝ := s21iS0 d Corb with hS0def
  have hS00 : 0 ≤ S0 := tsum_nonneg fun q => s21i_W_nonneg hCorb q
  set Cm : ℝ := max Cs 4 with hCm
  have hCm4 : 4 ≤ Cm := le_max_right _ _
  have hCm0 : 0 ≤ Cm := by linarith
  set C' : ℝ := max Cst 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set τ : ℝ := Real.sqrt Cm * τ₀ with hτ
  have hτ0 : 0 ≤ τ := mul_nonneg (Real.sqrt_nonneg _) hτ₀
  set A1 : ℝ := cJ * (Cs * S0) with hA1
  set A2 : ℝ := max 1 (cJ ^ 2) * (C' * (S0 + S0 ^ 2)) with hA2
  set A3 : ℝ := cJ * (2 * τ + 4 * Real.sqrt K + C' * S0 + C' * S0 ^ 2) with hA3
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hA30 : 0 ≤ A3 := by positivity
  refine ⟨max A1 (max A2 A3), le_max_of_le_left hA10, ?_⟩
  intro C horb ρ0 hρ0 M L hM hL N hN hstat bw hbw
  have hN1 : 1 ≤ N := by omega
  haveI hμ0 : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ0) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
  obtain ⟨D, hD, hDw⟩ := s21i_orb_data hd1 horb bw hbw
  have hU := s21i_series_of_orb hT horb hbw D hD
  obtain ⟨hφ, hSle, hcbw⟩ := s21i_family hd1 horb hbw D hD hDw σ
  set φ : ℕ → Euc d → ℝ := fun j => D.f (σ j) with hφdef
  have hJ : (d : ℝ) / 2 + 2 < ((4 * d + 42 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨-, γ, hγ⟩ := S45.exists_gaussian_feature_proof hd hs0 hsd (4 * d + 42) hJ ρ0 hρ0 M hM β₀ hβ₀ φ hφ L hL
  haveI hGg : IsGaussian γ := hγ.1.1
  set Φ := s21gPhi σ hT ((wholeSpaceIndex d : ℕ) : ℝ) with hΦ
  have hΦn : ‖Φ‖ ≤ cJ := s21gPhi_norm_le σ hT _
  set P := HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal ρ0) with hP
  haveI hPp : IsProbabilityMeasure P := hstat.prob
  haveI hν : IsProbabilityMeasure (HRS.Whole.firstMarginal P) := s21i_nu_prob hN hPp
  have hfmν : Measurable (featureVec φ (HRS.Whole.firstMarginal P) : EucConfig d N → SeqL2) :=
    S45.s45_feature_measurable hN1 hφ
  have hfm0 : Measurable (featureVec φ (HRS.Whole.withDensityReal ρ0) : EucConfig d N → SeqL2) :=
    S45.s45_feature_measurable hN1 hφ
  have hpath : ∀ x : EucConfig d N, s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal ρ0) bw x =
      Φ (featureVec φ (HRS.Whole.withDensityReal ρ0) x) := fun x => s21i_path_eq hT bw D hU σ hφ _ hN1 x
  have hstatic := hstat.static φ hφ γ hγ
  have hδ0 : 0 < HRS.deltaN d s N := s21_deltaN_pos hs0 hsd N hN1
  have hδ1 : HRS.deltaN d s N ≤ 1 := s21_deltaN_le_one hs0 hsd N hN1
  set δ : ℝ := HRS.deltaN d s N with hδ
  have hsqN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsqδ : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  set S : ℝ := featureSum (4 * d + 42) φ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hSS0 : S ≤ S0 := hSle
  set Bsh : ℝ := Real.sqrt N * (Cs * δ) * S with hBsh
  have hBsh0 : 0 ≤ Bsh := by positivity
  have hdiff : ∀ x : EucConfig d N, ‖featureVec φ (HRS.Whole.withDensityReal ρ0) x -
      featureVec φ (HRS.Whole.firstMarginal P) x‖ ≤ Bsh := fun x => s21i_shift hN hφ (Bs := Cs * δ) hstat.bias x
  have hmapeq : P.map (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal ρ0) bw) =
      (P.map (featureVec φ (HRS.Whole.withDensityReal ρ0))).map Φ := by
    rw [Measure.map_map Φ.continuous.measurable hfm0]
    congr 1
    funext x
    exact hpath x
  have hγpm : IsProbabilityMeasure (γ.map Φ) :=
    (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  haveI hY1 : IsProbabilityMeasure (P.map (featureVec φ (HRS.Whole.withDensityReal ρ0))) :=
    (Measure.isProbabilityMeasure_map_iff hfm0.aemeasurable).2 inferInstance
  haveI hX1 : IsProbabilityMeasure (P.map (featureVec φ (HRS.Whole.firstMarginal P))) :=
    (Measure.isProbabilityMeasure_map_iff hfmν.aemeasurable).2 inferInstance
  haveI hY2 : IsProbabilityMeasure ((P.map (featureVec φ (HRS.Whole.withDensityReal ρ0))).map Φ) :=
    (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  haveI hX2 : IsProbabilityMeasure ((P.map (featureVec φ (HRS.Whole.firstMarginal P))).map Φ) :=
    (Measure.isProbabilityMeasure_map_iff Φ.continuous.measurable.aemeasurable).2 inferInstance
  refine ⟨γ.map Φ, hγpm, s21i_fdd hT hU σ hφ hd1 hs0 hsd hρ0 hM hL hβ₀ hγ, ?_, ?_⟩
  · rw [hmapeq]
    obtain ⟨-, -, hsm, -⟩ := hstatic
    have hY := s21i_smooth_shift Φ P hfm0 hfmν hBsh0 hdiff
    have hX := HRS.Main.smoothDist_map_clm_le Φ 2 (P.map (featureVec φ (HRS.Whole.firstMarginal P))) γ
    have hst : smoothDist 2 (P.map (featureVec φ (HRS.Whole.firstMarginal P))) γ ≤
        Cst * (S + S ^ 2) * Real.sqrt δ := hsm
    have htri := smoothDist_triangle 2 ((P.map (featureVec φ (HRS.Whole.withDensityReal ρ0))).map Φ)
      ((P.map (featureVec φ (HRS.Whole.firstMarginal P))).map Φ) (γ.map Φ)
    have hn : max 1 (‖Φ‖ ^ 2) ≤ max 1 (cJ ^ 2) :=
      max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hΦn 2)
    have t1 : ‖Φ‖ * Bsh ≤ A1 * (Real.sqrt N * δ) := by
      calc ‖Φ‖ * Bsh ≤ cJ * Bsh := mul_le_mul_of_nonneg_right hΦn hBsh0
        _ = cJ * (Real.sqrt N * (Cs * δ) * S) := rfl
        _ ≤ cJ * (Real.sqrt N * (Cs * δ) * S0) := by gcongr
        _ = A1 * (Real.sqrt N * δ) := by rw [hA1]; ring
    have t2 : max 1 (‖Φ‖ ^ 2) * smoothDist 2 (P.map (featureVec φ (HRS.Whole.firstMarginal P))) γ ≤
        A2 * Real.sqrt δ := by
      have hS2 : S + S ^ 2 ≤ S0 + S0 ^ 2 := by
        have := pow_le_pow_left₀ hS0 hSS0 2
        linarith
      calc _ ≤ max 1 (cJ ^ 2) * (Cst * (S + S ^ 2) * Real.sqrt δ) :=
            mul_le_mul hn hst (smoothDist_nonneg 2 _ _) (by positivity)
        _ ≤ max 1 (cJ ^ 2) * (C' * (S0 + S0 ^ 2) * Real.sqrt δ) := by
            gcongr
            exact le_max_left _ _
        _ = A2 * Real.sqrt δ := by rw [hA2]; ring
    have hA1' : A1 ≤ max A1 (max A2 A3) := le_max_left _ _
    have hA2' : A2 ≤ max A1 (max A2 A3) := (le_max_left _ _).trans (le_max_right _ _)
    calc _ ≤ smoothDist 2 ((P.map (featureVec φ (HRS.Whole.withDensityReal ρ0))).map Φ)
          ((P.map (featureVec φ (HRS.Whole.firstMarginal P))).map Φ) +
          smoothDist 2 ((P.map (featureVec φ (HRS.Whole.firstMarginal P))).map Φ) (γ.map Φ) := htri
      _ ≤ A1 * (Real.sqrt N * δ) + A2 * Real.sqrt δ := add_le_add (hY.trans t1) (hX.trans t2)
      _ ≤ max A1 (max A2 A3) * (Real.sqrt N * δ + Real.sqrt δ) := by
          have h1 := mul_le_mul_of_nonneg_right hA1' (mul_nonneg hsqN hδ0.le)
          have h2 := mul_le_mul_of_nonneg_right hA2' hsqδ
          nlinarith
  · rw [hmapeq]
    -- the exactly centred law against the Gaussian
    have hcb0 : ∀ k, 0 ≤ cbNorm (4 * d + 42) (φ k) := fun k => HRS.MS.Tc5.tc5_cb_nonneg _ _
    have hw0 : ∀ k, 0 ≤ s21iW d Corb (σ k) := fun k => s21i_W_nonneg hCorb (σ k)
    have hWσ : Summable fun k => s21iW d Corb (σ k) := (Equiv.summable_iff σ).2 (s21i_W_summable hd1 Corb)
    have hsc0 : ∀ k, 0 ≤ Cm * s21iW d Corb (σ k) ^ 2 := fun k => by positivity
    have hsum : Summable fun k => Cm * s21iW d Corb (σ k) ^ 2 :=
      (S45.s45_summable_sq hw0 hWσ).mul_left Cm
    have hcbw' : ∀ k, cbNorm (4 * d + 42) (φ k) ^ 2 ≤ s21iW d Corb (σ k) ^ 2 := fun k =>
      pow_le_pow_left₀ (hcb0 k) (hcbw k) 2
    have hsμ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂(P.map (featureVec φ (HRS.Whole.firstMarginal P))) ≤
        ENNReal.ofReal (Cm * s21iW d Corb (σ k) ^ 2) := fun k =>
      (s21i_particle_coord (μ0 := HRS.Whole.withDensityReal ρ0) hN hCs hstat.exch (fun f _ hf => hstat.linear f hf) hφ k).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_left _ _) (hcbw' k) (sq_nonneg _) hCm0))
    have hsγ : ∀ k, ∫⁻ v, ENNReal.ofReal (SeqL2.coord v k ^ 2) ∂γ ≤ ENNReal.ofReal (Cm * s21iW d Corb (σ k) ^ 2) :=
      fun k => (s21i_gauss_coord hd1 hs0 hsd hρ0 hM hL hβ₀ hφ hγ k).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul hCm4 (hcbw' k) (sq_nonneg _) hCm0))
    have hbox' : ∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
        ∑' k : ℕ, (if k ∈ I then 0 else Cm * s21iW d Corb (σ k) ^ 2) ≤ τ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
      intro Q hQ1
      obtain ⟨I, hI, hT'⟩ := hbox Q hQ1
      refine ⟨I, hI, ?_⟩
      have e : (∑' k : ℕ, (if k ∈ I then 0 else Cm * s21iW d Corb (σ k) ^ 2)) =
          Cm * ∑' k : ℕ, (if k ∈ I then 0 else s21iW d Corb (σ k) ^ 2) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        split_ifs <;> simp
      rw [e, hτ, mul_pow, Real.sq_sqrt hCm0, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hT' hCm0
    have hwX := s21h_init_w1_feat Φ hN1 P (HRS.Whole.firstMarginal P) hφ hγ.1 (le_max_left Cst 0)
      hC'0 hstatic hδ0 hδ1 hK hτ0 (fun k => Cm * s21iW d Corb (σ k) ^ 2) hsc0 hsum hsμ hsγ hbox'
    have hwY := s21i_w1_shift Φ P hfm0 hfmν hBsh0 hdiff
    have htri := wassersteinE_triangle 1 le_rfl ((P.map (featureVec φ (HRS.Whole.withDensityReal ρ0))).map Φ)
      ((P.map (featureVec φ (HRS.Whole.firstMarginal P))).map Φ) (γ.map Φ)
    refine htri.trans ?_
    have t1 : ‖Φ‖ * Bsh ≤ A1 * (Real.sqrt N * δ) := by
      calc ‖Φ‖ * Bsh ≤ cJ * Bsh := mul_le_mul_of_nonneg_right hΦn hBsh0
        _ = cJ * (Real.sqrt N * (Cs * δ) * S) := rfl
        _ ≤ cJ * (Real.sqrt N * (Cs * δ) * S0) := by gcongr
        _ = A1 * (Real.sqrt N * δ) := by rw [hA1]; ring
    have hd3 : 0 ≤ δ ^ ((3 : ℝ) / 20) := Real.rpow_nonneg hδ0.le _
    have t3 : ‖Φ‖ * ((2 * τ + 4 * Real.sqrt K + C' * S + C' * S ^ 2) * δ ^ ((3 : ℝ) / 20)) ≤
        A3 * δ ^ ((3 : ℝ) / 20) := by
      have hS2 : S ^ 2 ≤ S0 ^ 2 := pow_le_pow_left₀ hS0 hSS0 2
      calc _ ≤ cJ * ((2 * τ + 4 * Real.sqrt K + C' * S + C' * S ^ 2) * δ ^ ((3 : ℝ) / 20)) :=
            mul_le_mul_of_nonneg_right hΦn (by positivity)
        _ ≤ cJ * ((2 * τ + 4 * Real.sqrt K + C' * S0 + C' * S0 ^ 2) * δ ^ ((3 : ℝ) / 20)) := by
            gcongr
        _ = A3 * δ ^ ((3 : ℝ) / 20) := by rw [hA3]; ring
    have hA1' : A1 ≤ max A1 (max A2 A3) := le_max_left _ _
    have hA3' : A3 ≤ max A1 (max A2 A3) := (le_max_right _ _).trans (le_max_right _ _)
    have hfin : ‖Φ‖ * Bsh + ‖Φ‖ * ((2 * τ + 4 * Real.sqrt K + C' * S + C' * S ^ 2) * δ ^ ((3 : ℝ) / 20)) ≤
        max A1 (max A2 A3) * (Real.sqrt N * δ + δ ^ ((3 : ℝ) / 20)) := by
      have h1 := mul_le_mul_of_nonneg_right hA1' (mul_nonneg hsqN hδ0.le)
      have h2 := mul_le_mul_of_nonneg_right hA3' hd3
      nlinarith
    calc _ ≤ ENNReal.ofReal (‖Φ‖ * Bsh) + ENNReal.ofReal (‖Φ‖ * ((2 * τ + 4 * Real.sqrt K + C' * S +
          C' * S ^ 2) * δ ^ ((3 : ℝ) / 20))) := add_le_add hwY hwX
      _ = ENNReal.ofReal (‖Φ‖ * Bsh + ‖Φ‖ * ((2 * τ + 4 * Real.sqrt K + C' * S + C' * S ^ 2) *
          δ ^ ((3 : ℝ) / 20))) := by
          rw [ENNReal.ofReal_add (mul_nonneg (norm_nonneg _) hBsh0) (by positivity)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

end HRS.MS.S21
