import HRS.MS.Fp81S21CovCumulative2
import HRS.MS.R2InterpAux127

/-!
# HRS S2.1(iii), packet 19c-i: moving raw eta is horizon-L1F almost surely

This stage assembles the pointwise weighted fluctuation estimate and time
measurability for the raw eta field with its actual moving reference measure.
The extension is zero away from the physical horizon, as required by `IsR2L1F`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- For almost every particle realization, the raw moving-reference eta field,
extended by zero away from `[0,H]`, satisfies the exact `IsR2L1F` contract. -/
theorem fp81s21_moving_raw_eta_horizonL1F_ae
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A H) :
    ∀ᵐ ω ∂A.P,
      IsR2L1F (2 * p.d + 8) ((p.d : ℝ) + 2) H
        (fp81s21_horizonFieldExtension H
          (fp81s21_movingRawEtaField p R A ω)) := by
  classical
  let Pw : ℝ := (p.d : ℝ) + 2
  let r : ℕ := 2 * p.d + 8
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hPw0 : 0 ≤ Pw := by dsimp [Pw]; positivity
  have hr : (p.d : ℝ) / 2 < r := by
    dsimp [r]
    push_cast
    have hd : 2 ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith
  have hN0 : 0 < N := by omega
  obtain ⟨Mρ, hρmom⟩ :=
    fp81s21_moving_eta_referenceMoment p R hN A hphysical
  obtain ⟨C0, hC0, hηbound⟩ :=
    s102_eta_bound_unif hd1 hPw0 r hr hN0
  have hρmom0 : 0 ≤ Mρ := by
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
    have hjb : ∀ x : Euc p.d, 0 ≤ jbracket x := by
      intro x
      unfold jbracket
      positivity
    have hnonneg : 0 ≤
        ∫ x : Euc p.d, jbracket x ^ Pw ∂(r26t3_mu R 0) :=
      integral_nonneg (fun x => Real.rpow_nonneg (hjb x) Pw)
    exact le_trans hnonneg (hρmom 0 h0).2
  have hstrong := A.strong H
  have hXcont : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous fun t : ℝ≥0 => A.X t ω k := hstrong.cont
  filter_upwards [hXcont] with ω hω
  have hcz : ∀ k : Fin N, Continuous fun t : ℝ≥0 => A.X t ω k := hω
  let η : ℝ → (Euc p.d → ℝ) → ℝ :=
    fp81s21_movingRawEtaField p R A ω
  let ηext : ℝ → (Euc p.d → ℝ) → ℝ :=
    fp81s21_horizonFieldExtension H η
  have hρnonneg : ∀ v ∈ Icc (0 : ℝ) H, ∀ x : Euc p.d, 0 ≤ R.ρ v x := by
    intro v hv x
    exact ((R.resulting.global H).density v hv).nonneg x
  have hρjoint : Measurable
      (fun q : Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2) :=
    hphysical.density_joint
  have hρnonneg' : ∀ v : Icc (0 : ℝ) H, ∀ x : Euc p.d,
      0 ≤ R.ρ v.1 x := fun v x => hρnonneg v.1 v.2 x
  have hlin : ∀ u ∈ Icc (0 : ℝ) H,
      (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
        ηext u (f + g) = ηext u f + ηext u g) ∧
      (∀ c f, IsR2WeightedTest r Pw f →
        ηext u (c • f) = c * ηext u f) ∧
      ∃ M : ℝ, ∀ f, IsR2WeightedTest r Pw f →
        |ηext u f| ≤ M * (weightedSobolevE r Pw f).toReal := by
    intro u hu
    have hμint := (hρmom u hu).1
    have hz := s102_Z_fluct hd1 hPw0 r hr hN0
      (A.X u.toNNReal ω) (r26t3_mu R u) hμint (Real.sqrt N)
    have heq : ηext u =
        (fun f => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical (A.X u.toNNReal ω)) f -
            HRS.Whole.pair (r26t3_mu R u) f)) := by
      funext f
      simp [ηext, η, fp81s21_horizonFieldExtension, hu,
        fp81s21_movingRawEtaField, HRS.MS.R2Interp.s102_etaf]
    rw [heq]
    exact ⟨hz.add, hz.smul, hz.bdd⟩
  have hmeas : ∀ f, IsR2WeightedTest r Pw f → Measurable fun u => ηext u f := by
    intro f hf
    let μpair : Icc (0 : ℝ) H → ℝ := fun v =>
      HRS.Whole.pair (r26t3_mu R v.1) f
    have hμpair : Measurable μpair := by
      have hfjoint : Measurable
          (fun q : Icc (0 : ℝ) H × Euc p.d => f q.2) :=
        hf.1.continuous.measurable.comp measurable_snd
      have hIntegral := fp81s21_moving_spatial_integral_meas
        (ρ := fun v : Icc (0 : ℝ) H => R.ρ v.1)
        hρjoint hρnonneg' (f := fun _ x => f x) hfjoint
      change Measurable (fun v : Icc (0 : ℝ) H =>
        ∫ x, f x ∂(HRS.Whole.withDensityReal (R.ρ v.1))) at hIntegral
      have heq : μpair = fun v : Icc (0 : ℝ) H =>
          ∫ x, f x ∂(HRS.Whole.withDensityReal (R.ρ v.1)) := by
        funext v
        simp [μpair, HRS.Whole.pair, r26t3_mu]
      rw [heq]
      exact hIntegral
    have hpath : ∀ k : Fin N,
        Measurable fun v : Icc (0 : ℝ) H => A.X v.1.toNNReal ω k := by
      intro k
      exact (((hcz k).comp continuous_real_toNNReal).measurable.comp
        continuous_subtype_val.measurable)
    let empPair : Icc (0 : ℝ) H → ℝ := fun v =>
      HRS.Whole.pair (HRS.Whole.empirical (A.X v.1.toNNReal ω)) f
    have hemp : Measurable empPair := by
      have hempEq : empPair = fun v : Icc (0 : ℝ) H =>
          (N : ℝ)⁻¹ * ∑ k : Fin N, f (A.X v.1.toNNReal ω k) := by
        funext v
        simpa [empPair] using
          (HRS.Whole.pair_empirical hN0 (A.X v.1.toNNReal ω) f)
      rw [hempEq]
      refine measurable_const.mul
        (Finset.measurable_sum _ fun k _ => ?_)
      exact hf.1.continuous.measurable.comp (hpath k)
    have hinside : Measurable (fun v : Icc (0 : ℝ) H =>
        Real.sqrt N * (empPair v - μpair v)) :=
      measurable_const.mul (hemp.sub hμpair)
    have hglobal : Measurable (fun u : ℝ =>
        if hu : u ∈ Icc (0 : ℝ) H then
          Real.sqrt N * (empPair ⟨u, hu⟩ - μpair ⟨u, hu⟩)
        else 0) :=
      hinside.dite measurable_const measurableSet_Icc
    have heq : (fun u => ηext u f) = fun u : ℝ =>
        if hu : u ∈ Icc (0 : ℝ) H then
          Real.sqrt N * (empPair ⟨u, hu⟩ - μpair ⟨u, hu⟩)
        else 0 := by
      funext u
      by_cases hu : u ∈ Icc (0 : ℝ) H
      · simp [ηext, η, fp81s21_horizonFieldExtension, hu,
          empPair, μpair, fp81s21_movingRawEtaField, s102_etaf,
          HRS.Whole.pair_empirical hN0]
      · simp [ηext, η, fp81s21_horizonFieldExtension, hu]
    rw [heq]
    exact hglobal
  let empMoment : ℝ → ℝ := fun v => (N : ℝ)⁻¹ *
    ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw
  have hj : Continuous fun x : Euc p.d => jbracket x ^ Pw := by
    have hb : Continuous fun x : Euc p.d => jbracket x := by
      unfold jbracket
      fun_prop
    exact hb.rpow_const (fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')
  have hempMomentCont : ContinuousOn empMoment (Icc (0 : ℝ) H) := by
    have hc : Continuous fun v : ℝ => (N : ℝ)⁻¹ *
        ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ Pw := by
      refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
      exact hj.comp ((hcz k).comp continuous_real_toNNReal)
    exact hc.continuousOn
  obtain ⟨Bω, hBω⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hempMomentCont
  let Mω : ℝ := Real.sqrt N * C0 * (max Bω 0 + Mρ)
  have hMω0 : 0 ≤ Mω := by
    dsimp [Mω]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC0.le)
      (add_nonneg (le_max_right Bω 0) hρmom0)
  have hmeta : ∀ v ∈ Icc (0 : ℝ) H,
      s102_Meta C0 Pw (r26t3_mu R v) (A.X v.toNNReal ω) ≤ Mω := by
    intro v hv
    have hq : empMoment v ≤ max Bω 0 := by
      dsimp [empMoment]
      exact (le_abs_self _).trans ((hBω v hv).trans (le_max_left _ _))
    have hμ := hρmom v hv
    have hqnonneg : 0 ≤ empMoment v := by
      dsimp [empMoment]
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ =>
        Real.rpow_nonneg (by
          unfold jbracket
          positivity) Pw)
    have hsum : empMoment v +
        ∫ x, jbracket x ^ Pw ∂(r26t3_mu R v) ≤ max Bω 0 + Mρ := by
      have hμ' : ∫ x, jbracket x ^ Pw ∂(r26t3_mu R v) ≤ Mρ := hμ.2
      exact add_le_add hq hμ'
    have hcoef : 0 ≤ Real.sqrt N * C0 := mul_nonneg (Real.sqrt_nonneg _) hC0.le
    dsimp [s102_Meta, empMoment, Mω]
    exact mul_le_mul_of_nonneg_left hsum hcoef
  have hdual : ∀ v : ℝ,
      dualNormE r Pw (ηext v) ≤ ENNReal.ofReal Mω := by
    intro v
    by_cases hv : v ∈ Icc (0 : ℝ) H
    · have hηb : ∀ f, IsR2WeightedTest r Pw f →
          |ηext v f| ≤ Mω * (weightedSobolevE r Pw f).toReal := by
        intro f hf
        have hbound := hηbound (r26t3_mu R v) (hρmom v hv).1
          (A.X v.toNNReal ω) f hf
        have hmeta' := hmeta v hv
        have hbase := hbound.trans (mul_le_mul_of_nonneg_right hmeta'
          (ENNReal.toReal_nonneg))
        simpa [ηext, η, fp81s21_horizonFieldExtension, hv,
          fp81s21_movingRawEtaField, HRS.MS.R2Interp.s102_etaf] using hbase
      exact s102_dualNormE_le hMω0 hηb
    · have hz : ηext v = 0 := by
        funext f
        simp [ηext, fp81s21_horizonFieldExtension, hv]
      rw [hz]
      have hzero : dualNormE r Pw (0 : (Euc p.d → ℝ) → ℝ) = 0 := by
        unfold dualNormE
        simp
      rw [hzero]
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hMω0
  have hconst : (∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal Mω) < ⊤ := by
    rw [lintegral_const]
    have hmeasure : volume (Icc (0 : ℝ) H) < ⊤ := measure_Icc_lt_top
    have hrestrict : (volume.restrict (Icc (0 : ℝ) H)) Set.univ =
        volume (Icc (0 : ℝ) H) := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
    rw [hrestrict]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmeasure
  have hfin : (∫⁻ v in Icc (0 : ℝ) H, dualNormE r Pw (ηext v)) < ⊤ := by
    calc
      _ ≤ ∫⁻ v in Icc (0 : ℝ) H, ENNReal.ofReal Mω :=
        lintegral_mono fun v => hdual v
      _ < ⊤ := hconst
  exact ⟨hlin, hmeas, hfin⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_horizonL1F_ae

end HRS.Fp81.S21

end
