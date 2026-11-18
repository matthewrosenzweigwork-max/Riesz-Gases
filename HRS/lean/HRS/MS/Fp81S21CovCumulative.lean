import HRS.MS.Fp81S21MovingInputs2
import HRS.MS.Fp81S21MovingHeat3
import HRS.MS.Fp81S21MovingHeat4
import HRS.MS.Fp81S21MovingMeas

/-!
# HRS S2.1(iii), packet 19c-i: full-horizon raw-η covariance cumulative

This file records the physical cumulative contract and proves the moving raw-field
covariance-integrand measurability stage.  The cumulative constructor is intentionally
left as a subsequent stage: its `IsR2L1F` input must use a measurable extension outside
the physical horizon while preserving the raw moving-reference field on `[0,H]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The raw fluctuation field centered at the actual moving reference `μ_v`. -/
def fp81s21_movingRawEtaField
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (ω : A.Ω) (v : ℝ) : (Euc p.d → ℝ) → ℝ :=
  s102_etaf (r26t3_mu R v) A.X ω v

/-- The exact physical common-telescope statement for the full-horizon raw-η
covariance cumulative of packet 19c-i.  Its projective tensor paths have a
single event for every admissible real interval, and the variation majorant is
integrable under the particle law. -/
def fp81s21_rawEtaCovarianceCumulativeSpec (p : Parameters) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ future : (H : ℝ) → ℝ →
          Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        fp81s21_moving_heat_full_clause p R future ∧
        ∀ a (ha : 0 ≤ a) N (hN : 2 ≤ N) (A : Particle R N),
          let H := a + p.T
          let B_H := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
          ∃ Fj : A.Ω → ℝ → projTensor B_H 2,
            (∀ ω, Fj ω 0 = 0) ∧
            (∀ᵐ ω ∂A.P, ∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
              IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
                (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
                (((Fj ω r - Fj ω q : projTensor B_H 2) : TensorDual B_H 2))) ∧
            (∀ᵐ ω ∂A.P, ContinuousOn (Fj ω) (Icc 0 H)) ∧
            (∀ᵐ ω ∂A.P, BoundedVariationOn (Fj ω) (Icc 0 H)) ∧
            ∃ Vf : A.Ω → ℝ, Integrable Vf A.P ∧
              ∀ᵐ ω ∂A.P, (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ Vf ω

/-- The packet-18b physical reference moment controls the exact weighted
moment of the moving measure `r26t3_mu R v` throughout the horizon. -/
theorem fp81s21_moving_eta_referenceMoment
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Mρ : ℝ, ∀ v ∈ Icc (0 : ℝ) H,
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
        (r26t3_mu R v) ∧
      (∫ x, jbracket x ^ ((p.d : ℝ) + 2) ∂(r26t3_mu R v)) ≤ Mρ := by
  obtain ⟨Mρ, hMρ⟩ := hphysical.reference_moment
  refine ⟨Mρ, fun v hv => ?_⟩
  obtain ⟨hhigh, hhighBound⟩ := hMρ v hv
  have hρ : HRS.Whole.IsProbDensity (R.ρ v) := (R.resulting.global H).density v hv
  have hPw : 0 ≤ (p.d : ℝ) + 2 := by positivity
  have hbase : Continuous fun x : Euc p.d => jbracket x := by
    unfold jbracket
    fun_prop
  have hpower : Continuous fun x : Euc p.d =>
      jbracket x ^ ((p.d : ℝ) + 2) := by
    exact hbase.rpow_const (fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')
  have hlowMeas : AEStronglyMeasurable
      (fun x : Euc p.d => R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2)) volume :=
    ((R.resulting.regular v hv.1).mul hpower).aestronglyMeasurable
  have hlow : Integrable
      (fun x : Euc p.d => R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2)) volume := by
    refine Integrable.mono' hhigh hlowMeas (Eventually.of_forall fun x => ?_)
    have hj : 1 ≤ jbracket x := HRS.MS.R2Poly.s95_one_le_jb x
    have hp : jbracket x ^ ((p.d : ℝ) + 2) ≤
        jbracket x ^ (2 * ((p.d : ℝ) + 2)) :=
      Real.rpow_le_rpow_of_exponent_le hj (by
        have hd : 0 ≤ (p.d : ℝ) := by positivity
        nlinarith)
    have hρx := hρ.nonneg x
    have hlower : 0 ≤ R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2) :=
      mul_nonneg hρx (Real.rpow_nonneg (by linarith [hj]) _)
    have hupper : 0 ≤ R.ρ v x * jbracket x ^ (2 * ((p.d : ℝ) + 2)) :=
      mul_nonneg hρx (Real.rpow_nonneg (by linarith [hj]) _)
    have hlowerNorm : ‖R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2)‖ =
        R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hlower]
    have hupperNorm : ‖R.ρ v x * jbracket x ^ (2 * ((p.d : ℝ) + 2))‖ =
        R.ρ v x * jbracket x ^ (2 * ((p.d : ℝ) + 2)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hupper]
    have hpointwise : R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2) ≤
        R.ρ v x * jbracket x ^ (2 * ((p.d : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hp hρx
    simpa only [hlowerNorm, hupperNorm] using hpointwise
  have hρmeas : Measurable (fun x : Euc p.d => ENNReal.ofReal (R.ρ v x)) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  have hρfinite : ∀ᵐ x ∂volume, ENNReal.ofReal (R.ρ v x) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hμint : Integrable
      (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2))
      (r26t3_mu R v) := by
    change Integrable _ (volume.withDensity fun x => ENNReal.ofReal (R.ρ v x))
    rw [integrable_withDensity_iff hρmeas hρfinite]
    have heq : (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 2) *
        (ENNReal.ofReal (R.ρ v x)).toReal) =
        fun x => R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2) := by
      funext x
      rw [ENNReal.toReal_ofReal (hρ.nonneg x)]
      ring
    rw [heq]
    exact hlow
  refine ⟨hμint, ?_⟩
  calc
    (∫ x, jbracket x ^ ((p.d : ℝ) + 2) ∂(r26t3_mu R v))
        = ∫ x, R.ρ v x * jbracket x ^ ((p.d : ℝ) + 2) :=
          HRS.MP.RdRem.mrr_integral_withDensityReal (R.ρ v)
            hρ.measurable hρ.nonneg _
    _ ≤ ∫ x, R.ρ v x * jbracket x ^ (2 * ((p.d : ℝ) + 2)) := by
      apply integral_mono hlow hhigh
      intro x
      have hj : 1 ≤ jbracket x := HRS.MS.R2Poly.s95_one_le_jb x
      have hp : jbracket x ^ ((p.d : ℝ) + 2) ≤
        jbracket x ^ (2 * ((p.d : ℝ) + 2)) :=
      Real.rpow_le_rpow_of_exponent_le hj (by
        have hd : 0 ≤ (p.d : ℝ) := by positivity
        nlinarith)
      exact mul_le_mul_of_nonneg_left hp (hρ.nonneg x)
    _ ≤ Mρ := hhighBound

/-- The packet-18b particle moment gives an integrable uniform expectation bound
for the empirical weighted moment at every physical time. -/
theorem fp81s21_moving_eta_particleMoment
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (hphysical : Fp81MovingPhysicalInputs R hN A H) :
    ∃ Cm : ℝ, ∀ v ∈ Icc (0 : ℝ) H,
      Integrable (fun ω => (N : ℝ)⁻¹ *
        ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ ((p.d : ℝ) + 2)) A.P ∧
      (∫ ω, (N : ℝ)⁻¹ *
        ∑ k : Fin N, jbracket (A.X v.toNNReal ω k) ^ ((p.d : ℝ) + 2)
        ∂A.P) ≤ Cm := by
  obtain ⟨Cm, hCm⟩ := hphysical.particle_moment
  have hstrong := A.strong H
  have hNpos : 0 < N := by omega
  have haMeas : Measurable fun x : Euc p.d =>
      jbracket x ^ ((p.d : ℝ) + 2) := by
    have hj : Continuous fun x : Euc p.d => jbracket x := by
      unfold jbracket
      fun_prop
    exact (hj.rpow_const (fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')).measurable
  have haNonneg : ∀ x : Euc p.d, 0 ≤ jbracket x ^ ((p.d : ℝ) + 2) :=
    fun x => Real.rpow_nonneg (by linarith [HRS.MS.R2Poly.s95_one_le_jb x]) _
  refine ⟨Cm, fun v hv => ?_⟩
  obtain ⟨hint, hbound⟩ := hCm v hv
  have hYmeas : Measurable (A.X v.toNNReal) := hstrong.adapted _
  have hmoment := HRS.MS.R2Interp.s102_empMoment hNpos A.P
    (A.X v.toNNReal) hYmeas haMeas haNonneg hint
  refine ⟨hmoment.1, ?_⟩
  rw [hmoment.2]
  exact hbound

/-- On each finite physical horizon, the raw η field with the moving reference
`r26t3_mu R v` satisfies the exact covariance-integrand measurability required
by the proved `r2_covariance_measure_proof`. -/
theorem fp81s21_moving_raw_eta_JIntegrandMeas
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → EucConfig p.d N) (ω : Ω)
    (hcz : ∀ k, Continuous fun t : ℝ≥0 => X t ω k) :
    R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (fun v => s102_etaf (r26t3_mu R v) X ω v) := by
  exact fp81s21_moving_eta_JIntegrandMeas p R hδ hδh hH hN X ω hcz

/-- The proved covariance-measure constructor turns a raw moving η field with
its two exact admissibility hypotheses into one projective cumulative path.
The interval specification is simultaneous for all admissible real intervals;
the variation estimate is still in its pre-`toReal` form. -/
theorem fp81s21_raw_eta_covariance_cumulative_of_L1F
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    (horb : R2OrbitSummable (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8))
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H)
    {Pw : ℝ} (hP : (p.d : ℝ) / 2 < Pw)
    {N : ℕ} (A : Particle R N) (ω : A.Ω)
    (hη : IsR2L1F (2 * p.d + 8) Pw H
      (fp81s21_movingRawEtaField p R A ω))
    (hηm : R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (fp81s21_movingRawEtaField p R A ω)) :
    ∃ K : ℝ,
      ∃ Jc : ℝ → projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2,
        Jc 0 = 0 ∧
        (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
            (((Jc r - Jc q : projTensor
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
        ContinuousOn Jc (Icc 0 H) ∧
        BoundedVariationOn Jc (Icc 0 H) ∧
        eVariationOn Jc (Icc 0 H) ≤
          ENNReal.ofReal K * ∫⁻ v in Icc (0 : ℝ) H,
            dualNormE (2 * p.d + 8) Pw
              (fp81s21_movingRawEtaField p R A ω v) := by
  classical
  let z := fp81s21_movingRawEtaField p R A ω
  obtain ⟨K, Jm, _, _, hmain⟩ :=
    HRS.MS.CovMeas.r2_covariance_measure_proof p.hd
      (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H hH
      (2 * p.d + 8) Pw hP horb hlin
  obtain ⟨hadd, hself, hcontinuous, hvariation, hvalue⟩ := hmain z hη hηm
  refine ⟨K, fun v => Jm z 0 v, ?_, ?_, ?_, ?_, ?_⟩
  · change Jm z 0 0 = 0
    exact hself 0
  · intro q r hq hqr hr
    have hsplit : Jm z 0 r = Jm z 0 q + Jm z q r :=
      hadd 0 q r (by norm_num) hq hqr hr
    have hdiff : Jm z 0 r - Jm z 0 q = Jm z q r := by
      rw [hsplit]
      abel
    change IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H z (Ioc q r)
      (((Jm z 0 r - Jm z 0 q : projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))
    rw [hdiff]
    exact hvalue q r hq hqr hr
  · exact hcontinuous
  · have hfinite : ENNReal.ofReal K *
        ∫⁻ v in Icc (0 : ℝ) H,
          dualNormE (2 * p.d + 8) Pw (z v) < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hη.2.2
    exact ne_top_of_le_ne_top hfinite.ne hvariation
  · exact hvariation

#print axioms HRS.Fp81.S21.fp81s21_movingRawEtaField
#print axioms HRS.Fp81.S21.fp81s21_rawEtaCovarianceCumulativeSpec
#print axioms HRS.Fp81.S21.fp81s21_moving_eta_referenceMoment
#print axioms HRS.Fp81.S21.fp81s21_moving_eta_particleMoment
#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_JIntegrandMeas
#print axioms HRS.Fp81.S21.fp81s21_raw_eta_covariance_cumulative_of_L1F

end HRS.Fp81.S21

end
