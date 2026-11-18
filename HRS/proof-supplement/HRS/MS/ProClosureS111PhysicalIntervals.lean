import HRS.MS.ProClosureS111ChartInterval
import HRS.MS.ProClosureS111PhysicalChartFields
import HRS.MS.ProClosureS111FieldMoments
import HRS.MS.ProClosureS111PairedFieldDecay
import HRS.MS.S111K4J02
import HRS.MS.R2ChaosAux37

/-!
Actual random interval responses for the physical paired evolution.

The chart, interval operators, common Gaussian law, native spatial basis,
and both normalized coefficient fields are all produced from the physical
parameters. The accepted J02 theorem is reused for random time slices,
all-original-test coordinates, and L2 interval increments. Individual
field envelopes are uniform and paired envelopes decay exponentially.
No random-field, orbit, path-moment, or source-decomposition premise is
added to the final physical producer.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T

variable {d r : ℕ} {Pw : ℝ}

/-- Exact inverse conversion of the frozen interval structure. The
operators and every coordinate and norm field are retained verbatim. -/
def nativeIntervalOfFrozen (E : r26t6_WeightedChart d r Pw)
    {C : WholeCoeff d} {T u c0 B : ℝ}
    (O : r26t6_IntervalOperators E C T u c0 B) :
    HRS.MS.S111K4J01.IntervalOperators (nativeChartOfFrozen E) C T u c0 B where
  drift := O.drift
  covariance := O.covariance
  drift_zero := O.drift_zero
  covariance_zero := O.covariance_zero
  drift_add := O.drift_add
  covariance_add := O.covariance_add
  drift_cont := O.drift_cont
  covariance_cont := O.covariance_cont
  drift_norm := O.drift_norm
  covariance_norm := O.covariance_norm
  drift_coordinate := O.drift_coordinate
  covariance_coordinate := O.covariance_coordinate

/-- The full random interval conclusion, stated with the exact frozen
operators, coefficient slicing, and all-test boundary predicates. This is
an output certificate for the actual constructed responses. -/
structure RandomIntervalControl
    {Omega : Type*} [MeasurableSpace Omega]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d} {T u c0 B : ℝ}
    (P : Measure Omega) (O : r26t6_IntervalOperators E C T u c0 B)
    (q : ℝ × Omega → r26t6_Coeff) (R : ℝ → ℝ) : Prop where
  time_measurable : AEStronglyMeasurable (r26t6_timeCoeffOf (u + T) q) P
  drift_zero : r26t6_randomDrift O q 0 = 0
  covariance_zero : r26t6_randomCovariance O q 0 = 0
  drift_continuous : ∀ w, ContinuousOn (fun v => r26t6_randomDrift O q v w)
    (Icc 0 (u + T))
  covariance_continuous : ∀ w, ContinuousOn (fun v => r26t6_randomCovariance O q v w)
    (Icc 0 (u + T))
  moments : ∀ v ∈ Icc 0 (u + T),
    MemLp (r26t6_randomDrift O q v) 2 P ∧
      MemLp (r26t6_randomCovariance O q v) 2 P
  increments : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
    eLpNorm (fun z => r26t6_randomDrift O q w z - r26t6_randomDrift O q v z) 2 P ≤
      ENNReal.ofReal (B * ∫ z in Icc v w,
        HRS.MS.S111K2.s111k2_age c0 u z * R z) ∧
    eLpNorm (fun z => r26t6_randomCovariance O q w z -
        r26t6_randomCovariance O q v z) 2 P ≤
      ENNReal.ofReal (B * |2 * C.ν| * ∫ z in Icc v w,
        HRS.MS.S111K2.s111k2_age c0 u z ^ 2 * R z)
  coordinates : ∀ᵐ w ∂P, ∀ v ∈ Icc 0 (u + T),
    r26t6_AllDriftCoordinates C (wholeSpaceIndex d) T u
      (r26t6_coefficientField E (fun z => q (z,w))) v
      (r26t6_randomDrift O q v w) ∧
    r26t6_AllShiftedJValue C (wholeSpaceIndex d) T u
      (r26t6_coefficientField E (fun z => q (z,w))) v
      (r26t6_randomCovariance O q v w)
  differences : ∀ q' : ℝ × Omega → r26t6_Coeff,
    MemLp q' 2 ((volume.restrict (Icc 0 (u + T))).prod P) →
    ∀ᵐ w ∂P, ∀ v : ℝ,
      r26t6_randomDrift O (q-q') v w =
        r26t6_randomDrift O q v w - r26t6_randomDrift O q' v w ∧
      r26t6_randomCovariance O (q-q') v w =
        r26t6_randomCovariance O q v w - r26t6_randomCovariance O q' v w

/-- Reuse of the accepted J02 result, with only a fieldwise conversion
between its native vocabulary and the frozen D02/D03 vocabulary. -/
theorem random_interval_control_of_frozen
    {Omega : Type*} [MeasurableSpace Omega]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d} {T u c0 B : ℝ}
    (hu : 0 ≤ u) (hc0 : 0 < c0) (hB : 0 ≤ B)
    (hco : r26t6_ChartedOrbits E C (wholeSpaceIndex d) (u + T))
    (hPw : (d : ℝ) < 2 * Pw)
    (horb : r26t6_OscOrbitApprox C (wholeSpaceIndex d) (u + T) r)
    (O : r26t6_IntervalOperators E C T u c0 B)
    (P : Measure Omega) [IsProbabilityMeasure P]
    (q : ℝ × Omega → r26t6_Coeff) (hqm : Measurable q)
    (hq : MemLp q 2 ((volume.restrict (Icc 0 (u + T))).prod P))
    (hq0 : ∀ p, inner ℝ (q p) (E.encode (fun _ => 1)) = 0)
    (R : ℝ → ℝ) (hRi : IntegrableOn R (Icc 0 (u + T)))
    (hRn : ∀ v ∈ Icc 0 (u + T), 0 ≤ R v)
    (hRs : ∀ᵐ v ∂volume.restrict (Icc 0 (u + T)),
      MemLp (fun w => q (v,w)) 2 P ∧
        eLpNorm (fun w => q (v,w)) 2 P ≤ ENNReal.ofReal (R v)) :
    RandomIntervalControl P O q R := by
  have hco' : HRS.MS.S111K4J01.ChartedOrbits (nativeChartOfFrozen E) C
      (wholeSpaceIndex d) (u + T) := hco
  have horb' : HRS.MS.S111K4AT.K4OscOrbitApprox C
      (wholeSpaceIndex d) (u + T) r :=
    ⟨horb.classical, horb.smooth, horb.bound, horb.limit⟩
  obtain ⟨hm, hz, hmem, hinc, hcoord, hsub⟩ :=
    HRS.MS.S111K4J01.k4_random_interval_L2 Pw T u c0 B hu hc0 hB
      (nativeChartOfFrozen E) C hco' hPw horb' (nativeIntervalOfFrozen E O)
      P q hqm hq hq0 R hRi hRn hRs
  refine ⟨hm, hz.1, hz.2, ?_, ?_, hmem, hinc, hcoord, hsub⟩
  · intro w
    exact O.drift_cont (r26t6_timeCoeffOf (u + T) q w)
  · intro w
    exact O.covariance_cont (r26t6_timeCoeffOf (u + T) q w)

/-- A vector second-moment estimate gives its L2 norm estimate, using
the accepted real-valued square-integral lemma on the norm function. -/
theorem vector_eLpNorm_two_le_of_second
    {Omega V : Type*} [MeasurableSpace Omega] [NormedAddCommGroup V]
    {P : Measure Omega} {f : Omega → V} (hf : MemLp f 2 P)
    {R : ℝ} (hR : 0 ≤ R) (hbound : (∫ w, ‖f w‖^2 ∂P) ≤ R^2) :
    eLpNorm f 2 P ≤ ENNReal.ofReal R := by
  have hn : MemLp (fun w => ‖f w‖) 2 P := by
    change eLpNorm (fun w => ‖f w‖) 2 P < ⊤
    rw [eLpNorm_norm _ hf.aestronglyMeasurable]
    exact hf
  have h := HRS.MS.R2Chaos.s94_eLpNorm_le_of_sq hn hR hbound
  rwa [eLpNorm_norm _ hf.aestronglyMeasurable] at h

/-- Paired increment bounds for the actual difference of the two random
responses, rather than only the response to the coefficient difference.
The accepted all-time a.e. linearity supplies one probability-good set
for both interval endpoints. -/
theorem RandomIntervalControl.paired_increments
    {Omega : Type*} [MeasurableSpace Omega]
    {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d} {T u c0 B : ℝ}
    {P : Measure Omega} {O : r26t6_IntervalOperators E C T u c0 B}
    {q0 q1 : ℝ × Omega → r26t6_Coeff} {R0 R : ℝ → ℝ}
    (h0 : RandomIntervalControl P O q0 R0)
    (hD : RandomIntervalControl P O (q0-q1) R)
    (hq1 : MemLp q1 2 ((volume.restrict (Icc 0 (u + T))).prod P)) :
    ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
      eLpNorm (fun z =>
          (r26t6_randomDrift O q0 w z - r26t6_randomDrift O q1 w z) -
          (r26t6_randomDrift O q0 v z - r26t6_randomDrift O q1 v z)) 2 P ≤
        ENNReal.ofReal (B * ∫ z in Icc v w,
          HRS.MS.S111K2.s111k2_age c0 u z * R z) ∧
      eLpNorm (fun z =>
          (r26t6_randomCovariance O q0 w z - r26t6_randomCovariance O q1 w z) -
          (r26t6_randomCovariance O q0 v z - r26t6_randomCovariance O q1 v z)) 2 P ≤
        ENNReal.ofReal (B * |2 * C.ν| * ∫ z in Icc v w,
          HRS.MS.S111K2.s111k2_age c0 u z ^ 2 * R z) := by
  intro v w hv hvw hw
  have hinc := hD.increments v w hv hvw hw
  have hlin := h0.differences q1 hq1
  constructor
  · have he : (fun z => r26t6_randomDrift O (q0-q1) w z -
        r26t6_randomDrift O (q0-q1) v z) =ᵐ[P] fun z =>
        (r26t6_randomDrift O q0 w z - r26t6_randomDrift O q1 w z) -
        (r26t6_randomDrift O q0 v z - r26t6_randomDrift O q1 v z) := by
      filter_upwards [hlin] with z hz
      rw [(hz w).1, (hz v).1]
    rw [← eLpNorm_congr_ae he]
    exact hinc.1
  · have he : (fun z => r26t6_randomCovariance O (q0-q1) w z -
        r26t6_randomCovariance O (q0-q1) v z) =ᵐ[P] fun z =>
        (r26t6_randomCovariance O q0 w z - r26t6_randomCovariance O q1 w z) -
        (r26t6_randomCovariance O q0 v z - r26t6_randomCovariance O q1 v z) := by
      filter_upwards [hlin] with z hz
      rw [(hz w).2, (hz v).2]
    rw [← eLpNorm_congr_ae he]
    exact hinc.2

/-- Complete physical random interval data. One chart, decay rate,
operator bound, and field envelope are chosen before the density,
preparation, and window start. Every law, field, and interval operator
in the conclusion is constructed from the physical data. -/
theorem physical_paired_interval_responses (hd : 2 ≤ d)
    (s a beta T lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2)
    (ha : 0 < a) (hbeta : 0 < beta) (hT : 0 < T) (hlam : 0 < lam) :
    ∃ E : r26t6_WeightedChart d (r26t6_coreOrder d) (r26t6_coreWeight d),
    ∃ c0 B R : ℝ, 0 < c0 ∧ 0 ≤ B ∧ 0 < R ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma → ∀ u : ℝ, ∀ hu : 0 ≤ u,
      ∃ P : Measure (PathPair d (wholeSpaceIndex d) (u + T)),
      ∃ hprob : IsProbabilityMeasure P,
        r26t6_SharedThermalLaw P s a beta gamma (u + T) rho
          (pairedProcess d (wholeSpaceIndex d) (u + T) (add_nonneg hu hT.le)) ∧
        ∃ basis : ℕ → Euc d → ℝ,
          IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis ∧
        ∃ qLin qQuad : Fin 2 → ℝ × PathPair d (wholeSpaceIndex d) (u + T) → r26t6_Coeff,
          (∀ i, @r26t6_PhysicalChartFields d (r26t6_coreOrder d) (r26t6_coreWeight d)
            (PathPair d (wholeSpaceIndex d) (u + T)) _ P hprob rho s (u + T) E basis
            (pairedProcess d (wholeSpaceIndex d) (u + T) (add_nonneg hu hT.le) i)
            (qLin i) (qQuad i)) ∧
        ∃ O : r26t6_IntervalOperators E (r26t6_thermalCoeff d s a beta rho) T u c0 B,
          (∀ i, RandomIntervalControl P O (qLin i) (fun _ => R) ∧
            RandomIntervalControl P O (qQuad i) (fun _ => R)) ∧
          RandomIntervalControl P O (qLin 0-qLin 1)
            (fun t => R * Real.exp (-(lam/beta)*t)) ∧
          RandomIntervalControl P O (qQuad 0-qQuad 1)
            (fun t => R * Real.exp (-(lam/beta)*t)) := by
  have hr : (2 : ℝ)+(d : ℝ)/2 < r26t6_coreOrder d := by
    unfold r26t6_coreOrder
    push_cast
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hPw : (d : ℝ) < 2*r26t6_coreWeight d := by
    unfold r26t6_coreWeight
    linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  obtain ⟨E, c0, B, hc0, hB, hO⟩ := physical_core_chart_interval_data
    hd s a beta T hs0 hs ha hbeta hT
  obtain ⟨C0, hC0, hind⟩ := physical_chart_field_uniform_moments
    (r := r26t6_coreOrder d) (Pw := r26t6_coreWeight d)
    hd s a beta hs0 hs ha hbeta hr hPw
  obtain ⟨C1, hC1, hpair⟩ := physical_paired_chart_field_decay
    (r := r26t6_coreOrder d) (Pw := r26t6_coreWeight d)
    hd s a beta lam hs0 hs ha hbeta hlam hr hPw
  let R : ℝ := Real.sqrt C0 + Real.sqrt C1 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have h0R : C0 ≤ R^2 := by
    calc
      C0 = (Real.sqrt C0)^2 := (Real.sq_sqrt hC0.le).symm
      _ ≤ R^2 := (sq_le_sq₀ (Real.sqrt_nonneg C0) hR.le).2
        (by dsimp [R]; linarith [Real.sqrt_nonneg C1])
  have h1R : C1 ≤ R^2 := by
    calc
      C1 = (Real.sqrt C1)^2 := (Real.sq_sqrt hC1.le).symm
      _ ≤ R^2 := (sq_le_sq₀ (Real.sqrt_nonneg C1) hR.le).2
        (by dsimp [R]; linarith [Real.sqrt_nonneg C0])
  refine ⟨E, c0, B, R, hc0, hB, hR, fun rho hrho hgap gamma hgamma u hu => ?_⟩
  have hH : 0 < u + T := add_pos_of_nonneg_of_pos hu hT
  obtain ⟨hco, horb, ⟨O⟩⟩ := hO rho hrho u hu
  obtain ⟨P, hprob, hZ, basis, hbasis, qLin, qQuad, hfields⟩ :=
    physical_shared_chart_fields hd s a beta gamma (u + T) hs0 hs ha hbeta hgamma hH
      hr hPw rho hrho E
  letI : IsProbabilityMeasure P := hprob
  let Z := pairedProcess d (wholeSpaceIndex d) (u + T) hH.le
  have hInd : ∀ i : Fin 2, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (u + T)),
      (MemLp (fun w => qLin i (t,w)) 2 P ∧ (∫ w, ‖qLin i (t,w)‖^2 ∂P) ≤ C0) ∧
      (MemLp (fun w => qQuad i (t,w)) 2 P ∧ (∫ w, ‖qQuad i (t,w)‖^2 ∂P) ≤ C0) := by
    intro i
    have hi : 0 ≤ r26t6_preparation beta gamma i := by
      unfold r26t6_preparation
      split_ifs
      · exact hgamma
      · exact hbeta.le
    exact hind rho hrho (r26t6_preparation beta gamma i) hi
      (PathPair d (wholeSpaceIndex d) (u + T)) P (u + T) (Z i) (hZ.evolution i)
      E basis hbasis (qLin i) (qQuad i) (hfields i)
  have hPair := hpair rho hrho hgap gamma hgamma
    (PathPair d (wholeSpaceIndex d) (u + T)) P (u + T) Z hZ E basis hbasis
    qLin qQuad hfields
  have hConstInt : IntegrableOn (fun _ : ℝ => R) (Icc 0 (u + T)) := integrable_const R
  have hExpInt : IntegrableOn (fun t : ℝ => R*Real.exp (-(lam/beta)*t))
      (Icc 0 (u + T)) := (by fun_prop : Continuous (fun t : ℝ =>
        R*Real.exp (-(lam/beta)*t))).continuousOn.integrableOn_Icc
  have hExpSq : ∀ t : ℝ,
      C1*Real.exp (-2*(lam/beta)*t) ≤ (R*Real.exp (-(lam/beta)*t))^2 := by
    intro t
    have he : Real.exp (-(lam/beta)*t)^2 = Real.exp (-2*(lam/beta)*t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, ← he]
    exact mul_le_mul_of_nonneg_right h1R (sq_nonneg _)
  refine ⟨P, hprob, hZ, basis, hbasis, qLin, qQuad, hfields, O, ?_, ?_, ?_⟩
  · intro i
    constructor
    · apply random_interval_control_of_frozen hu hc0 hB hco hPw horb O P (qLin i)
        (hfields i).linear_measurable (hfields i).linear_moment
        (fun p => ((hfields i).mass_zero p).1) (fun _ => R) hConstInt
        (fun _ _ => hR.le)
      filter_upwards [hInd i] with t ht
      exact ⟨ht.1.1, vector_eLpNorm_two_le_of_second ht.1.1 hR.le (ht.1.2.trans h0R)⟩
    · apply random_interval_control_of_frozen hu hc0 hB hco hPw horb O P (qQuad i)
        (hfields i).quadratic_measurable (hfields i).quadratic_moment
        (fun p => ((hfields i).mass_zero p).2) (fun _ => R) hConstInt
        (fun _ _ => hR.le)
      filter_upwards [hInd i] with t ht
      exact ⟨ht.2.1, vector_eLpNorm_two_le_of_second ht.2.1 hR.le (ht.2.2.trans h0R)⟩
  · have hmass : ∀ p, inner ℝ (qLin 0 p-qLin 1 p) (E.encode (fun _ => 1)) = 0 := by
      intro p
      change inner ℝ (qLin 0 p-qLin 1 p) (E.encode (fun _ => 1)) = 0
      rw [inner_sub_left, ((hfields 0).mass_zero p).1, ((hfields 1).mass_zero p).1,
        sub_self]
    have hslice : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (u + T)),
        MemLp (fun w => (qLin 0-qLin 1) (t,w)) 2 P ∧
          eLpNorm (fun w => (qLin 0-qLin 1) (t,w)) 2 P ≤
            ENNReal.ofReal (R*Real.exp (-(lam/beta)*t)) := by
      filter_upwards [hPair] with t ht
      exact ⟨ht.1.1, vector_eLpNorm_two_le_of_second ht.1.1 (by positivity)
        (ht.1.2.trans (hExpSq t))⟩
    exact random_interval_control_of_frozen hu hc0 hB hco hPw horb O P (qLin 0-qLin 1)
      ((hfields 0).linear_measurable.sub (hfields 1).linear_measurable)
      ((hfields 0).linear_moment.sub (hfields 1).linear_moment) hmass
      (fun t => R*Real.exp (-(lam/beta)*t)) hExpInt (fun _ _ => by positivity) hslice
  · have hmass : ∀ p, inner ℝ (qQuad 0 p-qQuad 1 p) (E.encode (fun _ => 1)) = 0 := by
      intro p
      change inner ℝ (qQuad 0 p-qQuad 1 p) (E.encode (fun _ => 1)) = 0
      rw [inner_sub_left, ((hfields 0).mass_zero p).2, ((hfields 1).mass_zero p).2,
        sub_self]
    have hslice : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (u + T)),
        MemLp (fun w => (qQuad 0-qQuad 1) (t,w)) 2 P ∧
          eLpNorm (fun w => (qQuad 0-qQuad 1) (t,w)) 2 P ≤
            ENNReal.ofReal (R*Real.exp (-(lam/beta)*t)) := by
      filter_upwards [hPair] with t ht
      exact ⟨ht.2.1, vector_eLpNorm_two_le_of_second ht.2.1 (by positivity)
        (ht.2.2.trans (hExpSq t))⟩
    exact random_interval_control_of_frozen hu hc0 hB hco hPw horb O P (qQuad 0-qQuad 1)
      ((hfields 0).quadratic_measurable.sub (hfields 1).quadratic_measurable)
      ((hfields 0).quadratic_moment.sub (hfields 1).quadratic_moment) hmass
      (fun t => R*Real.exp (-(lam/beta)*t)) hExpInt (fun _ _ => by positivity) hslice

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.random_interval_control_of_frozen
#print axioms HRS.MS.ProClosureS111.vector_eLpNorm_two_le_of_second
#print axioms HRS.MS.ProClosureS111.RandomIntervalControl.paired_increments
#print axioms HRS.MS.ProClosureS111.physical_paired_interval_responses
