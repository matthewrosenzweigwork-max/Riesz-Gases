import HRS.MS.S111K4J02H

/-!
# S11.1 / J02: `random_interval_L2` (S111K4)

Pro contract `S111.J02` (skeleton `S11.1-Intervals`), same conclusion, same hypotheses except that the orbit
approximation `horb : OscOrbitApprox C (wholeSpaceIndex d) (u + T) r` (a structure absent from the repo) is replaced by the
local copy `K4OscOrbitApprox` (Pro `r26t6_OscOrbitApprox`); the Pro boundary lemmas
`boundary_drift/covariance_coordinates_all_tests` are proved from it (`k4_all_tests_drift/cov`, S111K4ATE/ATK), and
`hco : ChartedOrbits` is explicit; `hP : d < 2 Pw` is the Pro `hPw` (it is part of the data of `E`,
`O` in the Pro DAG). Falsity check: the statement as given is true; the proof is Minkowski in `L²(P)` on the slice
envelope (C, E), measurability of the `L¹`-valued slice map (A, B), additivity of the operator (F).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4_random_interval_L2
    {d r : ℕ} (Pw T u c0 B : ℝ)
    (hu : 0 ≤ u) (hc0 : 0 < c0) (hB : 0 ≤ B)
    (E : WeightedChart d r Pw) (C : WholeCoeff d)
    (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T))
    (hP : (d : ℝ) < 2 * Pw)
    (horb : HRS.MS.S111K4AT.K4OscOrbitApprox C (wholeSpaceIndex d : ℝ) (u + T) r)
    (O : IntervalOperators E C T u c0 B)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (q : ℝ × Omega → Coeff) (hqm : Measurable q)
    (hq : MemLp q 2 ((volume.restrict (Set.Icc 0 (u + T))).prod P))
    (hq0 : ∀ p, inner ℝ (q p) (E.encode (fun _ => 1)) = 0)
    (R : ℝ → ℝ) (hRi : IntegrableOn R (Set.Icc 0 (u + T)))
    (hRn : ∀ v ∈ Set.Icc 0 (u + T), 0 ≤ R v)
    (hRs : ∀ᵐ v ∂volume.restrict (Set.Icc 0 (u + T)),
      MemLp (fun w => q (v, w)) 2 P ∧
        eLpNorm (fun w => q (v, w)) 2 P ≤ ENNReal.ofReal (R v)) :
    AEStronglyMeasurable (timeCoeffOf (u + T) q) P ∧
    (randomDrift O q 0 = 0 ∧ randomCovariance O q 0 = 0) ∧
    (∀ v ∈ Set.Icc 0 (u + T),
      MemLp (randomDrift O q v) 2 P ∧ MemLp (randomCovariance O q v) 2 P) ∧
    (∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
      eLpNorm (fun z => randomDrift O q w z - randomDrift O q v z) 2 P ≤
        ENNReal.ofReal (B * ∫ z in Set.Icc v w, age c0 u z * R z) ∧
      eLpNorm (fun z => randomCovariance O q w z - randomCovariance O q v z) 2 P ≤
        ENNReal.ofReal (B * |2 * C.ν| * ∫ z in Set.Icc v w, age c0 u z ^ 2 * R z)) ∧
    (∀ᵐ w ∂P, ∀ v ∈ Set.Icc 0 (u + T),
      AllDriftCoordinates C (wholeSpaceIndex d : ℝ) T u
        (coefficientField E (fun z => q (z, w))) v (randomDrift O q v w) ∧
      AllShiftedJValue C (wholeSpaceIndex d : ℝ) T u
        (coefficientField E (fun z => q (z, w))) v (randomCovariance O q v w)) ∧
    ∀ q' : ℝ × Omega → Coeff,
      MemLp q' 2 ((volume.restrict (Set.Icc 0 (u + T))).prod P) →
      ∀ᵐ w ∂P, ∀ v : ℝ,
        randomDrift O (q - q') v w = randomDrift O q v w - randomDrift O q' v w ∧
        randomCovariance O (q - q') v w =
          randomCovariance O q v w - randomCovariance O q' v w := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := k4_random_interval_core Pw T u c0 B hc0 hB O P q hqm hq R hRi hRn hRs
  exact ⟨h1, h2, h3, h4, k4_random_coordinates T u c0 B hu hco hP horb O P q hqm hq hq0, h6⟩

end HRS.MS.S111K4J01
