import HRS.MS.S111K4J02E
import HRS.MS.S111K4J01N
import HRS.MS.S111K4J01M

/-!
# S11.1 / J02, piece F (S111K4): clauses 1-4 and 6 of `random_interval_L2`

Everything in Pro `S111.J02` except the all-oscillator-test coordinate clause (clause 5), which needs the separate
`all_tests` boundary (`OscOrbitApprox`, not in the repo).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4j_age_props {c0 u : ℝ} (hc0 : 0 < c0) (k : ℕ) :
    (∀ v, 0 ≤ age c0 u v ^ k) ∧ (∀ v, age c0 u v ^ k ≤ 1) ∧ Measurable (fun v => age c0 u v ^ k) :=
  age_props (u := u) hc0 k

theorem k4_random_interval_core {d r : ℕ} (Pw T u c0 B : ℝ) (hc0 : 0 < c0) (hB : 0 ≤ B)
    {E : WeightedChart d r Pw} {C : WholeCoeff d}
    (O : IntervalOperators E C T u c0 B)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (q : ℝ × Omega → Coeff) (hqm : Measurable q)
    (hq : MemLp q 2 ((volume.restrict (Set.Icc 0 (u + T))).prod P))
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
    ∀ q' : ℝ × Omega → Coeff,
      MemLp q' 2 ((volume.restrict (Set.Icc 0 (u + T))).prod P) →
      ∀ᵐ w ∂P, ∀ v : ℝ,
        randomDrift O (q - q') v w = randomDrift O q v w - randomDrift O q' v w ∧
        randomCovariance O (q - q') v w =
          randomCovariance O q v w - randomCovariance O q' v w := by
  have hRs' : ∀ᵐ v ∂volume.restrict (Set.Icc 0 (u + T)),
      eLpNorm (fun w => q (v, w)) 2 P ≤ ENNReal.ofReal (R v) := hRs.mono fun v hv => hv.2
  have hQ := k4j_timeCoeffOf_stronglyMeasurable (u + T) q hqm
  obtain ⟨a0, a1, am⟩ := k4j_age_props (u := u) hc0 1
  obtain ⟨b0, b1, bm⟩ := k4j_age_props (u := u) hc0 2
  simp only [pow_one] at a0 a1 am
  -- the two L2 bounds on every interval
  have hD : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
      eLpNorm (fun z => O.drift v w (timeCoeffOf (u + T) q z)) 2 P ≤
        ENNReal.ofReal (B * ∫ z in Set.Icc v w, age c0 u z * R z) := fun v w hv hvw hw =>
    k4j_L2_bound P (u + T) q hqm R hRi hRn hRs' (O.drift v w) hv hvw hw (age c0 u) a0 a1 am B hB
      (O.drift_norm v w hv hvw hw)
  have hCv : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
      eLpNorm (fun z => O.covariance v w (timeCoeffOf (u + T) q z)) 2 P ≤
        ENNReal.ofReal (B * |2 * C.ν| * ∫ z in Set.Icc v w, age c0 u z ^ 2 * R z) := fun v w hv hvw hw =>
    k4j_L2_bound P (u + T) q hqm R hRi hRn hRs' (O.covariance v w) hv hvw hw (fun z => age c0 u z ^ 2) b0 b1
      bm (B * |2 * C.ν|) (mul_nonneg hB (abs_nonneg _)) (O.covariance_norm v w hv hvw hw)
  refine ⟨hQ.aestronglyMeasurable, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · funext z
    show O.drift 0 0 (timeCoeffOf (u + T) q z) = 0
    rw [O.drift_zero]; rfl
  · funext z
    show O.covariance 0 0 (timeCoeffOf (u + T) q z) = 0
    rw [O.covariance_zero]; rfl
  · intro v hv
    exact ⟨lt_of_le_of_lt (hD 0 v le_rfl hv.1 hv.2) ENNReal.ofReal_lt_top,
      lt_of_le_of_lt (hCv 0 v le_rfl hv.1 hv.2) ENNReal.ofReal_lt_top⟩
  · intro v w hv hvw hw
    constructor
    · have : (fun z => randomDrift O q w z - randomDrift O q v z) =
          fun z => O.drift v w (timeCoeffOf (u + T) q z) := by
        funext z
        show O.drift 0 w _ - O.drift 0 v _ = _
        rw [O.drift_add 0 v w le_rfl hv hvw hw, add_apply, add_sub_cancel_left]
      rw [this]; exact hD v w hv hvw hw
    · have : (fun z => randomCovariance O q w z - randomCovariance O q v z) =
          fun z => O.covariance v w (timeCoeffOf (u + T) q z) := by
        funext z
        show O.covariance 0 w _ - O.covariance 0 v _ = _
        rw [O.covariance_add 0 v w le_rfl hv hvw hw, add_apply,
          add_sub_cancel_left]
      rw [this]; exact hCv v w hv hvw hw
  · intro q' hq'
    exact k4j_random_sub O q q' hq hq'

end HRS.MS.S111K4J01
