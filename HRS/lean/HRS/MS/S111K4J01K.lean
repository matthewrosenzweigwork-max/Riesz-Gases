import HRS.MS.S111K4J01J

/-!
# S11.1 / J01 piece: the covariance interval map as a bounded linear map on the `L¹` coefficient space (S11K4)

From the B03 output (`CovCore`: an interval tensor `J z a b`, additive/homogeneous in admissible forcings, with the K3 coordinate
formula and the age-squared norm bound) we build, for `0 ≤ a ≤ b ≤ u + T`, a bounded linear map
`q ↦ J (coefficientField E q) a b` on `TimeCoeff (u + T)`; additivity uses that `((q + q') v) = q v + q' v` for a.e. `v` and the
a.e.-congruence `J_congr`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

/-- The output of the B03 covariance theorem for one realisation (Pro `window_covariance_BV`, local copy). -/
def CovCore (d r : ℕ) (m T Pw u c0 K : ℝ) (C : WholeCoeff d)
    (J : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d m T) 2) : Prop :=
  (∀ z z', IsR2L1F r Pw (u + T) z → IsR2L1F r Pw (u + T) z' →
    R2JIntegrandMeas C m (u + T) z → R2JIntegrandMeas C m (u + T) z' →
    ∀ a b, J (z + z') a b = J z a b + J z' a b) ∧
  (∀ (c : ℝ) z, IsR2L1F r Pw (u + T) z → R2JIntegrandMeas C m (u + T) z →
    ∀ a b, J (c • z) a b = c • J z a b) ∧
  ∀ z, IsR2L1F r Pw (u + T) z → R2JIntegrandMeas C m (u + T) z →
    (∀ a, J z a a = 0) ∧
    (∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ u + T → J z a c = J z a b + J z b c) ∧
    ContinuousOn (fun v => J z 0 v) (Set.Icc 0 (u + T)) ∧
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ u + T →
      HRS.MS.S111K3.K3ShiftedJValue C m T u z a b (J z a b) ∧
      ‖J z a b‖ₑ ≤ ENNReal.ofReal (K * |2 * C.ν|) *
        ∫⁻ v in Set.Ioc a b, ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v)

section cov
variable {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {T u c0 K : ℝ}
  {J : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d (wholeSpaceIndex d : ℝ) T) 2}

theorem q_int (q : TimeCoeff (u + T)) :
    ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖(q : ℝ → Coeff) v‖ₑ < ⊤ :=
  (Lp.memLp q |>.integrable le_rfl).2

theorem zq0_adm (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T)) (q : TimeCoeff (u + T)) :
    IsR2L1F r Pw (u + T) (coefficientField E (q : ℝ → Coeff)) ∧
      R2JIntegrandMeas C (wholeSpaceIndex d : ℝ) (u + T) (coefficientField E (q : ℝ → Coeff)) :=
  ⟨zQ_L1F E (Lp.stronglyMeasurable q) (q_int q), zQ_JMeas E hco (Lp.stronglyMeasurable q)⟩

/-- The value of the interval tensor on the forcing of `q` (junk `0` off `0 ≤ a ≤ b ≤ u + T`). -/
def Jq (J : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d (wholeSpaceIndex d : ℝ) T) 2)
    (q : TimeCoeff (u + T)) (a b : ℝ) : projTensor (OscPath d (wholeSpaceIndex d : ℝ) T) 2 :=
  J (coefficientField E (q : ℝ → Coeff)) a b

theorem admQ (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T)) {Q : ℝ → Coeff}
    (hQ : StronglyMeasurable Q) (hint : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖Q v‖ₑ < ⊤) :
    IsR2L1F r Pw (u + T) (coefficientField E Q) ∧
      R2JIntegrandMeas C (wholeSpaceIndex d : ℝ) (u + T) (coefficientField E Q) :=
  ⟨zQ_L1F E hQ hint, zQ_JMeas E hco hQ⟩

theorem Jq_add (hT : 0 < T) (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T))
    (hJ : CovCore d r (wholeSpaceIndex d : ℝ) T Pw u c0 K C J) (q q' : TimeCoeff (u + T))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ u + T) :
    Jq E J (q + q') a b = Jq E J q a b + Jq E J q' a b := by
  obtain ⟨hadd, -, hprops⟩ := hJ
  obtain ⟨hA1, hM1⟩ := zq0_adm E hco q
  obtain ⟨hA2, hM2⟩ := zq0_adm E hco q'
  obtain ⟨hA3, hM3⟩ := zq0_adm E hco (q + q')
  have hsum : coefficientField E (q + q' : TimeCoeff (u + T)) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (u + T))]
      coefficientField E (q : ℝ → Coeff) + coefficientField E (q' : ℝ → Coeff) := by
    filter_upwards [Lp.coeFn_add q q'] with v hv
    funext f
    show inner ℝ (((q + q' : TimeCoeff (u + T)) : ℝ → Coeff) v) (E.encode f) =
      inner ℝ ((q : ℝ → Coeff) v) (E.encode f) + inner ℝ ((q' : ℝ → Coeff) v) (E.encode f)
    rw [hv]
    simp [inner_add_left]
  -- the sum field is admissible
  have hQ : StronglyMeasurable (fun v => (q : ℝ → Coeff) v + (q' : ℝ → Coeff) v) :=
    (Lp.stronglyMeasurable q).add (Lp.stronglyMeasurable q')
  have hQint : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖(q : ℝ → Coeff) v + (q' : ℝ → Coeff) v‖ₑ < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun v => enorm_add_le _ _) ?_
    rw [lintegral_add_left (Lp.stronglyMeasurable q).enorm]
    exact ENNReal.add_lt_top.2 ⟨q_int q, q_int q'⟩
  have hzs : coefficientField E (q : ℝ → Coeff) + coefficientField E (q' : ℝ → Coeff) =
      coefficientField E (fun v => (q : ℝ → Coeff) v + (q' : ℝ → Coeff) v) := by
    funext v f; simp [coefficientField, inner_add_left]
  obtain ⟨hA4, hM4⟩ := admQ E hco hQ hQint
  rw [← hzs] at hA4 hM4
  obtain ⟨-, -, -, hv3⟩ := hprops _ hA3 hM3
  obtain ⟨-, -, -, hv4⟩ := hprops _ hA4 hM4
  have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Icc (0 : ℝ) (u + T) →
      coefficientField E (q + q' : TimeCoeff (u + T)) v =
        (coefficientField E (q : ℝ → Coeff) + coefficientField E (q' : ℝ → Coeff)) v :=
    (ae_restrict_iff' measurableSet_Icc).1 hsum
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  unfold Jq
  rw [J_congr hT (hv3 a b ha hab hb).1 (hv4 a b ha hab hb).1 hsub hae]
  exact hadd _ _ hA1 hA2 hM1 hM2 a b

theorem Jq_smul (hT : 0 < T) (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T))
    (hJ : CovCore d r (wholeSpaceIndex d : ℝ) T Pw u c0 K C J) (c : ℝ) (q : TimeCoeff (u + T))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ u + T) :
    Jq E J (c • q) a b = c • Jq E J q a b := by
  obtain ⟨-, hsmul, hprops⟩ := hJ
  obtain ⟨hA1, hM1⟩ := zq0_adm E hco q
  obtain ⟨hA3, hM3⟩ := zq0_adm E hco (c • q)
  have hQ : StronglyMeasurable (fun v => c • (q : ℝ → Coeff) v) := (Lp.stronglyMeasurable q).const_smul c
  have hQint : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖c • (q : ℝ → Coeff) v‖ₑ < ⊤ := by
    simp_rw [enorm_smul]
    rw [lintegral_const_mul' _ _ (by simp)]
    exact ENNReal.mul_lt_top (by simp) (q_int q)
  have hzs : c • coefficientField E (q : ℝ → Coeff) =
      coefficientField E (fun v => c • (q : ℝ → Coeff) v) := by
    funext v f; simp [coefficientField, inner_smul_left]
  obtain ⟨hA4, hM4⟩ := admQ E hco hQ hQint
  rw [← hzs] at hA4 hM4
  obtain ⟨-, -, -, hv3⟩ := hprops _ hA3 hM3
  obtain ⟨-, -, -, hv4⟩ := hprops _ hA4 hM4
  have hae : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Icc (0 : ℝ) (u + T) →
      coefficientField E (c • q : TimeCoeff (u + T)) v = (c • coefficientField E (q : ℝ → Coeff)) v := by
    refine (ae_restrict_iff' measurableSet_Icc).1 ?_
    filter_upwards [Lp.coeFn_smul c q] with v hv
    funext f
    show inner ℝ (((c • q : TimeCoeff (u + T)) : ℝ → Coeff) v) (E.encode f) =
      c * inner ℝ ((q : ℝ → Coeff) v) (E.encode f)
    rw [hv]
    simp [inner_smul_left]
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  unfold Jq
  rw [J_congr hT (hv3 a b ha hab hb).1 (hv4 a b ha hab hb).1 hsub hae]
  exact hsmul c _ hA1 hM1 a b

end cov

end HRS.MS.S111K4J01
