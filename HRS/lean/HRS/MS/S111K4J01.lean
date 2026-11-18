import HRS.MS.S111K4J01N

/-!
# S11.1 / J01: `coefficient_interval_operators` (S11K4)

Pro contract `S111.J01` (skeleton `S11.1-Intervals`), proved against the local copies of the skeleton structures
(`S111K4J01D`) and the repo's `S111k2WindowOrbitInput`, which has the same fields as Pro's `WindowOrbitInput`.
Difference to the contract's proof sketch: the drift operator is extended off the zero-mass subspace by composing with the
orthogonal projection onto `(E 1)^⊥` (identity on zero-mass coefficients) instead of subtracting `f(0)`, so no weighted
Sobolev point evaluation is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4_coefficient_interval_operators (d r : ℕ) (hd : 2 ≤ d)
    (T Pw S c0 : ℝ) (hT : 0 < T) (hPw : (d : ℝ) / 2 + 1 < Pw)
    (hr : (d : ℝ) / 2 + 2 < r) (hS : 0 ≤ S) (hc0 : 0 < c0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ E : WeightedChart d r Pw,
      ∀ C : WholeCoeff d, ∀ b : MultiIndex d → ℝ,
      Summable (fun alpha => b alpha ^ 2) → (∑' alpha, b alpha ^ 2) ≤ S →
      S111k2WindowOrbitInput C (wholeSpaceIndex d : ℝ) c0 r b →
      ∀ u : ℝ, 0 ≤ u → ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T) →
        Nonempty (IntervalOperators E C T u c0 B) := by
  classical
  obtain ⟨K3, hK3, hcov⟩ := HRS.MS.S111K3.s111k3_window_covariance_BV d r hd (wholeSpaceIndex d : ℝ) T
    Pw S c0 hT (by linarith) hS hc0
  set Kd : ℝ := s111k2_Kdrift d r Pw S with hKd
  have hKd0 : 0 ≤ Kd := (s111k2_Kdrift_pos d r Pw S).le
  refine ⟨max Kd K3, le_max_of_le_left hKd0, ?_⟩
  intro E C b hbs hbS hW u hu hco
  obtain ⟨J, hJ⟩ := hcov C b hbs hbS hW u hu
  have hCore : CovCore d r (wholeSpaceIndex d : ℝ) T Pw u c0 K3 C J :=
    ⟨hJ.1, hJ.2.1, fun z hz hm => by
      obtain ⟨h1, h2, h3, -, h5⟩ := hJ.2.2 z hz hm
      exact ⟨h1, h2, h3, h5⟩⟩
  have hdata : ∀ q : TimeCoeff (u + T),
      S111k2Drift C (wholeSpaceIndex d : ℝ) c0 r b S T u Pw (zq E q) := fun q =>
    zq_drift E hPw hT hc0 hu hbs hbS hW hco q
  -- the drift linear maps
  have Dq_add_q : ∀ (q q' : TimeCoeff (u + T)) {a b' : ℝ}, 0 ≤ a → a ≤ b' → b' ≤ u + T →
      Dq E hdata (q + q') a b' = Dq E hdata q a b' + Dq E hdata q' a b' := by
    intro q q' a b' ha hab hb
    have := Dq_lin E hdata (q := q) (q' := q') (q'' := q + q') (c := 1) (by
      filter_upwards [Lp.coeFn_add q q'] with v hv
      rw [hv]; simp) ha hab hb
    simpa using this
  have Dq_smul_q : ∀ (c : ℝ) (q : TimeCoeff (u + T)) {a b' : ℝ}, 0 ≤ a → a ≤ b' → b' ≤ u + T →
      Dq E hdata (c • q) a b' = c • Dq E hdata q a b' := by
    intro c q a b' ha hab hb
    have := Dq_lin E hdata (q := 0) (q' := q) (q'' := c • q) (c := c) (by
      filter_upwards [Lp.coeFn_smul c q, Lp.coeFn_zero Coeff 1
        (volume.restrict (Set.Icc (0 : ℝ) (u + T)))] with v hv h0
      rw [hv, h0]; simp) ha hab hb
    rw [Dq_zero E hdata hc0 ha hab hb, zero_add] at this
    exact this
  have hdr : ∃ dL : ℝ → ℝ → (TimeCoeff (u + T) →L[ℝ] R2X d T),
      (∀ a b', 0 ≤ a → a ≤ b' → b' ≤ u + T → ∀ q, dL a b' q = Dq E hdata q a b') ∧
      (∀ a b', ¬ (0 ≤ a ∧ a ≤ b' ∧ b' ≤ u + T) → dL a b' = 0) := by
    refine ⟨fun a b' => if h : 0 ≤ a ∧ a ≤ b' ∧ b' ≤ u + T then
      LinearMap.mkContinuous
        { toFun := fun q => Dq E hdata q a b'
          map_add' := fun q q' => Dq_add_q q q' h.1 h.2.1 h.2.2
          map_smul' := fun c q => by simpa using Dq_smul_q c q h.1 h.2.1 h.2.2 }
        Kd (fun q => Dq_norm_le E hdata hc0 q h.1 h.2.1 h.2.2) else 0, ?_, ?_⟩
    · intro a b' ha hab hb q
      simp only [dif_pos (And.intro ha (And.intro hab hb))]
      rfl
    · intro a b' h
      simp only [dif_neg h]
  obtain ⟨dL, hdL, hdL0⟩ := hdr
  -- the covariance linear maps
  have hcr : ∃ cL : ℝ → ℝ → (TimeCoeff (u + T) →L[ℝ] projTensor (R2X d T) 2),
      (∀ a b', 0 ≤ a → a ≤ b' → b' ≤ u + T → ∀ q, cL a b' q = Jq E J q a b') ∧
      (∀ a b', ¬ (0 ≤ a ∧ a ≤ b' ∧ b' ≤ u + T) → cL a b' = 0) := by
    refine ⟨fun a b' => if h : 0 ≤ a ∧ a ≤ b' ∧ b' ≤ u + T then
      LinearMap.mkContinuous
        { toFun := fun q => Jq E J q a b'
          map_add' := fun q q' => Jq_add E hT hco hCore q q' h.1 h.2.1 h.2.2
          map_smul' := fun c q => by simpa using Jq_smul E hT hco hCore c q h.1 h.2.1 h.2.2 }
        (K3 * |2 * C.ν|) (fun q => Jq_norm_le E hco hCore hc0 hK3 q h.1 h.2.1 h.2.2) else 0, ?_, ?_⟩
    · intro a b' ha hab hb q
      simp only [dif_pos (And.intro ha (And.intro hab hb))]
      rfl
    · intro a b' h
      simp only [dif_neg h]
  obtain ⟨cL, hcL, hcL0⟩ := hcr
  have hprops := fun q : TimeCoeff (u + T) =>
    hCore.2.2 _ (zq0_adm E hco q).1 (zq0_adm E hco q).2
  refine ⟨⟨dL, cL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v
    by_cases h : 0 ≤ v ∧ v ≤ u + T
    · ext q
      rw [hdL v v h.1 le_rfl h.2, Dq_self E hdata q h.1 h.2]; rfl
    · rw [hdL0]; exact fun h' => h ⟨h'.1, h'.2.2⟩
  · intro v
    by_cases h : 0 ≤ v ∧ v ≤ u + T
    · refine ContinuousLinearMap.ext fun q => ?_
      rw [hcL v v h.1 le_rfl h.2]
      exact (hprops q).1 v
    · rw [hcL0]; exact fun h' => h ⟨h'.1, h'.2.2⟩
  · intro v w z hv hvw hwz hz
    ext q
    rw [add_apply, hdL v z hv (hvw.trans hwz) hz, hdL v w hv hvw (hwz.trans hz),
      hdL w z (hv.trans hvw) hwz hz]
    exact Dq_interval_add E hdata q hv hvw hwz hz
  · intro v w z hv hvw hwz hz
    refine ContinuousLinearMap.ext fun q => ?_
    rw [add_apply, hcL v z hv (hvw.trans hwz) hz, hcL v w hv hvw (hwz.trans hz),
      hcL w z (hv.trans hvw) hwz hz]
    exact (hprops q).2.1 v w z hv hvw hwz hz
  · intro q
    exact (Dq_cont E hdata hc0 q).congr fun v hv => hdL 0 v le_rfl hv.1 hv.2 q
  · intro q
    exact (hprops q).2.2.1.congr fun v hv => hcL 0 v le_rfl hv.1 hv.2 q
  · intro v w hv hvw hw q
    rw [hdL v w hv hvw hw q]
    refine (Dq_norm_int E hdata hc0 q hv hvw hw).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (integral_nonneg fun z => mul_nonneg (s111k2_age_pos c0 u z).le (norm_nonneg _))
  · intro v w hv hvw hw q
    rw [hcL v w hv hvw hw q]
    refine (Jq_norm_int E hco hCore hc0 hK3 q hv hvw hw).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
      (integral_nonneg fun z => mul_nonneg ((age_props (u := u) hc0 2).1 z) (norm_nonneg _))
  · intro q hq0 v w hv hvw hw tau phi hphi
    rw [hdL v w hv hvw hw q]
    exact Dq_coordinate E hdata q hq0 hv hvw hw tau hphi
  · intro q v w hv hvw hw
    rw [show cL v w q = Jq E J q v w from hcL v w hv hvw hw q]
    exact ((hprops q).2.2.2 v w hv hvw hw).1

end HRS.MS.S111K4J01
