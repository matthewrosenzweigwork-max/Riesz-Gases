import HRS.MS.S111K3D2

/-!
# S11.1 continuation (S11K3), B03 part E1: the measurable modification of the covariance density, admissibility, linearity in `z`

`k3Dm C m T u z`: `1_G(v) D_v` for a Borel set `G` of full measure on which `D` is entrywise measurable (`k3_exists_good_D`).
`K3Tr`: finiteness of the trace integral; closed under sums and scalar multiples; `K3TD` for `k3Dm`; the a.e. linearity of
`z ↦ k3Dm z`.
-/

set_option autoImplicit false
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.Uniform HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T u c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ} {Pw K1 : ℝ}
  {z z' : ℝ → (Euc d → ℝ) → ℝ}

/-- The `z`-independent part of `K3Adm`. -/
structure K3Ctx (C : WholeCoeff d) (m T u c0 : ℝ) (r : ℕ) (b : MultiIndex d → ℝ) (Pw K1 : ℝ) : Prop where
  hd : 1 ≤ d
  hP : (d : ℝ) < 2 * Pw
  hW : S111k2WindowOrbitInput C m c0 r b
  hbS : Summable fun α => b α ^ 2
  hc0 : 0 ≤ c0
  hu : 0 ≤ u
  hT : 0 ≤ T
  hK1 : 0 ≤ K1
  hG : ∀ v ∈ Icc (0 : ℝ) (u + T), ∀ i : Fin d, ContDiff ℝ r (k3G C m T u v i) ∧
    ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (k3G C m T u v i) x‖ ≤ K1 * s111k2_age c0 u v

def K3Ctx.adm (c : K3Ctx C m T u c0 r b Pw K1) (hz : S101Lin r Pw (u + T) z) (hm : R2JIntegrandMeas C m (u + T) z) :
    K3Adm C m T u c0 r b Pw K1 z :=
  ⟨c.hd, c.hP, c.hW, c.hbS, c.hc0, c.hu, c.hT, c.hK1, c.hG, hz, hm⟩

lemma K3Adm.add (A : K3Adm C m T u c0 r b Pw K1 z) (A' : K3Adm C m T u c0 r b Pw K1 z') :
    K3Adm C m T u c0 r b Pw K1 (z + z') :=
  ⟨A.hd, A.hP, A.hW, A.hbS, A.hc0, A.hu, A.hT, A.hK1, A.hG, A.hz.add A'.hz, s101_meas_add A.hmeas A'.hmeas⟩

lemma K3Adm.smul (c : ℝ) (A : K3Adm C m T u c0 r b Pw K1 z) : K3Adm C m T u c0 r b Pw K1 (c • z) :=
  ⟨A.hd, A.hP, A.hW, A.hbS, A.hc0, A.hu, A.hT, A.hK1, A.hG, A.hz.smul c, s101_meas_smul c A.hmeas⟩

/-! ### The measurable modification -/

def k3Good (C : WholeCoeff d) (m T u : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (G : Set ℝ) : Prop :=
  MeasurableSet G ∧ G ⊆ Icc 0 (u + T) ∧ volume (Icc 0 (u + T) \ G) = 0 ∧
    ∀ h k : KSpace d m T, Measurable (fun v => if v ∈ G then k3D C m T u z v h k else 0)

def k3Dm (C : WholeCoeff d) (m T u : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ) : K3Bil d m T :=
  if h : ∃ G, k3Good C m T u z G then (if v ∈ h.choose then k3D C m T u z v else 0) else 0

lemma k3_Dm_spec (A : K3Adm C m T u c0 r b Pw K1 z) :
    ∃ G, k3Good C m T u z G ∧ ∀ v, k3Dm C m T u z v = if v ∈ G then k3D C m T u z v else 0 := by
  have h : ∃ G, k3Good C m T u z G := k3_exists_good_D A
  refine ⟨h.choose, h.choose_spec, fun v => ?_⟩
  unfold k3Dm
  rw [dif_pos h]

lemma k3_Dm_ae_eq (A : K3Adm C m T u c0 r b Pw K1 z) :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (u + T))), k3Dm C m T u z v = k3D C m T u z v := by
  obtain ⟨G, hG, hDm⟩ := k3_Dm_spec A
  have h1 : ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (u + T))), v ∈ G := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have : ∀ᵐ v ∂(volume : Measure ℝ), v ∉ Icc (0 : ℝ) (u + T) \ G :=
      measure_eq_zero_iff_ae_notMem.1 hG.2.2.1
    filter_upwards [this] with v hv hvI
    by_contra hnot
    exact hv ⟨hvI, hnot⟩
  filter_upwards [h1] with v hv
  rw [hDm, if_pos hv]

lemma k3_Dm_entries_meas (A : K3Adm C m T u c0 r b Pw K1 z) (x y : KSpace d m T) :
    Measurable fun v => k3Dm C m T u z v x y := by
  obtain ⟨G, hG, hDm⟩ := k3_Dm_spec A
  have := hG.2.2.2 x y
  convert this using 1
  funext v
  rw [hDm]
  by_cases hv : v ∈ G <;> simp [hv]

lemma k3_Dm_symm (A : K3Adm C m T u c0 r b Pw K1 z) (v : ℝ) (x y : KSpace d m T) :
    k3Dm C m T u z v x y = k3Dm C m T u z v y x := by
  obtain ⟨G, hG, hDm⟩ := k3_Dm_spec A
  rw [hDm]
  by_cases hv : v ∈ G
  · simp only [hv, if_true]
    exact k3_D_symm A (hG.2.1 hv) x y
  · simp [hv]

lemma k3_Dm_bdd (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) :
    BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) =>
      ∑ i, |k3Dm C m T u z v (p.1.2.1 i) (p.1.2.2 i)|) := by
  obtain ⟨G, hG, hDm⟩ := k3_Dm_spec A
  by_cases h : v ∈ G
  · have e : k3Dm C m T u z v = k3D C m T u z v := by rw [hDm, if_pos h]
    rw [e]; exact (k3_D_data A hv).2.2.1
  · have e : k3Dm C m T u z v = 0 := by rw [hDm, if_neg h]
    rw [e]
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    simp

theorem k3_Dm_trace_bound (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) :
    ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) ≤
      ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z v) *
        ENNReal.ofReal (s57pC d r Pw * s101Cf d r (K1 * s111k2_age c0 u v)) := by
  obtain ⟨G, hG, hDm⟩ := k3_Dm_spec A
  by_cases h : v ∈ G
  · have e : k3Dm C m T u z v = k3D C m T u z v := by rw [hDm, if_pos h]
    rw [e]; exact (k3_D_data A hv).2.2.2
  · have e : k3Dm C m T u z v = 0 := by rw [hDm, if_neg h]
    rw [e, traceNormForm_zero_eq]
    simp

/-- The integrability hypothesis of a trace density. -/
def K3Tr (C : WholeCoeff d) (m T u : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) < ⊤

lemma k3_Tr_of_L1F (A : K3Adm C m T u c0 r b Pw K1 z) (hz : IsR2L1F r Pw (u + T) z) : K3Tr C m T u z := by
  unfold K3Tr
  set K0 : ℝ := s57pC d r Pw * s101Cf d r K1 with hK0
  have hage : ∀ v, s111k2_age c0 u v ≤ 1 := fun v => by
    unfold s111k2_age
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ max (u - v) 0 := le_max_right _ _
    nlinarith [A.hc0]
  have hbd : ∀ v ∈ Icc (0 : ℝ) (u + T), ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) ≤
      ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z v) := by
    intro v hv
    refine (k3_Dm_trace_bound A hv).trans ?_
    have h1 : s101Cf d r (K1 * s111k2_age c0 u v) ≤ s101Cf d r K1 := by
      unfold s101Cf
      have h0 : 0 ≤ K1 * s111k2_age c0 u v := mul_nonneg A.hK1 (Real.exp_pos _).le
      have h2 : K1 * s111k2_age c0 u v ≤ K1 := by nlinarith [hage v, A.hK1]
      have : (K1 * s111k2_age c0 u v) ^ 2 ≤ K1 ^ 2 := pow_le_pow_left₀ h0 h2 2
      have hd : (0 : ℝ) ≤ (d : ℝ) * 2 ^ r := by positivity
      nlinarith
    have h3 : ENNReal.ofReal (s57pC d r Pw * s101Cf d r (K1 * s111k2_age c0 u v)) ≤ ENNReal.ofReal K0 :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h1 (s57pC_nonneg d r Pw))
    calc ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z v) *
          ENNReal.ofReal (s57pC d r Pw * s101Cf d r (K1 * s111k2_age c0 u v))
        ≤ ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z v) * ENNReal.ofReal K0 := mul_le_mul' le_rfl h3
      _ = ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z v) := by ring
  calc ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v))
      ≤ ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z v) :=
        setLIntegral_mono' measurableSet_Icc hbd
    _ = ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * ∫⁻ v in Icc (0 : ℝ) (u + T), dualNormE r Pw (z v) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hz.2.2

theorem k3_Dm_td (A : K3Adm C m T u c0 r b Pw K1 z) (htr : K3Tr C m T u z) :
    K3TD T u (k3Dm C m T u z) := by
  refine ⟨k3_Dm_symm A, k3_Dm_entries_meas A, fun v hv => k3_Dm_bdd A hv, ?_⟩
  have hm : Measurable fun v => HRS.traceNormForm (k3Dm C m T u z v) :=
    HRS.measurable_traceNormForm _ (k3_Dm_entries_meas A)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v => traceNormForm_nonneg _)]
  exact htr

/-! ### Linearity in `z` -/

theorem k3_D_add (A : K3Adm C m T u c0 r b Pw K1 z) (A' : K3Adm C m T u c0 r b Pw K1 z') {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (u + T)) :
    k3D C m T u (z + z') v = k3D C m T u z v + k3D C m T u z' v := by
  ext x y
  rw [k3_D_apply (A.add A') hv, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    k3_D_apply A hv, k3_D_apply A' hv]
  simp only [Pi.add_apply]
  ring

theorem k3_D_smul (c : ℝ) (A : K3Adm C m T u c0 r b Pw K1 z) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (u + T)) :
    k3D C m T u (c • z) v = c • k3D C m T u z v := by
  ext x y
  rw [k3_D_apply (A.smul c) hv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    k3_D_apply A hv]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem k3_Dm_ae_add (A : K3Adm C m T u c0 r b Pw K1 z) (A' : K3Adm C m T u c0 r b Pw K1 z') :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (u + T))),
      k3Dm C m T u (z + z') v = k3Dm C m T u z v + k3Dm C m T u z' v := by
  filter_upwards [k3_Dm_ae_eq (A.add A'), k3_Dm_ae_eq A, k3_Dm_ae_eq A', ae_restrict_mem measurableSet_Icc]
    with v h1 h2 h3 hv
  rw [h1, h2, h3, k3_D_add A A' hv]

theorem k3_Dm_ae_smul (c : ℝ) (A : K3Adm C m T u c0 r b Pw K1 z) :
    ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) (u + T))), k3Dm C m T u (c • z) v = c • k3Dm C m T u z v := by
  filter_upwards [k3_Dm_ae_eq (A.smul c), k3_Dm_ae_eq A, ae_restrict_mem measurableSet_Icc] with v h1 h2 hv
  rw [h1, h2, k3_D_smul c A hv]

theorem K3Tr.add (A : K3Adm C m T u c0 r b Pw K1 z) (A' : K3Adm C m T u c0 r b Pw K1 z')
    (h : K3Tr C m T u z) (h' : K3Tr C m T u z') : K3Tr C m T u (z + z') := by
  unfold K3Tr at *
  have hm : Measurable fun v => ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) :=
    ENNReal.measurable_ofReal.comp (HRS.measurable_traceNormForm _ (k3_Dm_entries_meas A))
  calc ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u (z + z') v))
      ≤ ∫⁻ v in Icc (0 : ℝ) (u + T), (ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) +
          ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z' v))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [k3_Dm_ae_add A A', ae_restrict_mem measurableSet_Icc] with v h1 hv
        rw [h1, ← ENNReal.ofReal_add (HRS.traceNormForm_nonneg _) (HRS.traceNormForm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (s101_tn_add_le (k3_Dm_bdd A hv) (k3_Dm_bdd A' hv))
    _ = _ + _ := lintegral_add_left hm _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h, h'⟩

theorem K3Tr.smul (c : ℝ) (A : K3Adm C m T u c0 r b Pw K1 z) (h : K3Tr C m T u z) :
    K3Tr C m T u (c • z) := by
  unfold K3Tr at *
  calc ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u (c • z) v))
      ≤ ∫⁻ v in Icc (0 : ℝ) (u + T), ENNReal.ofReal |c| *
          ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [k3_Dm_ae_smul c A, ae_restrict_mem measurableSet_Icc] with v h1 hv
        rw [h1, ← ENNReal.ofReal_mul (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (s101_tn_smul_le c (k3_Dm_bdd A hv))
    _ = ENNReal.ofReal |c| * ∫⁻ v in Icc (0 : ℝ) (u + T),
          ENNReal.ofReal (HRS.traceNormForm (k3Dm C m T u z v)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

end HRS.MS.S111K3
