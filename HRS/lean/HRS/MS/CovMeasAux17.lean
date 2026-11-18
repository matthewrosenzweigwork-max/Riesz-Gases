import HRS.MS.CovMeasAux16

/-!
# S10.1 (worker S101B), part 17: the measurable trace density `D'`

`s101Dm C m T z τ = 1_G(τ) D_τ` for a Borel set `G` of full measure with `S101Good C m T z G` (chosen once, classically).
`s101_Dm_isTraceDensity`: for admissible `z`, `s101Dm` satisfies `HRS.Uniform.IsTraceDensityL1 T`; `s101_Dm_trace_le`: the pointwise bound of its
trace norm by `2|ν| dualNormE(z^τ) K0`; `s101_Dm_ae_eq`: `D' = D` almost everywhere on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

open Classical in
/-- The measurable modification of the covariance density. -/
def s101Dm (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (τ : ℝ) :
    KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ :=
  if h : ∃ G, S101Good C m T z G then (if τ ∈ h.choose then s101D C m T z τ else 0) else 0

lemma s101_Dm_spec (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) :
    ∃ G, S101Good C m T z G ∧ ∀ τ, s101Dm C m T z τ = if τ ∈ G then s101D C m T z τ else 0 := by
  classical
  have h := s101_exists_good A hT
  refine ⟨h.choose, h.choose_spec, fun τ => ?_⟩
  unfold s101Dm
  rw [dif_pos h]

lemma traceNormForm_zero_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    HRS.traceNormForm (0 : H →L[ℝ] H →L[ℝ] ℝ) ≤ 0 := by
  unfold HRS.traceNormForm
  exact Real.iSup_le (fun p => by simp) le_rfl

theorem s101_Dm_ae_eq (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) :
    ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), s101Dm C m T z τ = s101D C m T z τ := by
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hT
  have h1 : ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), τ ∈ G := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ Icc (0 : ℝ) T \ G :=
      measure_eq_zero_iff_ae_notMem.1 hG.2.2.1
    filter_upwards [this] with τ hτ hτI
    by_contra hnot
    exact hτ ⟨hτI, hnot⟩
  filter_upwards [h1] with τ hτ
  rw [hDm, if_pos hτ]

/-- The trace norm of `D'_τ` is bounded by `2|ν| K0 dualNormE(z^τ)`. -/
theorem s101_Dm_trace_bound (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ τ ∈ Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) ≤
        ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z τ) := by
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hT
  obtain ⟨K0, hK0, hK⟩ := s101_D_data A.hd A.hP A.horb
  refine ⟨K0, hK0, fun τ hτ => ?_⟩
  by_cases h : τ ∈ G
  · have e : s101Dm C m T z τ = s101D C m T z τ := by rw [hDm, if_pos h]
    rw [e]
    refine ((hK z A.hz τ hτ).2.2.2).trans (le_of_eq ?_)
    ring
  · have e : s101Dm C m T z τ = 0 := by rw [hDm, if_neg h]
    rw [e]
    have : HRS.traceNormForm (0 : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ) ≤ 0 := traceNormForm_zero_le
    rw [ENNReal.ofReal_of_nonpos this]
    exact bot_le

/-- The integrability hypothesis of a trace density. -/
def S101Tr (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ)) < ⊤

theorem s101_htr_of_L1F (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (hz : IsR2L1F r Pw T z) :
    S101Tr C m T z := by
  obtain ⟨K0, hK0, hbound⟩ := s101_Dm_trace_bound A hT
  unfold S101Tr
  calc ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal (HRS.traceNormForm (s101Dm C m T z τ))
      ≤ ∫⁻ τ in Icc (0 : ℝ) T, ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * dualNormE r Pw (z τ) :=
        setLIntegral_mono' measurableSet_Icc hbound
    _ = ENNReal.ofReal |2 * C.ν| * ENNReal.ofReal K0 * ∫⁻ τ in Icc (0 : ℝ) T, dualNormE r Pw (z τ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ?_
        exact hz.2.2

theorem s101_Dm_isTraceDensity (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (htr : S101Tr C m T z) :
    HRS.Uniform.IsTraceDensityL1 T (s101Dm C m T z) := by
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hT
  obtain ⟨K0, hK0, hK⟩ := s101_D_data A.hd A.hP A.horb
  have hentry : ∀ τ u v, s101Dm C m T z τ u v = if τ ∈ G then s101D C m T z τ u v else 0 := by
    intro τ u v
    rw [hDm]; by_cases h : τ ∈ G <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ x y
    rw [hentry, hentry]
    by_cases h : τ ∈ G
    · simp only [h, if_true]; exact s101_D_symm A (hG.2.1 h) x y
    · simp [h]
  · intro τ hτ
    by_cases h : τ ∈ G
    · have := (hK z A.hz τ hτ).2.2.1
      have e : s101Dm C m T z τ = s101D C m T z τ := by rw [hDm, if_pos h]
      rw [e]; exact this
    · have e : s101Dm C m T z τ = 0 := by rw [hDm, if_neg h]
      rw [e]
      refine ⟨0, ?_⟩
      rintro _ ⟨p, rfl⟩
      simp
  · intro x y
    have := hG.2.2.2 x y
    convert this using 1
    funext τ
    exact hentry τ x y
  · have hmeasD : ∀ x y : KSpace d m T, Measurable fun τ => s101Dm C m T z τ x y := by
      intro x y
      have := hG.2.2.2 x y
      convert this using 1
      funext τ
      exact hentry τ x y
    have hmeas : Measurable fun τ => HRS.traceNormForm (s101Dm C m T z τ) :=
      HRS.measurable_traceNormForm _ hmeasD
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun τ => HRS.traceNormForm_nonneg _)]
    exact htr

end HRS.MS.CovMeas
