import HRS.MS.Fp81S21RSValue2

/-! Integrability and pathwise compatibility for measurable scalar RS selections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS.MS.R2Interp HRS.Whole

/-- The BV majorant is the exact one in `fp81s21_rsOn_bv_bound`.  Its
integrability hypothesis also supplies the measurability needed for domination. -/
theorem fp81s21_rs_bv_ae_integrable_selection
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {q r : ℝ} (hqr : q < r)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (hS : ∀ τ u v, Measurable (fun ω => A ω τ (F ω v - F ω u)))
    (hgood : ∀ᵐ ω ∂μ, ContinuousOn (A ω) (Icc q r) ∧
      BoundedVariationOn (F ω) (Icc q r))
    (hmaj : Integrable (fun ω =>
      (⨆ τ : Icc q r, ‖A ω τ‖) * (eVariationOn (F ω) (Icc q r)).toReal) μ) :
    ∃ I : Ω → ℝ, AEMeasurable I μ ∧
      (∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
        (fun τ u v => A ω τ (F ω v - F ω u)) (I ω)) ∧
      Integrable I μ ∧
      (∫ ω, |I ω| ∂μ ≤ ∫ ω,
        (⨆ τ : Icc q r, ‖A ω τ‖) *
          (eVariationOn (F ω) (Icc q r)).toReal ∂μ) := by
  obtain ⟨I, hIm, hI, _⟩ :=
    fp81s21_rs_bv_ae_selection μ hqr A F hS hgood
  have hbound : ∀ᵐ ω ∂μ, ‖I ω‖ ≤
      (⨆ τ : Icc q r, ‖A ω τ‖) *
        (eVariationOn (F ω) (Icc q r)).toReal := by
    filter_upwards [hgood, hI] with ω hω hωI
    rw [Real.norm_eq_abs]
    exact fp81s21_rsOn_bv_bound hqr (F ω) (A ω) hω.2 hω.1 hωI
  have hInt : Integrable I μ := hmaj.mono' hIm.aestronglyMeasurable hbound
  have hIntAbs : Integrable (fun ω => |I ω|) μ := by
    simpa only [Real.norm_eq_abs] using hInt.norm
  refine ⟨I, hIm, hI, hInt, ?_⟩
  exact integral_mono_ae hIntAbs hmaj (by
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω)

/-- On a zero-length interval every specified RS value is zero. -/
theorem fp81s21_rs_zero_length_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {q : ℝ}
    (S : Ω → ℝ → ℝ → ℝ → ℝ) (I : Ω → ℝ)
    (hI : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q q (S ω) (I ω)) :
    I =ᵐ[μ] fun _ => 0 := by
  filter_upwards [hI] with ω hω
  exact fp81s21_isRSOn_zero_forces hω

/-- The zero summand has scalar RS value zero on every ordered compact interval. -/
theorem fp81s21_isRSOn_zero_summand {q r : ℝ} (hqr : q ≤ r)
    {S : ℝ → ℝ → ℝ → ℝ} (hS : ∀ τ u v, S τ u v = 0) :
    fp81s21_IsRSOn q r S 0 := by
  unfold fp81s21_IsRSOn IsR2RS
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro n u τ hu hu0 huT htag hmesh
  have hsum : (∑ i : Fin n,
      S (q + τ i) (q + u i.castSucc) (q + u i.succ)) = 0 := by
    simp [hS]
  rw [hsum]
  simpa using hε

/-- If all increments in the random summand vanish, its a.e. selected value vanishes. -/
theorem fp81s21_rs_zero_summand_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {q r : ℝ} (hqr : q ≤ r)
    (S : Ω → ℝ → ℝ → ℝ → ℝ) (I : Ω → ℝ)
    (hzero : ∀ᵐ ω ∂μ, ∀ τ u v, S ω τ u v = 0)
    (hI : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r (S ω) (I ω)) :
    I =ᵐ[μ] fun _ => 0 := by
  filter_upwards [hzero, hI] with ω hω hωI
  by_cases hqr' : q = r
  · subst r
    exact fp81s21_isRSOn_zero_forces hωI
  · have hlt : q < r := lt_of_le_of_ne hqr hqr'
    have hzeroI := fp81s21_isRSOn_zero_summand hqr hω
    have heq := fp81s21_isRSOn_unique hlt hωI hzeroI
    exact heq

/-- A zero operator-valued integrand gives zero for the selected BV RS value. -/
theorem fp81s21_rs_bv_zero_integrand_ae
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {q r : ℝ} (hqr : q ≤ r)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E) (I : Ω → ℝ)
    (hA0 : ∀ᵐ ω ∂μ, ∀ τ, A ω τ = 0)
    (hI : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun τ u v => A ω τ (F ω v - F ω u)) (I ω)) :
    I =ᵐ[μ] fun _ => 0 := by
  apply fp81s21_rs_zero_summand_ae μ hqr
    (fun ω τ u v => A ω τ (F ω v - F ω u)) I ?_ hI
  filter_upwards [hA0] with ω hω
  intro τ u v
  simp [hω τ]

/-- A constant BV path gives zero for its selected scalar RS value. -/
theorem fp81s21_rs_bv_constant_path_ae
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {q r : ℝ} (hqr : q ≤ r)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E) (I : Ω → ℝ)
    (hFconst : ∀ᵐ ω ∂μ, ∀ u v, F ω u = F ω v)
    (hI : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun τ u v => A ω τ (F ω v - F ω u)) (I ω)) :
    I =ᵐ[μ] fun _ => 0 := by
  apply fp81s21_rs_zero_summand_ae μ hqr
    (fun ω τ u v => A ω τ (F ω v - F ω u)) I ?_ hI
  filter_upwards [hFconst] with ω hω
  intro τ u v
  rw [hω v u]
  simp

/-- Additivity of the measurable BV selections on adjacent intervals, a.e. -/
theorem fp81s21_rs_bv_split_ae_selection
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω)
    {q s r : ℝ} (hqs : q ≤ s) (hsr : s ≤ r)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (Iqr Iqs Isr : Ω → ℝ)
    (hIqr : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r
      (fun τ u v => A ω τ (F ω v - F ω u)) (Iqr ω))
    (hIqs : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q s
      (fun τ u v => A ω τ (F ω v - F ω u)) (Iqs ω))
    (hIsr : ∀ᵐ ω ∂μ, fp81s21_IsRSOn s r
      (fun τ u v => A ω τ (F ω v - F ω u)) (Isr ω)) :
    Iqr =ᵐ[μ] fun ω => Iqs ω + Isr ω := by
  filter_upwards [hIqr, hIqs, hIsr] with ω hωqr hωqs hωsr
  exact fp81s21_isRSOn_split_general hqs hsr hωqr hωqs hωsr

/-- The restriction theorem's value agrees with any selected subinterval value. -/
theorem fp81s21_rs_bv_restriction_ae_selection
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {H q r : ℝ} (hH : 0 < H) (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H)
    (S : Ω → ℝ → ℝ → ℝ → ℝ) (I J : Ω → ℝ)
    (hI : ∀ᵐ ω ∂μ, fp81s21_IsRSOn 0 H (S ω) (I ω))
    (hJ : ∀ᵐ ω ∂μ, fp81s21_IsRSOn q r (S ω) (J ω)) :
    ∀ᵐ ω ∂μ, ∃ J' : ℝ,
      fp81s21_IsRSOn q r (S ω) J' ∧ J' = J ω := by
  filter_upwards [hI, hJ] with ω hωI hωJ
  have hwhole : IsR2RS H (S ω) (I ω) := by
    simpa [fp81s21_IsRSOn] using hωI
  obtain ⟨J', hJ'⟩ := fp81s21_rs_restrict hH hwhole hq hqr hr
  have heq : J' = J ω := by
    by_cases hqr' : q = r
    · subst r
      have hJ'zero := fp81s21_isRSOn_zero_forces hJ'
      have hJzero := fp81s21_isRSOn_zero_forces hωJ
      rw [hJ'zero, hJzero]
    · have hlt : q < r := lt_of_le_of_ne hqr hqr'
      exact fp81s21_isRSOn_unique hlt hJ' hωJ
  exact ⟨J', hJ', heq⟩

#print axioms fp81s21_rs_bv_ae_integrable_selection
#print axioms fp81s21_rs_zero_length_ae
#print axioms fp81s21_isRSOn_zero_summand
#print axioms fp81s21_rs_zero_summand_ae
#print axioms fp81s21_rs_bv_zero_integrand_ae
#print axioms fp81s21_rs_bv_constant_path_ae
#print axioms fp81s21_rs_bv_split_ae_selection
#print axioms fp81s21_rs_bv_restriction_ae_selection
end HRS.Fp81.S21
end
