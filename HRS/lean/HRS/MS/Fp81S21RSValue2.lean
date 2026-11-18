import HRS.MS.Fp81S21RSValue

/-! Scalar RS selections from BV sample paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21

/-- Continuous integrands against BV paths have a measurable scalar RS selection,
provided the scalar summands at deterministic tags and endpoints are measurable. -/
theorem fp81s21_rs_bv_measurable_selection {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q r : ℝ} (hqr : q < r) (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (hS : ∀ τ u v, Measurable (fun ω => A ω τ (F ω v - F ω u)))
    (hA : ∀ ω, ContinuousOn (A ω) (Icc q r))
    (hF : ∀ ω, BoundedVariationOn (F ω) (Icc q r)) :
    ∃ I : Ω → ℝ, Measurable I ∧
      ∀ ω, fp81s21_IsRSOn q r (fun τ u v => A ω τ (F ω v - F ω u)) (I ω) := by
  have hex : ∀ ω, ∃ i, fp81s21_IsRSOn q r
      (fun τ u v => A ω τ (F ω v - F ω u)) i :=
    fun ω => fp81s21_rsOn_bv_exists hqr (F ω) (A ω) (hF ω) (hA ω)
  choose I hI using hex
  exact ⟨I, fp81s21_rs_value_measurable hqr _ I hS hI, hI⟩

/-- An a.e. BV/continuity event yields an a.e.-measurable RS selection;
the value is zero wherever no RS value exists. -/
theorem fp81s21_rs_bv_ae_selection {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) {q r : ℝ} (hqr : q < r)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (hS : ∀ τ u v, Measurable (fun ω => A ω τ (F ω v - F ω u)))
    (hgood : ∀ᵐ ω ∂μ, ContinuousOn (A ω) (Icc q r) ∧
      BoundedVariationOn (F ω) (Icc q r)) :
    ∃ I : Ω → ℝ, AEMeasurable I μ ∧
      (∀ᵐ ω ∂μ, fp81s21_IsRSOn q r (fun τ u v => A ω τ (F ω v - F ω u)) (I ω)) ∧
      (∀ ω, (¬ ∃ i, fp81s21_IsRSOn q r
        (fun τ u v => A ω τ (F ω v - F ω u)) i) → I ω = 0) := by
  classical
  let P : Ω → ℝ → Prop := fun ω i => fp81s21_IsRSOn q r
    (fun τ u v => A ω τ (F ω v - F ω u)) i
  let I : Ω → ℝ := fun ω => if h : ∃ i, P ω i then Classical.choose h else 0
  have hI : ∀ᵐ ω ∂μ, P ω (I ω) := by
    filter_upwards [hgood] with ω hω
    have hex : ∃ i, P ω i := fp81s21_rsOn_bv_exists hqr (F ω) (A ω) hω.2 hω.1
    simpa [I, hex] using Classical.choose_spec hex
  refine ⟨I, fp81s21_rs_value_aemeasurable μ hqr _ I hS hI, hI, ?_⟩
  intro ω h
  change ¬ ∃ i, P ω i at h
  simp [I, h]

#print axioms fp81s21_rs_bv_measurable_selection
#print axioms fp81s21_rs_bv_ae_selection
end HRS.Fp81.S21
end
