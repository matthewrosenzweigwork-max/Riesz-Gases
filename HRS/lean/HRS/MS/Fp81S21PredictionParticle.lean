import HRS.MS.Fp81S21PredictionPhysicalDefs
import HRS.MS.Fp81S21WindowSup13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_particle_CH_measSpace (H : ℝ) :
    MeasurableSpace (CH H) := borel _
local instance fp81s21_particle_CH_borelSpace (H : ℝ) :
    BorelSpace (CH H) := ⟨rfl⟩

/-- Chart and time evaluation commute with the path-valued Bochner mean. -/
theorem fp81s21_particle_centered_chart
    {p : Parameters} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ) (b H : ℝ) (X : Ω → CH H)
    (hX : CD E μ Q b H X) :
    ∀ᵐ ω ∂μ, ∀ t : I H, ∀ f, IsR2Test f →
      fp81s21_chartAction E (cen μ X ω t) f =
        Q (b + (t : ℝ)) ω f - ∫ ω', Q (b + (t : ℝ)) ω' f ∂μ := by
  have hInt : Integrable X μ := hX.2.1.integrable one_le_two
  filter_upwards [hX.2.2] with ω hω
  intro t f hf
  let S : CH H →L[ℝ] ℝ := (innerSL ℝ (E.encode f)).comp (ContinuousMap.evalCLM ℝ t)
  have hS (x : CH H) : S x = fp81s21_chartAction E (x t) f := by
    simp [S, fp81s21_chartAction, real_inner_comm]
  have hmean : fp81s21_chartAction E ((∫ ω', X ω' ∂μ) t) f =
      ∫ ω', Q (b + (t : ℝ)) ω' f ∂μ := by
    rw [← hS, ← S.integral_comp_comm hInt]
    apply integral_congr_ae
    filter_upwards [hX.2.2] with ω' hω'
    exact (hS (X ω')).trans (hω' t f hf)
  change fp81s21_chartAction E (X ω t - (∫ ω', X ω' ∂μ) t) f = _
  simp only [fp81s21_chartAction, inner_sub_left]
  change fp81s21_chartAction E (X ω t) f -
    fp81s21_chartAction E ((∫ ω', X ω' ∂μ) t) f = _
  rw [hω t f hf, hmean]

/-- The centered physical chart represents the exactly centered empirical field. -/
theorem fp81s21_particle_centered_zf
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ} (hN : 2 ≤ N)
    (A : Particle R N) (E : r26t6_WeightedChart p.d (r p) (Pw p))
    (b H : ℝ) (hb : 0 ≤ b) (X : A.Ω → CH H)
    (hX : CD E A.P (fp81s21_particleEmpField R N A) b H X) :
    ∀ᵐ ω ∂A.P, ∀ t : I H, ∀ f, IsR2Test f →
      fp81s21_chartAction E (cen A.P X ω t) f =
        s102_zf A.P A.X ω (b + (t : ℝ)) f := by
  have hN0 : 0 < N := by omega
  have hXm : ∀ u, Measurable (A.X u) := (A.strong (b + H)).adapted
  filter_upwards [fp81s21_particle_centered_chart E A.P
    (fp81s21_particleEmpField R N A) b H X hX] with ω hω
  intro t f hf
  have ht : b + (t : ℝ) ∈ I (b + H) := by
    constructor <;> linarith [t.2.1, t.2.2]
  letI : IsProbabilityMeasure (r26t3_mu R (b + (t : ℝ))) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu
      ((R.resulting.global (b + H)).density _ ht)
  obtain ⟨B, hB⟩ := HRS.MS.R2Chaos.s94_test_bounded hf
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  have hz := fp81s21_window_s102_zf_centered_raw A.P A.X (b + (t : ℝ))
    (hXm _) hN0 (r26t3_mu R (b + (t : ℝ))) hf.1.continuous.measurable
    hB0 hB ω
  rw [hω t f hf]
  simpa only [fp81s21_particleEmpField_eq_sqrt_pair] using hz.symm

#print axioms HRS.Fp81.S21.fp81s21_particle_centered_chart
#print axioms HRS.Fp81.S21.fp81s21_particle_centered_zf

end HRS.Fp81.S21
