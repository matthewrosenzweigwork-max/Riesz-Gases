import HRS.MS.Fp81S21GaussianIncrementAdapted

/-! Packet 36: adaptation of the actual retained quadratic coefficients and
integrability of both literal cumulative increments. Only countably many chart
coordinates are intersected. Time-integrated past adaptation and finite spatial
approximations remain separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

private theorem fp81s21_increment_chart_coordinate
    (Q : fp81s21_Physical35 p R) (z : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction Q.E z (Q.E.test j) = z j := by
  have he : Q.E.encode (Q.E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change Q.E.encode (Q.E.test j) i = _
    rw [Q.E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, he]
  simpa [lp.inner_single_right]

/-- The actual retained quadratic coefficient field is measurable in the
retained past at each fixed source time before the cutoff. The identification
uses the supplied half-Wick operator and its compact-test agreement. -/
theorem fp81s21_gaussian_quadratic_past_adapted
    (Q : fp81s21_Physical35 p R) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance]
      (Q.S.qe Q.src.G0 u) Q.src.G0.P := by
  let m := MeasurableSpace.comap
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  have hcoord (j : ℕ) : AEStronglyMeasurable[m]
      (fun ω => Q.S.qe Q.src.G0 u ω j) Q.src.G0.P := by
    obtain ⟨hk, hag⟩ := (Q.S.payload Q.src.G0).2.2.2.2.2.1
      u hu (Q.E.test j) (Q.E.test_smooth j)
    have hrep := (((Q.S.payload Q.src.G0).2.2.2.2.1).2 u hu).2.2
    have he : (Q.S.W Q.src.G0 u (hk.toLp _) : Q.src.G0.Ω → ℝ) =ᵐ[Q.src.G0.P]
        (fun ω => Q.S.qe Q.src.G0 u ω j) := by
      filter_upwards [hag, hrep] with ω hagω hrepω
      have hx := hrepω.1 (Q.E.test j) (Q.E.test_smooth j)
      rw [fp81s21_increment_chart_coordinate Q] at hx
      exact hagω.symm.trans hx.symm
    exact (fp81s21_gaussian_halfWick_past_adapted Q u v hu huv _).congr he
  let coords : r26t6_Coeff → (ℕ → ℝ) := fun z j => z j
  have hc : Continuous coords := continuous_pi fun j =>
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).continuous
  have hi : Function.Injective coords := by
    intro x y h
    ext j
    exact congrFun h j
  obtain ⟨g, hgm, hg⟩ := hc.measurableEmbedding hi |>.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨0⟩)
  let c : Q.src.G0.Ω → (ℕ → ℝ) := fun ω j =>
    (hcoord j).mk (fun ω => Q.S.qe Q.src.G0 u ω j) ω
  have hcm : Measurable[m] c := by
    letI : MeasurableSpace Q.src.G0.Ω := m
    exact measurable_pi_iff.2 fun j => (hcoord j).measurable_mk
  have he : (fun ω => g (c ω)) =ᵐ[Q.src.G0.P] Q.S.qe Q.src.G0 u := by
    have hall := ae_all_iff.2 (fun j => (hcoord j).ae_eq_mk)
    filter_upwards [hall] with ω hω
    have hx : coords (Q.S.qe Q.src.G0 u ω) = c ω := funext hω
    rw [← hx]
    exact congrFun hg _
  exact (hgm.comp hcm).stronglyMeasurable.aestronglyMeasurable.congr he

/-- Both actual increments are integrable in their original target spaces,
including the projective tensor subspace for covariance. This follows directly
from the retained L² histories and their supplied continuous linear operators;
no terminal-moment or past-adaptation hypothesis is substituted. -/
theorem fp81s21_gaussian_increments_integrable
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a) (u v : ℝ) :
    Integrable (fun ω =>
      fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) v ω -
      fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) u ω)
      Q.src.G0.P ∧
    Integrable (fun ω =>
      fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) v ω -
      fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) u ω)
      Q.src.G0.P := by
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  have hB := (Q.hUB a ha).2.1.integrable one_le_two
  have hG := (Q.hUG a ha).2.1.integrable one_le_two
  let T := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le)
  have hD (t : ℝ) : Integrable
      (fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) t)
      Q.src.G0.P := ((Q.OD a ha).drift 0 t |>.comp T).integrable_comp hB
  have hJ (t : ℝ) : Integrable
      (fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) t)
      Q.src.G0.P := ((Q.OJ a ha).covariance 0 t |>.comp T).integrable_comp hG
  exact ⟨(hD v).sub (hD u), (hJ v).sub (hJ u)⟩

#print axioms fp81s21_gaussian_quadratic_past_adapted
#print axioms fp81s21_gaussian_increments_integrable
end HRS.Fp81.S21
end
