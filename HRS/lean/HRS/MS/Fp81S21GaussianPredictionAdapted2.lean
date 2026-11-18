import HRS.MS.Fp81S21GaussianPredictionAdapted
import HRS.MS.Fp81S21FutureIndep39

/-! Exact past-measurable representatives of the retained chart coefficients.
Only compact chart tests are used; no oscillator regularity is assumed for
propagated tests. The source and canonical family remain unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- The entire retained initial-and-past-noise source at cutoff `r`. -/
def fp81s21_predictionPast (Q : fp81s21_Gaussian35Selection p R) (r : ℝ)
    (ω : Q.src.G0.Ω)
    (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) : ℝ :=
  Q.src.W (Q.src.J (WithLp.toLp 2 (i.1, i.2.1))) ω

private theorem fp81s21_prediction_noise_supported
    (u r : ℝ) (hur : u ≤ r) (φ : Euc p.d → ℝ) :
    movingNoiseFeature R 0 u φ ∈ fp81s21_PastNoiseFeatures p.d r := by
  unfold movingNoiseFeature
  split_ifs with hm
  · filter_upwards [hm.coeFn_toLp] with q hq
    intro hrq
    rw [hq]
    have hnot : q.1 ∉ Icc (0 : ℝ) u := fun h => (not_lt_of_ge (h.2.trans hur)) hrq
    simp only [movingNoiseKernel, if_neg hnot]
  · filter_upwards [Lp.coeFn_zero (Euc p.d) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d)))] with q hq
    intro _
    exact hq

private theorem fp81s21_prediction_chart_coordinate
    (Q : fp81s21_Gaussian35Selection p R) (z : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction Q.E z (Q.E.test j) = z j := by
  have he : Q.E.encode (Q.E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change Q.E.encode (Q.E.test j) i = _
    rw [Q.E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, he]
  simpa [lp.inner_single_right]

/-- At each source time before the cutoff, the retained canonical coefficient
has an ambient measurable, exactly past-measurable representative. -/
theorem fp81s21_gaussian_prediction_coefficient_adapted
    (Q : fp81s21_Gaussian35Selection p R) (u r : ℝ) (hu : 0 ≤ u) (hur : u ≤ r) :
    ∃ q : Q.src.G0.Ω → r26t6_Coeff,
      Measurable q ∧
      Measurable[MeasurableSpace.comap (fp81s21_predictionPast Q r) inferInstance] q ∧
      fp81s21_gaussian35_qG Q u =ᵐ[Q.src.G0.P] q := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  let b : ℕ → Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r := fun j =>
    (fp81s21_initialGaussianFeature p R Q.src.hK u (Q.E.test j),
      ⟨movingNoiseFeature R 0 u (Q.E.test j),
        fp81s21_prediction_noise_supported u r hur (Q.E.test j)⟩)
  let select : (Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r → ℝ) →
      (ℕ → ℝ) := fun z j => z (b j)
  have hs : Measurable select := measurable_pi_iff.2 fun j => measurable_pi_apply (b j)
  let coords : r26t6_Coeff → (ℕ → ℝ) := fun z j => z j
  have hc : Continuous coords := continuous_pi fun j =>
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).continuous
  have hi : Function.Injective coords := by
    intro x y h
    ext j
    exact congrFun h j
  have hemb := hc.measurableEmbedding hi
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨0⟩)
  let q := fun ω => g (select (fp81s21_predictionPast Q r ω))
  have hp : Measurable (fp81s21_predictionPast Q r) :=
    measurable_pi_iff.2 fun i => Q.src.rawBundle.2.2.2.1 _
  refine ⟨q, hgm.comp (hs.comp hp),
    hgm.comp (hs.comp (comap_measurable (fp81s21_predictionPast Q r))), ?_⟩
  have hcoords : ∀ j, ∀ᵐ ω ∂Q.src.G0.P,
      fp81s21_gaussian35_qG Q u ω j = fp81s21_predictionPast Q r ω (b j) := by
    intro j
    have hrep := ((Q.canon.payload Q.src.G0).coefficients.weak_momentRep.2 u hu).2.2
    have he := Q.src.sourceEvaluation u hu (Q.E.test j)
      (r2Test_isOscTest _ (Q.E.test_smooth j))
    filter_upwards [hrep, he] with ω hω heω
    calc
      fp81s21_gaussian35_qG Q u ω j =
          fp81s21_chartAction Q.E (fp81s21_gaussian35_qG Q u ω) (Q.E.test j) :=
        (fp81s21_prediction_chart_coordinate Q _ j).symm
      _ = OscDual.eval (Q.src.G0.Z u ω) (Q.E.test j) := hω.1 _ (Q.E.test_smooth j)
      _ = fp81s21_predictionPast Q r ω (b j) := heω
  filter_upwards [ae_all_iff.2 hcoords] with ω hω
  have he : coords (fp81s21_gaussian35_qG Q u ω) = select (fp81s21_predictionPast Q r ω) :=
    funext hω
  change fp81s21_gaussian35_qG Q u ω = g (select (fp81s21_predictionPast Q r ω))
  rw [← he]
  exact (congrFun hg _).symm

#print axioms fp81s21_gaussian_prediction_coefficient_adapted
end HRS.Fp81.S21
end
