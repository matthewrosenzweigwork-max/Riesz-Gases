import HRS.MS.Fp81S21GaussianSourceRetained
import HRS.MC.E213U13i

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MC.E213U13

/-- First-chaos membership is unchanged when every source coordinate is changed
on a null set. -/
theorem fp81s21_firstChaos_congr_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ ξ' : ℕ → Ω → ℝ} (hξ : ∀ i, ξ i =ᵐ[P] ξ' i)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {q : ℝ} {W : Ω → B} (hW : InFirstChaos P ξ q W) :
    InFirstChaos P ξ' q W := by
  obtain ⟨hWsm, n, c, hlim⟩ := hW
  refine ⟨hWsm, n, c, ?_⟩
  have hcoords : ∀ᵐ ω ∂P, ∀ i, ξ' i ω = ξ i ω :=
    ae_all_iff.2 fun i => (hξ i).symm
  have hpoly (m : ℕ) :
      (fun ω => ∑ i ∈ Finset.range (n m), ξ' i ω • c m i) =ᵐ[P]
        fun ω => ∑ i ∈ Finset.range (n m), ξ i ω • c m i := by
    filter_upwards [hcoords] with ω hω
    simp [hω]
  exact hlim.congr fun m => by
    apply lintegral_congr_ae
    filter_upwards [hpoly m] with ω hω
    rw [hω]

/-- Scalar `InQ1` membership is unchanged when the source coordinates are
replaced by measurable a.e.-equal coordinates with the same standard Gaussian
law. -/
theorem fp81s21_InQ1_congr_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ ξ' : ℕ → Ω → ℝ} (hξ : ∀ i, ξ i =ᵐ[P] ξ' i)
    (hstd : IsStdGaussianSeq P ξ) (hstd' : IsStdGaussianSeq P ξ')
    (hm : ∀ i, Measurable (ξ i)) (hm' : ∀ i, Measurable (ξ' i))
    {Y : Ω → ℝ} (hY : InQ1 hstd hm Y) : InQ1 hstd' hm' Y := by
  have hg1 : ∀ i, g1 hstd hm i = g1 hstd' hm' i := by
    intro i
    apply Lp.ext
    filter_upwards [(memLp_xi hstd hm i).coeFn_toLp, hξ i,
      (memLp_xi hstd' hm' i).coeFn_toLp] with ω hold heq hnew
    change ((memLp_xi hstd hm i).toLp (ξ i)) ω =
      ((memLp_xi hstd' hm' i).toLp (ξ' i)) ω
    rw [hold, hnew, heq]
  have hK1 : ∀ n, K1 hstd hm n = K1 hstd' hm' n := by
    intro n
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i, (hg1 i).symm⟩
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i, hg1 i⟩
  have hspan : (⨆ n, K1 hstd hm n) = ⨆ n, K1 hstd' hm' n :=
    iSup_congr hK1
  have hQc : Qc (K1 hstd hm) = Qc (K1 hstd' hm') := by
    unfold Qc
    rw [hspan]
  obtain ⟨hmem, hclosure⟩ := hY
  refine ⟨hmem, ?_⟩
  rw [← hQc]
  exact hclosure

/-- Second-chaos membership is unchanged when every source coordinate is
changed on a null set. -/
theorem fp81s21_secondChaos_congr_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ ξ' : ℕ → Ω → ℝ} (hξ : ∀ i, ξ i =ᵐ[P] ξ' i)
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {q : ℝ} {W : Ω → B} (hW : InSecondChaos P ξ q W) :
    InSecondChaos P ξ' q W := by
  obtain ⟨hWsm, n, c, hlim⟩ := hW
  refine ⟨hWsm, n, c, ?_⟩
  have hcoords : ∀ᵐ ω ∂P, ∀ i, ξ' i ω = ξ i ω :=
    ae_all_iff.2 fun i => (hξ i).symm
  have hpoly (m : ℕ) :
      (fun ω => ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m),
        (ξ' i ω * ξ' j ω - if i = j then 1 else 0) • c m i j) =ᵐ[P]
        fun ω => ∑ i ∈ Finset.range (n m), ∑ j ∈ Finset.range (n m),
          (ξ i ω * ξ j ω - if i = j then 1 else 0) • c m i j := by
    filter_upwards [hcoords] with ω hω
    simp [hω]
  exact hlim.congr fun m => by
    apply lintegral_congr_ae
    filter_upwards [hpoly m] with ω hω
    rw [hω]

/-- A measurable representative of each retained source coordinate. -/
noncomputable def fp81s21_gaussian_source_measurableXi
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
    (D : fp81s21_gaussian_source_retained_data p R hμ₀) :
    ℕ → D.G0.Ω → ℝ :=
  fun i => (D.ξAemeasurable i).mk (D.ξ i)

/-- The measurable representatives agree coordinatewise almost everywhere and
retain the standard Gaussian sequence law. -/
theorem fp81s21_gaussian_source_measurable_coords_std
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
    (D : fp81s21_gaussian_source_retained_data p R hμ₀) :
    (∀ i, Measurable (fp81s21_gaussian_source_measurableXi D i)) ∧
    (∀ i, D.ξ i =ᵐ[D.G0.P] fp81s21_gaussian_source_measurableXi D i) ∧
    IsStdGaussianSeq D.G0.P (fp81s21_gaussian_source_measurableXi D) := by
  have hstd : IsStdGaussianSeq D.G0.P D.ξ := by
    rcases D.rawBundle with ⟨_, _, hstd, _⟩
    exact hstd
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (D.ξAemeasurable i).measurable_mk
  · intro i
    exact (D.ξAemeasurable i).ae_eq_mk
  · have hae : ∀ i, D.ξ i =ᵐ[D.G0.P]
        fp81s21_gaussian_source_measurableXi D i := fun i =>
      (D.ξAemeasurable i).ae_eq_mk
    refine ⟨iIndepFun.congr hae hstd.1, ?_⟩
    intro i
    calc
      D.G0.P.map (fp81s21_gaussian_source_measurableXi D i) =
          D.G0.P.map (D.ξ i) := Measure.map_congr (hae i).symm
      _ = gaussianReal 0 1 := by simpa [HRS.law] using hstd.2 i

/-- Every retained isonormal value is in the first chaos generated by the
retained coordinates: the finite series polynomials converge by `rawBundle`'s
`hWlim` clause. -/
theorem fp81s21_gaussian_source_W_firstChaos
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
    (D : fp81s21_gaussian_source_retained_data p R hμ₀)
    (h : GaussianFeatureHilbert) :
    InFirstChaos D.G0.P D.ξ 2 (D.W h) := by
  rcases D.rawBundle with ⟨_, _, hstd, _, hW2, hWlim, _⟩
  have hξlaw : ∀ i, HasLaw (D.ξ i) (gaussianReal 0 1) D.G0.P := by
    intro i
    exact ⟨D.ξAemeasurable i,
      by simpa [HRS.law] using hstd.2 i⟩
  have hξmem : ∀ i, MemLp (D.ξ i) 2 D.G0.P :=
    fun i => HRS.HilbertCLTAux.gauss_memLp hξlaw i
  exact s21g2_s11a_firstChaos D.ξ hξmem
    (fun k => inner ℝ (D.e k) h) (hW2 h) (hWlim h)

/-- The retained source evaluation belongs to first chaos for every
nonnegative time and every oscillator test. -/
theorem fp81s21_gaussian_source_eval_firstChaos
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
    (D : fp81s21_gaussian_source_retained_data p R hμ₀)
    (u : ℝ) (hu : 0 ≤ u)
    (φ : {ψ : Euc p.d → ℝ // IsOscTest (wholeSpaceIndex p.d : ℝ) ψ}) :
    InFirstChaos D.G0.P D.ξ 2
      (fun ω => OscDual.eval (D.G0.Z u ω) φ.1) := by
  have hW := fp81s21_gaussian_source_W_firstChaos D
    (D.J (fp81s21_combinedFeature p R D.hK u φ.1))
  exact HRS.MC.E213U13.InFirstChaos.congr_ae
    (D.sourceEvaluation u hu φ.1 φ.2).symm hW

/-- The retained scalar Gaussian space can use measurable representatives of
its source coordinates.  The standard law, coordinatewise a.e. equality, and
first-chaos certificates for all required evaluations are retained together. -/
theorem fp81s21_gaussian_source_measurable_eval_firstChaos
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
    (D : fp81s21_gaussian_source_retained_data p R hμ₀) :
    (∀ i, Measurable (fp81s21_gaussian_source_measurableXi D i)) ∧
    IsStdGaussianSeq D.G0.P (fp81s21_gaussian_source_measurableXi D) ∧
    (∀ i, D.ξ i =ᵐ[D.G0.P] fp81s21_gaussian_source_measurableXi D i) ∧
    (∀ u : ℝ, 0 ≤ u →
      ∀ φ : {ψ : Euc p.d → ℝ // IsOscTest (wholeSpaceIndex p.d : ℝ) ψ},
      InFirstChaos D.G0.P (fp81s21_gaussian_source_measurableXi D) 2
        (fun ω => OscDual.eval (D.G0.Z u ω) φ.1)) := by
  obtain ⟨hmeas, hae, hstd⟩ := fp81s21_gaussian_source_measurable_coords_std D
  refine ⟨hmeas, hstd, hae, ?_⟩
  intro u hu φ
  exact fp81s21_firstChaos_congr_coordinates hae
    (fp81s21_gaussian_source_eval_firstChaos D u hu φ)

#print axioms fp81s21_firstChaos_congr_coordinates
#print axioms fp81s21_secondChaos_congr_coordinates
#print axioms fp81s21_InQ1_congr_coordinates
#print axioms fp81s21_gaussian_source_measurable_coords_std
#print axioms fp81s21_gaussian_source_W_firstChaos
#print axioms fp81s21_gaussian_source_eval_firstChaos
#print axioms fp81s21_gaussian_source_measurable_eval_firstChaos

end HRS.Fp81.S21
end
