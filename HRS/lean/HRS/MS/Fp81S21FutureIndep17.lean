import HRS.MS.Fp81S21FutureIndep12
import HRS.MS.Fp81S21FutureIndep15
import HRS.MS.Fp81S21FutureIndep16

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath

/-- The packet 12 future law has a measurable version on the retained source,
independent of the complete initial-and-past supported noise family. -/
theorem fp81s21_future_path_independent_of_past_source
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) H)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h)) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (hcov : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h')
    (γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)) [IsProbabilityMeasure γ]
    (hγ : IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r γ) :
    ∃ X : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
      Measurable X ∧ P.map X = γ ∧
      (∃ s : ℕ → Icc (0 : ℝ) H, DenseRange s ∧
        ∀ᵐ ω ∂P, ∀ i : ℕ × MultiIndex p.d,
          OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2 =
            W (J (fp81s21_futureNoiseSourceFeature p R r (s i.1)
              (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2))) ω) ∧
      IndepFun
        (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
          W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) X P := by
  letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, le_rfl, hH.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) H := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  obtain ⟨X, hXm, hXlaw, hXcoords⟩ :=
    fp81s21_future_source_path p R hδ hδhalf hH hr P J W hWm hcomb hcov γ hγ s hs
  let b : ℕ × MultiIndex p.d → fp81s21_FutureNoiseFeatures p.d r := fun i =>
    ⟨movingNoiseFeature R r (s i.1) (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2),
      fp81s21_future_feature_supported p R hδ hδhalf hH hr (s i.1).property
        (s56_isOscTest (wholeSpaceIndex p.d : ℝ) i.2)⟩
  let B : fp81s21_FutureNoiseFeatures p.d r → Ω → ℝ := fun j =>
    W (J (WithLp.toLp 2 (0, j.1)))
  let past := fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
    W (J (WithLp.toLp 2 (i.1, i.2.1))) ω
  have hind : IndepFun past (fun ω j => B j ω) P :=
    fp81s21_supported_source_families_independent p R r P J W hWm hW2 hcomb hcov
  have hcoord : ∀ i, (fun ω => OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2)
      =ᵐ[P] B (b i) := by
    intro i
    filter_upwards [hXcoords] with ω hω
    simpa [B, b, fp81s21_futureNoiseSourceFeature] using hω i
  have hfinal := fp81s21_path_indep_of_source_coordinates hH.le P past B
    (fun j => hWm _) hind X s hs b hcoord
  exact ⟨X, hXm, hXlaw, ⟨s, hs, hXcoords⟩, hfinal.2⟩

#print axioms fp81s21_future_path_independent_of_past_source

end HRS.Fp81.S21
end
