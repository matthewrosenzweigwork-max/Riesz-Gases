import HRS.MS.Fp81S21FutureIndep21
import HRS.MS.ProClosureS111GaussianLaw

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.MovOsc

private theorem fp81s21_source_finset_linear
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ) (hstd : HRS.IsStdGaussianSeq P ξ)
    (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun n : ℕ => ∫ ω,
      (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω - W h ω) ^ 2 ∂P) atTop (𝓝 0))
    {ι : Type*} (f : ι → GaussianFeatureHilbert) (c : ι → ℝ) (S : Finset ι) :
    W (∑ i ∈ S, c i • f i) =ᵐ[P] fun ω => ∑ i ∈ S, c i * W (f i) ω := by
  have hl := fp81s21_series_linear e ξ W hstd hW2 hWlim
  induction S using Finset.induction_on with
  | empty =>
      have hz := hl 0 0 1
      filter_upwards [hz] with ω hω
      simpa using (show W 0 ω = 0 by simp only [add_zero, one_smul] at hω; linarith)
  | @insert a S ha ih =>
      have hh := hl (∑ i ∈ S, c i • f i) (f a) (c a)
      filter_upwards [hh, ih] with ω hω hS
      rw [Finset.sum_insert ha]
      have he : W (c a • f a + ∑ i ∈ S, c i • f i) ω =
          W (∑ i ∈ S, c i • f i) ω + c a * W (f a) ω := by
        simpa [add_comm, add_left_comm, add_assoc] using hω
      rw [he, hS]
      simp only [Finset.sum_insert ha]
      ring

/-- A bounded linear feature map extends oscillator-coordinate identities to
all oscillator tests, with an exceptional set for each individual test. -/
theorem fp81s21_source_all_test_eval
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (e : ℕ → GaussianFeatureHilbert) (ξ : ℕ → Ω → ℝ)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hParseval : ∀ h h' : GaussianFeatureHilbert,
      HasSum (fun n => inner ℝ (e n) h * inner ℝ (e n) h') (inner ℝ h h'))
    (hstd : HRS.IsStdGaussianSeq P ξ) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hWlim : ∀ h, Tendsto (fun n : ℕ => ∫ ω,
      (s21g2_s11a_S ξ (fun k => inner ℝ (e k) h) n ω - W h ω) ^ 2 ∂P) atTop (𝓝 0))
    (v : Ω → OscDual d m) (hvm : Measurable v)
    (F : oscSub d m →ₗ[ℝ] GaussianFeatureHilbert)
    (hF : ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : oscSub d m,
      ‖F φ‖ ≤ B * oscNorm m (φ : Euc d → ℝ))
    (hc : ∀ α : MultiIndex d, (fun ω => OscDual.coord (v ω) α) =ᵐ[P]
      W (F (initialTestBasis m α)))
    (φ : oscSub d m) : (fun ω => OscDual.eval (v ω) (φ : Euc d → ℝ)) =ᵐ[P] W (F φ) := by
  let q : ℕ → oscSub d m := initialTestSection φ
  let U : ℕ → Ω → ℝ := fun n ω => OscDual.eval (v ω) (q n : Euc d → ℝ)
  let V : Ω → ℝ := fun ω => OscDual.eval (v ω) (φ : Euc d → ℝ)
  have hUm : ∀ n, AEStronglyMeasurable (U n) P := by
    intro n
    have hh := (gaussianOscEval (q n)).continuous.measurable.comp hvm
    simpa only [Function.comp_def, gaussianOscEval_apply, U] using hh.aestronglyMeasurable
  have hp : ∀ᵐ ω ∂P, Tendsto (fun n => U n ω) atTop (𝓝 (V ω)) :=
    Filter.Eventually.of_forall fun ω => initialTestSection_eval_tendsto φ (v ω)
  have hleft : TendstoInMeasure P U atTop V := tendstoInMeasure_of_tendsto_ae hUm hp
  let Z : ℕ → Ω → ℝ := fun n => W (F (q n))
  have hFq := linear_feature_section_tendsto F hF φ
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero).1 hFq
  have hdist : Tendsto (fun n => ∫ ω, (Z n ω - W (F φ) ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hs : Tendsto (fun n => ‖F (q n) - F φ‖ ^ 2) atTop (𝓝 0) := by
      simpa [q] using hnorm.pow 2
    apply hs.congr
    intro n
    exact (fp81s21_series_distance e ξ W hParseval hstd hW2 hWlim _ _).symm
  have hL2 : HRS.TendstoL2 P Z (W (F φ)) :=
    HRS.tendstoL2_of_memLp (hW2 _) (fun n => hW2 _) hdist
  have hright : TendstoInMeasure P Z atTop (W (F φ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (hL2.tendsto_eLpNorm (fun n => (hW2 _).aestronglyMeasurable))
  have hUZ : ∀ n, U n =ᵐ[P] Z n := by
    intro n
    have hsum := fp81s21_source_finset_linear P e ξ W hstd hW2 hWlim
      (fun α : MultiIndex d => F (initialTestBasis m α))
      (fun α => oscEigenvalue d α ^ (m / 2) * HRS.Whole.hermiteCoeff φ α)
      (mova2_S d n)
    have hcoords : ∀ᵐ ω ∂P, ∀ α, OscDual.coord (v ω) α = W (F (initialTestBasis m α)) ω := ae_all_iff.2 hc
    filter_upwards [hsum, hcoords] with ω hsumω hcω
    have hfeature : F (q n) = ∑ α ∈ mova2_S d n,
        (oscEigenvalue d α ^ (m / 2) * HRS.Whole.hermiteCoeff φ α) • F (initialTestBasis m α) := by
      simp only [q, initialTestSection, map_sum, map_smul]
    change OscDual.eval (v ω) (initialTestSection φ n : Euc d → ℝ) = W (F (q n)) ω
    rw [initialTestSection_eval, hfeature, hsumω]
    exact Finset.sum_congr rfl (fun α _ => by rw [hcω α])
  have hright' : TendstoInMeasure P U atTop (W (F φ)) :=
    hright.congr (fun n => (hUZ n).symm) (Filter.Eventually.of_forall fun _ => rfl)
  exact tendstoInMeasure_ae_unique hleft hright'

#print axioms fp81s21_source_all_test_eval
end HRS.Fp81.S21
end
