import HRS.MS.Fp81S21FutureIndep13
import HRS.MS.Fp81S21FutureIndep14

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath HRS.MS.R2Interp

/-- The selected future law is realized on the retained source; the dense
oscillator coordinates are the corresponding future-source evaluations. -/
theorem fp81s21_future_source_path
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) H)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h))
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (hcov : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h')
    (γ : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H)) [IsProbabilityMeasure γ]
    (hγ : IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r γ)
    (s : ℕ → Icc (0 : ℝ) H) (hs : DenseRange s) :
    ∃ X : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
      Measurable X ∧ P.map X = γ ∧
      ∀ᵐ ω ∂P, ∀ i : ℕ × MultiIndex p.d,
        OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2 =
          W (J (fp81s21_futureNoiseSourceFeature p R r (s i.1)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2))) ω := by
  let m : ℝ := wholeSpaceIndex p.d
  let Ψ := s56PathCoords (d := p.d) m H s
  let U : Ω → (ℕ × MultiIndex p.d → ℝ) := fun ω i =>
    W (J (fp81s21_futureNoiseSourceFeature p R r (s i.1)
      (oscTestFun m i.2))) ω
  have hUm : Measurable U := measurable_pi_iff.2 fun i => hWm _
  have hΨm : Measurable Ψ := s56_measurable_pathCoords m H s
  have hlaw : P.map U = γ.map Ψ := by
    apply s56_seq_law_eq P γ U Ψ hUm.aemeasurable hΨm.aemeasurable
    intro n f hf
    let τ : Fin n → Icc (0 : ℝ) H := fun i => s (f i).1
    let α : Fin n → MultiIndex p.d := fun i => (f i).2
    let F : Fin n → GaussianFeatureHilbert := fun i =>
      J (fp81s21_futureNoiseSourceFeature p R r (τ i) (oscTestFun m (α i)))
    have hmat : (Matrix.of fun i j => inner ℝ (F i) (F j)) =
        s102_obsCov (r26t3_coeff R) m τ α r := by
      ext i j
      have hfeat := (movingNoiseFeature_spec p R hδ hδhalf hH).2 r hr
        (τ i) (τ i).property (τ j) (τ j).property
        (oscTestFun m (α i)) (oscTestFun m (α j))
        (s56_isOscTest m (α i)) (s56_isOscTest m (α j))
      have hp := WithLp.prod_inner_apply (𝕜 := ℝ)
        (WithLp.toLp 2 (0, movingNoiseFeature R r (τ i) (oscTestFun m (α i))) :
          Fp81S21GaussFeatureHilbert p R)
        (WithLp.toLp 2 (0, movingNoiseFeature R r (τ j) (oscTestFun m (α j))) :
          Fp81S21GaussFeatureHilbert p R)
      simp only [Matrix.of_apply, F, J.inner_map_map, fp81s21_futureNoiseSourceFeature]
      rw [hp]
      have hnu : (r26t3_coeff R).ν = p.β⁻¹ := rfl
      have hrho : (r26t3_coeff R).ρ = R.ρ := rfl
      simpa [s102_obsCov, hnu, hrho, r26t3_U] using hfeat
    have hsource := fp81s21_source_finite_law P W hWm hcomb hcov n F
    have hfuture := (s102_obs_law (r26t3_coeff R) hγ τ α).2
    have hobs : (s102_obs τ α : OscPath p.d m H → EuclideanSpace ℝ (Fin n)) =
        (fun w => WithLp.toLp 2 (fun i => OscDual.coord (OscPath.at' w (τ i)) (α i))) := by
      funext w
      ext i
      exact s102_obs_apply τ α w i
    rw [hmat] at hsource
    rw [hobs] at hfuture
    simpa [U, Ψ, s56PathCoords, F, τ, α] using hsource.trans hfuture.symm
  exact fp81s21_path_from_coordinate_law P γ s hs U hUm hlaw

#print axioms fp81s21_future_source_path

end HRS.Fp81.S21
end
