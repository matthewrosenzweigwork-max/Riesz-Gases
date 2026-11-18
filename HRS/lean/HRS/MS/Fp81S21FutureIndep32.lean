import HRS.MS.Fp81S21FutureIndep31
import HRS.MS.Fp81S21GaussLaw2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2 HRS.MS.GenPath

/-- Reconstruct the full initial-plus-noise Gaussian path on the retained
source, with every dense oscillator coordinate identified. -/
theorem fp81s21_combined_source_path
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ) (hWm : ∀ h, Measurable (W h))
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (hcov : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h')
    (G : GaussianRealization R) (s : ℕ → Icc (0 : ℝ) H) (hs : DenseRange s) :
    ∃ X : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
      Measurable X ∧
      (∀ᵐ ω ∂P, ∀ i : ℕ × MultiIndex p.d,
        OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2 =
          W (J (fp81s21_combinedFeature p R hK (s i.1)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2))) ω) ∧
      P.map X = G.P.map (processWindow (wholeSpaceIndex p.d : ℝ) H 0 G.Z) := by
  let m : ℝ := wholeSpaceIndex p.d
  let Ψ := s56PathCoords (d := p.d) m H s
  let U : Ω → (ℕ × MultiIndex p.d → ℝ) := fun ω i =>
    W (J (fp81s21_combinedFeature p R hK (s i.1) (oscTestFun m i.2))) ω
  let V : G.Ω → (ℕ × MultiIndex p.d → ℝ) := fun ω i =>
    OscDual.coord (G.Z (s i.1) ω) i.2
  have hUm : Measurable U := measurable_pi_iff.2 fun _ => hWm _
  have hVm : Measurable V := measurable_pi_iff.2 fun i =>
    (s56_continuous_coord m i.2).measurable.comp ((G.evolution H).meas (s i.1))
  have hlaw : P.map U = G.P.map V := by
    apply s56_seq_law_eq P G.P U V hUm.aemeasurable hVm.aemeasurable
    intro n f hf
    let τ : Fin n → ℝ := fun i => s (f i).1
    let φ : Fin n → Euc p.d → ℝ := fun i => oscTestFun m (f i).2
    let F : Fin n → GaussianFeatureHilbert := fun i => J (fp81s21_combinedFeature p R hK (τ i) (φ i))
    have hmat : (Matrix.of fun i j => inner ℝ (F i) (F j)) =
        Matrix.of (fun i j => HRS.Whole.linearGaussianCov (r26t3_coeff R) p.β⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
          (τ i) (τ j) (φ i) (φ j)) := by
      ext i j
      have h := fp81s21_combinedFeature_gram p hδ hδhalf R hK
        (s (f i).1).property.1 (s (f j).1).property.1
        (s56_isOscTest m (f i).2) (s56_isOscTest m (f j).2)
      change inner ℝ (J (fp81s21_combinedFeature p R hK (τ i) (φ i)))
        (J (fp81s21_combinedFeature p R hK (τ j) (φ j))) = _
      rw [J.inner_map_map]
      exact h
    have hsource := fp81s21_source_finite_law P W hWm hcomb hcov n F
    have hG := (G.evolution H).gaussian n τ φ (fun i => (s (f i).1).property)
      (fun i => s56_isOscTest m (f i).2)
    rw [hmat] at hsource
    have hvec : (fun ω => (WithLp.toLp 2 (fun i => V ω (f i)) : EuclideanSpace ℝ (Fin n))) =
        (fun ω => (WithLp.toLp 2 (fun i => OscDual.eval (G.Z (τ i) ω) (φ i)) : EuclideanSpace ℝ (Fin n))) := by
      funext ω
      ext i
      exact (OscDual.eval_oscTestFun (G.Z (τ i) ω) (f i).2).symm
    rw [← hvec] at hG
    simpa only [U, F, τ, φ, HRS.law] using hsource.trans hG.symm
  have hemb := s56_measurableEmbedding_pathCoords (d := p.d) m H s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  have hV : ∀ᵐ ω ∂G.P, V ω = Ψ (processWindow m H 0 G.Z ω) := by
    filter_upwards [(G.evolution H).cont] with ω hω
    simpa only [V, Ψ, processWindow] using
      (s56_pathCoords_windowPathOf (d := p.d) s G.Z hω).symm
  have hrangeV : ∀ᵐ ω ∂G.P, V ω ∈ Set.range Ψ := by
    filter_upwards [hV] with ω hω
    exact ⟨processWindow m H 0 G.Z ω, hω.symm⟩
  have hrangeU : ∀ᵐ ω ∂P, U ω ∈ Set.range Ψ :=
    s56_ae_mem_of_map_eq P G.P U V hUm.aemeasurable hVm.aemeasurable hlaw
      hemb.measurableSet_range hrangeV
  let X := g ∘ U
  have hXcoords : ∀ᵐ ω ∂P, ∀ i, OscDual.coord (OscPath.at' (X ω) (s i.1)) i.2 = U ω i := by
    filter_upwards [hrangeU] with ω hω
    obtain ⟨w, hw⟩ := hω
    have : g (Ψ w) = w := congrFun hg w
    intro i
    change OscDual.coord (OscPath.at' (g (U ω)) (s i.1)) i.2 = U ω i
    rw [← hw, this]
    rfl
  have hY : (g ∘ V) =ᵐ[G.P] processWindow m H 0 G.Z := by
    filter_upwards [hV] with ω hω
    change g (V ω) = processWindow m H 0 G.Z ω
    rw [hω]
    exact congrFun hg _
  have hmap : P.map X = G.P.map (processWindow m H 0 G.Z) := by
    rw [show X = g ∘ U from rfl, ← Measure.map_map hgm hUm, hlaw,
      Measure.map_map hgm hVm]
    exact Measure.map_congr hY
  exact ⟨X, hgm.comp hUm, hXcoords, hmap⟩

#print axioms fp81s21_combined_source_path
end HRS.Fp81.S21
end
