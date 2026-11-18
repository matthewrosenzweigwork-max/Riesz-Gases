import HRS.MS.Fp81S21FutureIndep18
import HRS.MS.Fp81S21FutureIndep26

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.GenPath HRS.MS.R2Interp

/-- Cutoff-zero noise splits into a measurable past-source path and an
independent future path on the same retained Gaussian source. -/
theorem fp81s21_noise_past_future_paths
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
    (γ0 γr : Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    [IsProbabilityMeasure γ0] [IsProbabilityMeasure γr]
    (hγ0 : IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H 0 γ0)
    (hγr : IsR2FutureGaussian (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r γr) :
    ∃ X0 Xpast Xfuture : Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H,
      Measurable X0 ∧ Measurable Xpast ∧ Measurable Xfuture ∧
      P.map X0 = γ0 ∧ P.map Xfuture = γr ∧
      (∀ᵐ ω ∂P, X0 ω = Xpast ω + Xfuture ω) ∧
      Measurable[MeasurableSpace.comap
        (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
          W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance] Xpast ∧
      IndepFun Xpast Xfuture P := by
  obtain ⟨Xr, hXrm, hXrlaw, ⟨s, hs, hXrcoord⟩, hind⟩ :=
    fp81s21_future_path_independent_of_past_source p R hδ hδhalf hH hr P J W hWm hW2 hcomb hcov γr hγr
  obtain ⟨X0, hX0m, hX0law, hX0coord⟩ :=
    fp81s21_future_source_path p R hδ hδhalf hH ⟨le_rfl, hH.le⟩ P J W hWm hcomb hcov γ0 hγ0 s hs
  let past := fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
    W (J (WithLp.toLp 2 (i.1, i.2.1))) ω
  let b : ℕ × MultiIndex p.d → Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r := fun i =>
    (0, ⟨movingNoiseFeature R 0 (s i.1) (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2) -
      movingNoiseFeature R r (s i.1) (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2),
      fp81s21_past_feature_supported p R hδ hδhalf hH hr (s i.1).property
        (s56_isOscTest (wholeSpaceIndex p.d : ℝ) i.2)⟩)
  have hcoords : ∀ᵐ ω ∂P, ∀ i : ℕ × MultiIndex p.d,
      OscDual.coord (OscPath.at' (X0 ω - Xr ω) (s i.1)) i.2 = past ω (b i) := by
    have hd : ∀ i : ℕ × MultiIndex p.d, ∀ᵐ ω ∂P,
        W (J (WithLp.toLp 2 (0, movingNoiseFeature R 0 (s i.1)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2)))) ω =
          past ω (b i) + W (J (fp81s21_futureNoiseSourceFeature p R r (s i.1)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2))) ω := by
      intro i
      simpa [past, b, fp81s21_pastNoiseSourceFeature] using
        fp81s21_noise_source_decomposition p R P J W hWm hW2 hcomb r (s i.1)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2)
    filter_upwards [hX0coord, hXrcoord, ae_all_iff.2 hd] with ω h0 hr' hd' i
    have hs0 := h0 i
    have hsr := hr' i
    have hd0 := hd' i
    change s102_ell (s i.1) i.2 (X0 ω - Xr ω) = past ω (b i)
    rw [map_sub, s102_ell_apply, s102_ell_apply, hs0, hsr] 
    change W (J (WithLp.toLp 2 (0, movingNoiseFeature R 0 (s i.1)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2)))) ω -
        W (J (fp81s21_futureNoiseSourceFeature p R r (s i.1)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) i.2))) ω = past ω (b i)
    linarith
  let Ψ := s56PathCoords (d := p.d) (wholeSpaceIndex p.d : ℝ) H s
  have hemb := s56_measurableEmbedding_pathCoords (d := p.d) (wholeSpaceIndex p.d : ℝ) H s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend (g := id) measurable_id (fun _ => ⟨0⟩)
  let select : (Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r → ℝ) →
      (ℕ × MultiIndex p.d → ℝ) := fun z i => z (b i)
  have hselect : Measurable select := measurable_pi_iff.2 fun i => measurable_pi_apply (b i)
  let Xp := fun ω => g (select (past ω))
  have hpm : Measurable past := measurable_pi_iff.2 fun _ => hWm _
  have hXpm : Measurable Xp := hgm.comp (hselect.comp hpm)
  have hXpPast : Measurable[MeasurableSpace.comap past inferInstance] Xp :=
    hgm.comp (hselect.comp (comap_measurable past))
  have hXp : Xp =ᵐ[P] fun ω => X0 ω - Xr ω := by
    filter_upwards [hcoords] with ω hω
    have h : Ψ (X0 ω - Xr ω) = select (past ω) := by
      funext i
      exact hω i
    change g (select (past ω)) = X0 ω - Xr ω
    rw [← h]
    exact congrFun hg (X0 ω - Xr ω)
  have hInd : IndepFun Xp Xr P := by
    change IndepFun ((fun z => g (select z)) ∘ past) (id ∘ Xr) P
    exact hind.comp (hgm.comp hselect) measurable_id
  refine ⟨X0, Xp, Xr, hX0m, hXpm, hXrm, hX0law, hXrlaw, ?_, hXpPast, hInd⟩
  filter_upwards [hXp] with ω hω
  rw [hω]
  exact (sub_add_cancel _ _).symm

#print axioms fp81s21_noise_past_future_paths
end HRS.Fp81.S21
end
