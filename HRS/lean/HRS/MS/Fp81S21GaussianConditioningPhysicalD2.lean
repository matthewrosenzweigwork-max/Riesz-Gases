import HRS.MS.Fp81S21GaussianConditioningPhysicalD
import HRS.MS.Fp81S21GaussianPredictionPast

/-! Packet 36D: retained cutoff conditioning for the prediction in the supplied
GRS record. Equality of two physical versions is established at each cutoff;
no uncountable intersection and no replacement of the retained future is used. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.ProClosureS111 HRS.MS.GenPath

private theorem fp81s21_D36_path_ae_eq
    {p : Parameters} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y Y' : Ω → Window p)
    (h : ∀ τ : Icc (0 : ℝ) p.T,
      ∀ᵐ ω ∂P, OscPath.at' (Y ω) τ = OscPath.at' (Y' ω) τ) : Y =ᵐ[P] Y' := by
  letI : Nonempty (Icc (0 : ℝ) p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) p.T := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hc : ∀ i : ℕ × MultiIndex p.d, ∀ᵐ ω ∂P,
      OscDual.coord (OscPath.at' (Y ω) (s i.1)) i.2 =
        OscDual.coord (OscPath.at' (Y' ω) (s i.1)) i.2 := by
    intro i
    filter_upwards [h (s i.1)] with ω hω
    rw [hω]
  filter_upwards [ae_all_iff.2 hc] with ω hω
  exact s56_pathCoords_injective (wholeSpaceIndex p.d : ℝ) p.T s hs (funext hω)

/-- Radius-first per-cell conditioning for every supplied physical GRS record.
The right endpoint is a real number; its interval proof is used only to select
an adapted representative of this same prediction. -/
theorem fp81s21_gaussian_conditioning_physical_D_cell (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ future, fp81s21_moving_heat_full_clause p R future →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∀ C : fp81s21_GRS Q future a ha Φ, ∀ u v : ℝ,
        0 ≤ u → u ≤ v → v ≤ a + p.T →
        fp81s21_D36Cell Q future a ha Φ
          (fun ω => fp81s21_remote_G_extend Q.src.G0 a ha C.Y ω v) u v) := by
  obtain ⟨δp, hp, hhalf, hpred⟩ := fp81s21_gaussian_prediction_eq_retained_past p
  obtain ⟨δd, hd, _, hdec⟩ := fp81s21_gaussian_cutoff_source_decomposition p
  refine ⟨min δp δd, lt_min hp hd, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q future hf a ha Φ hΦ C u v hu huv hv
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  letI := fp81s21_initialMeasure_isProbability p R
  letI := hf.1 (a + p.T) v
  let r : Icc (0 : ℝ) (a + p.T) := ⟨v, hu.trans huv, hv⟩
  obtain ⟨Y, _, _, hphys, hidentify⟩ :=
    hpred δ hδ (hδle.trans (min_le_left _ _)) R Q a ha
  obtain ⟨D, _⟩ := hdec δ hδ (hδle.trans (min_le_right _ _)) R Q a ha
    v r.property (future (a + p.T) v) (hf.2.1 (a + p.T)
      (add_pos_of_nonneg_of_pos ha p.hT) v r.property)
  have hCY : (fun ω => C.Y ω r) =ᵐ[Q.src.G0.P] fun ω => Y ω r := by
    apply fp81s21_D36_path_ae_eq
    intro τ
    filter_upwards [C.physical r τ, hphys r τ] with ω hc hy
    exact hc.trans hy.symm
  obtain ⟨Yr, hYr, hYrpast, hCYr⟩ := C.adapted r
  let res := physicalWindowRestriction (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    ha (le_refl (a + p.T))
  let X := fun ω => res (D.Xfuture ω)
  have hX : Measurable X := res.measurable.comp D.measurable_future
  have hind : IndepFun (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v)
      X Q.src.G0.P :=
    D.independent_past.comp measurable_id res.measurable
  have hlaw : Q.src.G0.P.map X = windowFuture future a ha v := by
    change Q.src.G0.P.map (res ∘ D.Xfuture) = (future (a + p.T) v).map res
    rw [← Measure.map_map res.measurable D.measurable_future, D.future_law]
  have hZ : r26t3_Zpath Q.src.G0 a =ᵐ[Q.src.G0.P] fun ω => Yr ω + X ω := by
    filter_upwards [(hidentify r _ D).2, hCY, hCYr] with ω hz hc hyr
    change r26t3_Zpath Q.src.G0 a ω = Yr ω + res (D.Xfuture ω)
    rw [hz, ← hc, hyr]
  have hcell := fp81s21_gaussian_conditioning_drift_cell_of_decomposition Q future hf.1
    a ha Φ hΦ u v hu huv hv Yr X hYr hYrpast hX hind hlaw hZ
  have hsame : (fun ω => fderiv ℝ (initialHeat future a ha Φ v)
      (fp81s21_remote_G_extend Q.src.G0 a ha C.Y ω v)
      (fp81s21_incrementD36 Q a ha u v ω)) =ᵐ[Q.src.G0.P]
      fun ω => fderiv ℝ (initialHeat future a ha Φ v) (Yr ω)
        (fp81s21_incrementD36 Q a ha u v ω) := by
    filter_upwards [hCYr] with ω hω
    have he := fp81s21_remote_G_extend_at Q.src.G0 a ha C.Y ω r
    change fp81s21_remote_G_extend Q.src.G0 a ha C.Y ω v = C.Y ω r at he
    rw [he, hω]
  exact ⟨hcell.1.congr hsame.symm, hcell.2.1,
    (integral_congr_ae hsame).trans hcell.2.2⟩

#print axioms fp81s21_D36_path_ae_eq
#print axioms fp81s21_gaussian_conditioning_physical_D_cell
end HRS.Fp81.S21
end
