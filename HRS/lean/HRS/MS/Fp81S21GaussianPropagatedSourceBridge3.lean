import HRS.MS.Fp81S21GaussianPropagatedSourceBridge2

/-! The literal propagated-source bridge on the supplied physical package. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Covariance makes the retained source evaluation an isometry in L²;
no pointwise source linearity is required. -/
private theorem fp81s21_bridge_source_L2_isometry
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (D : fp81s21_gaussian_source_retained_data p R
      (fp81s21_initialMeasure_isProbability p R))
    (hW : ∀ h : Fp81S21GaussFeatureHilbert p R, MemLp (D.W (D.J h)) 2 D.G0.P) :
    Isometry (fun h => (hW h).toLp (D.W (D.J h))) := by
  let Y : Fp81S21GaussFeatureHilbert p R → Lp ℝ 2 D.G0.P :=
    fun h => (hW h).toLp (D.W (D.J h))
  have hi (h k : Fp81S21GaussFeatureHilbert p R) :
      inner ℝ (Y h) (Y k) = inner ℝ h k := by
    rw [L2.inner_def]
    calc
      (∫ ω, inner ℝ (Y h ω) (Y k ω) ∂D.G0.P) =
          ∫ ω, D.W (D.J h) ω * D.W (D.J k) ω ∂D.G0.P := by
        apply integral_congr_ae
        filter_upwards [(hW h).coeFn_toLp, (hW k).coeFn_toLp] with ω hh hk
        change Y h ω = _ at hh
        change Y k ω = _ at hk
        rw [hh, hk, Real.inner_apply]
      _ = inner ℝ (D.J h) (D.J k) := D.allFeatureCovariance _ _
      _ = inner ℝ h k := D.J.inner_map_map h k
  apply isometry_iff_dist_eq.mpr
  intro h k
  change dist (Y h) (Y k) = dist h k
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, hi]

/-- The chart action on a propagated oscillator coordinate equals the evaluation
of its literal initial-plus-noise feature, on the same retained Gaussian source.
The radius telescope is the definitional expansion of `fp81s21_Rad`. -/
theorem fp81s21_gaussian_propagated_source_bridge (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      letI := fp81s21_initialMeasure_isProbability p R
      ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, 0 ≤ a →
      ∀ r ∈ Icc (0 : ℝ) (a + p.T), ∀ t ∈ Icc r (a + p.T),
      ∀ α : MultiIndex p.d,
      let f := propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      (fun ω => fp81s21_chartAction Q.E
        (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection r ω) f)
        =ᵐ[Q.src.G0.P]
      fun ω => Q.src.W (Q.src.J (fp81s21_combinedFeature p R Q.src.hK r f)) ω := by
  obtain ⟨δW, hW, hWh, hthermal⟩ := fp81s21_gaussian_propagated_thermal_approximation p
  obtain ⟨δF, hF, hFh, hfeature⟩ := fp81s21_gaussian_propagated_feature_convergence p
  refine ⟨min δW δF, lt_min hW hF, (min_le_left _ _).trans hWh, ?_⟩
  intro δ hδ hδle R
  letI := fp81s21_initialMeasure_isProbability p R
  intro Q a ha r hr t ht α
  let f := propagatorW (r26t3_coeff R) r t
    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
  let ψ : ℕ → compactSmoothSubmodule p.d := chartSection Q.E (Q.E.encode f)
  obtain ⟨hfW, hf₀, hag, _⟩ :=
    hthermal δ hδ (hδle.trans (min_le_left _ _)) R Q a ha r hr t ht α
  obtain ⟨hf, hψ, hconv⟩ := fp81s21_chartSection_thermal_convergence p R Q.E f hfW
  have hfc := hfeature δ hδ (hδle.trans (min_le_right _ _)) R Q a ha r hr t ht α
  let F : (Euc p.d → ℝ) → Fp81S21GaussFeatureHilbert p R :=
    fp81s21_combinedFeature p R Q.src.hK r
  have hmem : ∀ h : Fp81S21GaussFeatureHilbert p R,
      MemLp (Q.src.W (Q.src.J h)) 2 Q.src.G0.P :=
    fun h => Q.src.rawBundle.2.2.2.2.1 (Q.src.J h)
  let Y : Fp81S21GaussFeatureHilbert p R → Lp ℝ 2 Q.src.G0.P :=
    fun h => (hmem h).toLp (Q.src.W (Q.src.J h))
  have hY : Isometry Y := fp81s21_bridge_source_L2_isometry p R Q.src hmem
  have hsource : Tendsto (fun n => Y (F (ψ n))) atTop (𝓝 (Y (F f))) :=
    (hY.continuous.tendsto (F f)).comp hfc
  have heq (n : ℕ) :
      Q.S.T Q.src.G0 r ((hψ n).toLp (ψ n : Euc p.d → ℝ)) = Y (F (ψ n)) := by
    have hosc := r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) (ψ n).property
    have hae := (Q.T_oscillator r hr.1 (ψ n) hosc (hψ n)).trans
      (Q.src.sourceEvaluation r hr.1 (ψ n) hosc)
    apply Lp.ext
    exact hae.trans (hmem (F (ψ n))).coeFn_toLp.symm
  have hoperator : Tendsto
      (fun n => Q.S.T Q.src.G0 r ((hψ n).toLp (ψ n : Euc p.d → ℝ)))
      atTop (𝓝 (Q.S.T Q.src.G0 r (hf.toLp f))) :=
    ((Q.S.T Q.src.G0 r).continuous.tendsto (hf.toLp f)).comp hconv
  have hlimit : Q.S.T Q.src.G0 r (hf.toLp f) = Y (F f) := by
    apply tendsto_nhds_unique hoperator
    simpa only [heq] using hsource
  have hop : (Q.S.T Q.src.G0 r (hf.toLp f) : Q.src.G0.Ω → ℝ) =ᵐ[Q.src.G0.P]
      Q.src.W (Q.src.J (F f)) := by
    rw [hlimit]
    exact (hmem (F f)).coeFn_toLp
  exact hag.trans hop

#print axioms fp81s21_bridge_source_L2_isometry
#print axioms fp81s21_gaussian_propagated_source_bridge
end HRS.Fp81.S21
end
