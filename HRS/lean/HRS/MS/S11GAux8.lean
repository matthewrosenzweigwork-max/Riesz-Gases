import HRS.MS.S111BDAux4

/-!
# S11G: Gaussian law of the degenerate window `T = 0`, and the empty window `T < 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS HRS.Whole

/-- Restriction of `C([0,1]; B)` to the point window `[0,0]`. -/
def s11g_restr (d : ℕ) (m : ℝ) : OscPath d m 1 →L[ℝ] OscPath d m 0 :=
  LinearMap.mkContinuous
    { toFun := fun w =>
        (show OscPath d m 0 from
          ((show C(Set.Icc (0 : ℝ) 1, OscDual d m) from w).comp
            (⟨fun τ : Set.Icc (0 : ℝ) 0 => (⟨τ.1, τ.2.1, τ.2.2.trans zero_le_one⟩ : Set.Icc (0 : ℝ) 1),
              by fun_prop⟩ : C(Set.Icc (0 : ℝ) 0, Set.Icc (0 : ℝ) 1))))
      map_add' := fun w w' => rfl
      map_smul' := fun c w => rfl } 1 (fun w => by
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun τ => ?_
    exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) 1, OscDual d m) from w) _)

theorem s11g_restr_apply (d : ℕ) (m : ℝ) (w : OscPath d m 1) (τ : Set.Icc (0 : ℝ) 0) :
    OscPath.at' (s11g_restr d m w) τ = OscPath.at' w ⟨τ.1, τ.2.1, τ.2.2.trans zero_le_one⟩ := rfl

theorem s11g_window_gaussian_zero (d : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (C : WholeCoeff d) (m q u : ℝ)
    (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ)
    (Z : ℝ → Ω → OscDual d m)
    (hZ : IsLinearGaussianEvolutionW P C m q (u + 1) C₀ Z) (hu : 0 ≤ u) :
    AEMeasurable (processWindow m 0 u Z) P ∧
      HRS.IsCenteredGaussian (P.map (processWindow m 0 u Z)) := by
  obtain ⟨hm1, hg1, -⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian d P C m q 1 u (u + 1) C₀ Z hZ
    one_pos hu le_rfl
  obtain ⟨hm0, hae0⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas d P C m q 0 u (u + 1) C₀ Z hZ le_rfl hu
    (by linarith)
  obtain ⟨-, hae1⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas d P C m q 1 u (u + 1) C₀ Z hZ zero_le_one hu
    le_rfl
  refine ⟨hm0, ?_⟩
  have hcongr : processWindow m 0 u Z =ᵐ[P] fun ζ => s11g_restr d m (processWindow m 1 u Z ζ) := by
    filter_upwards [hae0, hae1] with ζ h0 h1
    refine ContinuousMap.ext fun τ => ?_
    have := h0 τ
    have h1' := h1 ⟨τ.1, τ.2.1, τ.2.2.trans zero_le_one⟩
    exact this.trans h1'.symm
  have hmap : P.map (processWindow m 0 u Z) =
      (P.map (processWindow m 1 u Z)).map (s11g_restr d m) := by
    rw [AEMeasurable.map_map_of_aemeasurable (s11g_restr d m).continuous.measurable.aemeasurable hm1]
    exact Measure.map_congr hcongr
  obtain ⟨hG, hc⟩ := hg1
  have := hG
  rw [hmap]
  refine ⟨inferInstance, fun Λ => ?_⟩
  rw [integral_map (s11g_restr d m).continuous.measurable.aemeasurable
    Λ.continuous.measurable.aestronglyMeasurable]
  exact hc (Λ.comp (s11g_restr d m))

end HRS.MS.S11G
