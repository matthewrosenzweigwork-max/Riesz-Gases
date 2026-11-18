import HRS.MS.R26T6CI11CubeMemLp
import HRS.MS.R26T6CI11MeasPath

/-!
# I11: quantitative L³ estimate for a measurable continuous oscillator primitive.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ} {m : ℝ}

theorem r26t6c_measurable_primitive_L3
    (T : ℝ) (hT : 0 < T)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (I : Omega → OscDual d m) (hI : MemLp I 3 P)
    (G : ℝ × Omega → OscDual d m)
    (hG : MemLp G 3 ((volume.restrict (Set.Icc 0 T)).prod P))
    (A : ℝ) (hA : 0 ≤ A)
    (hIb : eLpNorm I 3 P ≤ ENNReal.ofReal A)
    (hsec : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      MemLp (fun w => G (t,w)) 3 P ∧
      eLpNorm (fun w => G (t,w)) 3 P ≤ ENNReal.ofReal A) :
    ∃ L : Omega → OscPath d m T,
      MemLp L 3 P ∧
      (∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T,
        OscPath.at' (L w) t =
          I w + ∫ v in Set.Icc 0 (t : ℝ), G (v,w)) ∧
      (∫ w, ‖L w‖ ^ 3 ∂P) ≤ 4 * (1 + T ^ 3) * A ^ 3 := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T)
  obtain ⟨L, hLm, hLae⟩ :=
    r26t6c_measurable_oscillator_primitive m T hT P I hI G hG
  have hGsec : ∀ᵐ w ∂P, MemLp (fun v => G (v,w)) 3 dt :=
    r26t6c_samplewise_memLp_three dt P G hG
  have hp : ∀ᵐ w ∂P,
      ‖L w‖ ^ 3 ≤ 4 * ‖I w‖ ^ 3 +
        4 * T ^ 2 * ∫ v in Set.Icc (0 : ℝ) T, ‖G (v,w)‖ ^ 3 := by
    filter_upwards [hLae, hGsec] with w hw hs
    exact r26t6c_primitive_path_cube_le T hT (I w)
      (fun v => G (v,w)) hs (L w) hw
  have hIi : Integrable (fun w => ‖I w‖ ^ 3) P :=
    hI.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  have hGi : Integrable (fun z => ‖G z‖ ^ 3) (dt.prod P) :=
    hG.integrable_norm_pow (by norm_num : (3 : ℕ) ≠ 0)
  have hGinner : Integrable (fun w => ∫ v, ‖G (v,w)‖ ^ 3 ∂dt) P :=
    hGi.integral_prod_right
  let Env : Omega → ℝ := fun w =>
    4 * ‖I w‖ ^ 3 + 4 * T ^ 2 * ∫ v, ‖G (v,w)‖ ^ 3 ∂dt
  have hEnv : Integrable Env P := (hIi.const_mul 4).add
    (hGinner.const_mul (4 * T ^ 2))
  have hEnv0 : ∀ w, 0 ≤ Env w := by
    intro w
    dsimp [Env]
    have hi : 0 ≤ ∫ v, ‖G (v,w)‖ ^ 3 ∂dt :=
      integral_nonneg (fun v => pow_nonneg (norm_nonneg _) 3)
    positivity
  have hLi : Integrable (fun w => ‖L w‖ ^ 3) P := by
    have hm : AEStronglyMeasurable (fun w => ‖L w‖ ^ 3) P :=
      (hLm.aestronglyMeasurable.norm.aemeasurable.pow_const 3).aestronglyMeasurable
    refine Integrable.mono' hEnv hm ?_
    filter_upwards [hp] with w hw
    simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg (L w)) 3),
      Real.norm_of_nonneg (hEnv0 w), Env] using hw
  have hLI : ∫ w, ‖L w‖ ^ 3 ∂P ≤
      4 * ∫ w, ‖I w‖ ^ 3 ∂P +
        4 * T ^ 2 * ∫ z, ‖G z‖ ^ 3 ∂(dt.prod P) := by
    calc
      _ ≤ ∫ w, Env w ∂P := integral_mono_ae hLi hEnv hp
      _ = 4 * ∫ w, ‖I w‖ ^ 3 ∂P +
          4 * T ^ 2 * ∫ w, (∫ v, ‖G (v,w)‖ ^ 3 ∂dt) ∂P := by
        dsimp [Env]
        rw [integral_add (hIi.const_mul 4)
            (hGinner.const_mul (4 * T ^ 2)),
          integral_const_mul, integral_const_mul]
      _ = _ := by
        rw [integral_prod_symm _ hGi]
  have hIbound : ∫ w, ‖I w‖ ^ 3 ∂P ≤ A ^ 3 :=
    r26t6c_vector_cube_le P I hI A hA hIb
  have hGbound : ∫ z, ‖G z‖ ^ 3 ∂(dt.prod P) ≤ T * A ^ 3 := by
    have hx := r26t6c_spacetime_cube_le dt P G hG A hA hsec
    have hMass : (dt Set.univ).toReal = T := by
      simp [dt, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal hT.le]
    rwa [hMass] at hx
  have hbound : ∫ w, ‖L w‖ ^ 3 ∂P ≤
      4 * (1 + T ^ 3) * A ^ 3 := by
    calc
      _ ≤ 4 * ∫ w, ‖I w‖ ^ 3 ∂P +
          4 * T ^ 2 * ∫ z, ‖G z‖ ^ 3 ∂(dt.prod P) := hLI
      _ ≤ 4 * A ^ 3 + 4 * T ^ 2 * (T * A ^ 3) := by
        have ht : 0 ≤ 4 * T ^ 2 := by positivity
        gcongr
      _ = _ := by ring
  exact ⟨L, r26t6c_memLp_three_of_integrable_norm_cube P L
      hLm.aestronglyMeasurable hLi, hLae, hbound⟩

end HRS.MS.R26T6C
