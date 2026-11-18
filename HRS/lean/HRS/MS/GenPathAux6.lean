import HRS.MS.GenPathAux5
import HRS.MS.SuppU9
import HRS.Uniform.Q45Smooth
import HRS.Main.GFB4Aux13
import HRS.Main.Headline

/-!
# S5.6 packet P9a, part 1: the reconstruction map `𝒯 : C([0,T];𝒦) → C([0,T];ℓ²)` as a bounded linear map

`s56_evalA_add`, `s56_evalA_smul`: `x ↦ A_t(x) = x.evalA t` is linear.  `s56_reconCLM`: the bounded linear map
`𝒯 w (t) = A_T(t) - B_T + B_t` of norm at most `3 + √T` (`W:r2:reconstruct`, S L3374), so that
`smoothDist_map_clm_le` and the maximal estimates of S5.2/S5.5 apply to `𝒯`-images of `𝒦`-valued path laws.
Helper names carry the prefix `s56_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.U9

variable {d : ℕ} {m T : ℝ}

lemma s56_A'_add (x y : KSpace d m T) :
    (((x + y).A' : L2Path d m T) : ℝ → OscDual d m) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
      (x.A' : ℝ → OscDual d m) + (y.A' : ℝ → OscDual d m) :=
  Lp.coeFn_add x.A' y.A'

lemma s56_A'_smul (c : ℝ) (x : KSpace d m T) :
    (((c • x).A' : L2Path d m T) : ℝ → OscDual d m) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
      c • (x.A' : ℝ → OscDual d m) :=
  Lp.coeFn_smul c x.A'

lemma s56_evalA_add (x y : KSpace d m T) (t : ℝ) :
    (x + y).evalA t = x.evalA t + y.evalA t := by
  unfold KSpace.evalA
  have hsub : volume.restrict (Set.Icc (0 : ℝ) (min t T)) ≤ volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right (min_le_right _ _)) le_rfl
  have h : ((x + y).A' : ℝ → OscDual d m) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (min t T))]
      (x.A' : ℝ → OscDual d m) + (y.A' : ℝ → OscDual d m) :=
    (s56_A'_add x y).filter_mono (Measure.absolutelyContinuous_of_le hsub).ae_le
  have hx : Integrable (x.A' : ℝ → OscDual d m) (volume.restrict (Set.Icc (0 : ℝ) (min t T))) :=
    (u9_integrableOn x.A').mono_set (Set.Icc_subset_Icc_right (min_le_right _ _))
  have hy : Integrable (y.A' : ℝ → OscDual d m) (volume.restrict (Set.Icc (0 : ℝ) (min t T))) :=
    (u9_integrableOn y.A').mono_set (Set.Icc_subset_Icc_right (min_le_right _ _))
  rw [integral_congr_ae h, Pi.add_def, integral_add hx hy]
  show x.A₀ + y.A₀ + _ = _
  abel

lemma s56_evalA_smul (c : ℝ) (x : KSpace d m T) (t : ℝ) : (c • x).evalA t = c • x.evalA t := by
  unfold KSpace.evalA
  have hsub : volume.restrict (Set.Icc (0 : ℝ) (min t T)) ≤ volume.restrict (Set.Icc (0 : ℝ) T) :=
    Measure.restrict_mono (Set.Icc_subset_Icc_right (min_le_right _ _)) le_rfl
  have h : ((c • x).A' : ℝ → OscDual d m) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (min t T))]
      c • (x.A' : ℝ → OscDual d m) :=
    (s56_A'_smul c x).filter_mono (Measure.absolutelyContinuous_of_le hsub).ae_le
  rw [integral_congr_ae h, Pi.smul_def, integral_smul]
  show c • x.A₀ + _ = _
  rw [smul_add]

lemma s56_B_add (x y : KSpace d m T) : (x + y).B = x.B + y.B := rfl

lemma s56_B_smul (c : ℝ) (x : KSpace d m T) : (c • x).B = c • x.B := rfl

/-- The reconstruction `(𝒯 w)(t) = A_T(t) - B_T + B_t` as a continuous map. -/
def s56_reconFun (hT : 0 ≤ T) (w : PathSp T (KSpace d m T)) : C(Set.Icc (0 : ℝ) T, OscDual d m) :=
  ⟨fun t => (pcm w ⟨T, hT, le_rfl⟩).evalA t - (pcm w ⟨T, hT, le_rfl⟩).B + (pcm w t).B, by
    have h1 : Continuous fun t : Set.Icc (0 : ℝ) T => (pcm w ⟨T, hT, le_rfl⟩).evalA t :=
      continuousOn_iff_continuous_restrict.1 (u9_continuousOn_evalA hT _)
    exact (h1.sub continuous_const).add (u9_continuous_B.comp (pcm w).continuous)⟩

lemma s56_reconFun_apply (hT : 0 ≤ T) (w : PathSp T (KSpace d m T)) (t : Set.Icc (0 : ℝ) T) :
    s56_reconFun hT w t = (pcm w ⟨T, hT, le_rfl⟩).evalA t - (pcm w ⟨T, hT, le_rfl⟩).B + (pcm w t).B :=
  rfl

def s56_reconLin (hT : 0 ≤ T) : PathSp T (KSpace d m T) →ₗ[ℝ] OscPath d m T where
  toFun w := s56_reconFun hT w
  map_add' w w' := by
    refine ContinuousMap.ext fun t => ?_
    show s56_reconFun hT (w + w') t = s56_reconFun hT w t + s56_reconFun hT w' t
    rw [s56_reconFun_apply, s56_reconFun_apply, s56_reconFun_apply, pcm_add, pcm_add,
      s56_evalA_add, s56_B_add, s56_B_add]
    abel
  map_smul' c w := by
    refine ContinuousMap.ext fun t => ?_
    show s56_reconFun hT (c • w) t = c • s56_reconFun hT w t
    rw [s56_reconFun_apply, s56_reconFun_apply, pcm_smul, pcm_smul, s56_evalA_smul,
      s56_B_smul, s56_B_smul]
    simp only [smul_sub, smul_add, RingHom.id_apply]

/-- `𝒯` as a bounded linear map, `‖𝒯‖ ≤ 3 + √T`. -/
def s56_reconCLM (hT : 0 ≤ T) : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T :=
  (s56_reconLin hT).mkContinuous (3 + Real.sqrt T) fun w => by
    have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
    show ‖s56_reconFun hT w t‖ ≤ (3 + Real.sqrt T) * ‖w‖
    rw [s56_reconFun_apply]
    refine (u9_recon_norm_le hT _ _ _).trans ?_
    have h1 := norm_pcm_apply_le w ⟨T, hT, le_rfl⟩
    have h2 := norm_pcm_apply_le w t
    have h3 : (2 + Real.sqrt T) * ‖pcm w ⟨T, hT, le_rfl⟩‖ ≤ (2 + Real.sqrt T) * ‖w‖ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith

lemma s56_reconCLM_apply (hT : 0 ≤ T) (w : PathSp T (KSpace d m T)) (t : Set.Icc (0 : ℝ) T) :
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from s56_reconCLM hT w) t =
      (pcm w ⟨T, hT, le_rfl⟩).evalA t - (pcm w ⟨T, hT, le_rfl⟩).B + (pcm w t).B := rfl

lemma s56_reconCLM_norm_le (hT : 0 ≤ T) : ‖(s56_reconCLM hT : PathSp T (KSpace d m T) →L[ℝ] OscPath d m T)‖ ≤
    3 + Real.sqrt T :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end HRS.MS.GenPath
