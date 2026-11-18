import HRS.MS.Fp81S21CenteredJointComparisonRetained3
import HRS.MS.Fp81S21PredictionParticle2
import HRS.MS.Fp81S21PredictionGaussian
import HRS.MS.Fp81S21WeightTrace
import HRS.MS.Fp81S21Uniform2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_predictionPhysical_CH_meas (H : ℝ) : MeasurableSpace (CH H) := borel _
local instance fp81s21_predictionPhysical_CH_borel (H : ℝ) : BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_predictionPhysical_UH_meas (H : ℝ) : MeasurableSpace (UH H) := borel _
local instance fp81s21_predictionPhysical_UH_borel (H : ℝ) : BorelSpace (UH H) := ⟨rfl⟩
local instance fp81s21_predictionPhysical_YH_meas (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_predictionPhysical_YH_borel (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩

private theorem fp81s21_predictionPhysical_prodMap_norm
    {U V C : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (S : U →L[ℝ] C) :
    ‖S.prodMap (ContinuousLinearMap.id ℝ V)‖ ≤ max 1 ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rcases z with ⟨u, v⟩
  change max ‖S u‖ ‖v‖ ≤ max 1 ‖S‖ * max ‖u‖ ‖v‖
  apply max_le
  · have hK : 0 ≤ max 1 ‖S‖ := le_trans (by norm_num) (le_max_left 1 ‖S‖)
    calc
      ‖S u‖ ≤ ‖S‖ * ‖u‖ := S.le_opNorm u
      _ ≤ max 1 ‖S‖ * ‖u‖ :=
        mul_le_mul_of_nonneg_right (le_max_right 1 ‖S‖) (norm_nonneg u)
      _ ≤ max 1 ‖S‖ * max ‖u‖ ‖v‖ :=
        mul_le_mul_of_nonneg_left (le_max_left ‖u‖ ‖v‖) hK
  · have hz : 0 ≤ max ‖u‖ ‖v‖ := le_trans (norm_nonneg u) (le_max_left _ _)
    calc
      ‖v‖ ≤ max ‖u‖ ‖v‖ := le_max_right _ _
      _ = 1 * max ‖u‖ ‖v‖ := (one_mul _).symm
      _ ≤ max 1 ‖S‖ * max ‖u‖ ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_max_left 1 ‖S‖) hz

/-- The retained physical joint comparison transported through the recent
prediction operator, with exact centered particle and Gaussian versions. -/
theorem fp81s21_physical_recent_prediction_comparison_centered (p : Parameters) :
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (r p) (Pw p),
    ∃ εAvg : ℕ → ℝ, (∀ k, 0 ≤ εAvg k) ∧ Tendsto εAvg atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∃ MUG : ℝ, 0 ≤ MUG ∧
    ∃ canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG εAvg,
    ∃ εN εG εB : ℕ → ℝ,
      (∀ k, 0 ≤ εN k) ∧ Tendsto εN atTop (𝓝 0) ∧
      (∀ k, 0 ≤ εG k) ∧ Tendsto εG atTop (𝓝 0) ∧
      (∀ k, 0 ≤ εB k) ∧ Tendsto εB atTop (𝓝 0) ∧
    ∃ S31 : fp81s21_Physical31 p R Es E εN εG εB,
    ∃ Kpred : ℝ, 0 ≤ Kpred ∧
    ∀ L : ℝ, 0 < L →
      let H := L + p.T
      ∃ e eL : ℕ → ℝ,
        (∀ N, 0 ≤ e N) ∧ Tendsto e atTop (𝓝 0) ∧
        eL = (fun N => max 1 Kpred * (2 * e N)) ∧
        (∀ N, 0 ≤ eL N) ∧ Tendsto eL atTop (𝓝 0) ∧
      ∃ P : (a : ℝ) → 0 ≤ a → CH H →L[ℝ] YH p H,
        (∀ a ha, ‖P a ha‖ ≤ Kpred ∧ PSpec p R E L a (P a ha)) ∧
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
      ∀ G : GaussianRealization R, ∀ a : ℝ, ∀ ha : 0 ≤ a,
        let b := max (a - L) 0
        ∃ XN : A.Ω → CH H, ∃ XG : G.Ω → CH H,
        ∃ UBN : A.Ω → UH H, ∃ UBG : G.Ω → UH H,
        ∃ YN : A.Ω → YH p H, ∃ YG : G.Ω → YH p H,
          CD E A.P (fp81s21_particleEmpField R N A) b H XN ∧
          CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f) b H XG ∧
          fp81s21_TimeL2Rep A.P (fun u ω => fp81s21_particle_embedField p Es E
            (S31.qsBN N hN A u ω)) S31.MN b H UBN ∧
          fp81s21_TimeL2Rep G.P (S31.gaussian.quadratic.qe G)
            (S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2) b H UBG ∧
          (∫ ω, XG ω ∂G.P) = 0 ∧
          GA p R E G (S31.gaussian.quadratic.T G) b H XG ∧
          YN = (fun ω => P a ha (cen A.P XN ω)) ∧
          YG = (fun ω => P a ha (cen G.P XG ω)) ∧
          Measurable YN ∧ MemLp YN 2 A.P ∧ Measurable YG ∧ MemLp YG 2 G.P ∧
          NId p R A L a YN ∧ GId p R E G L a XG YG ∧
          wassersteinE 2 (law A.P (fun ω => (XN ω, UBN ω)))
            (law G.P (fun ω => (XG ω, UBG ω))) ≤ ENNReal.ofReal (e N) ∧
          wassersteinE 2 (law A.P (fun ω => (cen A.P XN ω, cen A.P UBN ω)))
            (law G.P (fun ω => (cen G.P XG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (2 * e N) ∧
          wassersteinE 2 (law A.P (fun ω => (YN ω, cen A.P UBN ω)))
            (law G.P (fun ω => (YG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (eL N) := by
  obtain ⟨Es, E, εAvg, hε, hεlim, δc, hδc, hδch, hc⟩ :=
    fp81s21_physical_joint_comparison_centered_retained p
  obtain ⟨δo, hδo, _, ho⟩ := fp81s21_uniform_orbit_amplitudes p
  obtain ⟨δw, hδw, _, hw⟩ := fp81s21_uniform_higher_marginal_weights p
  let δ0 := min δc (min δo δw)
  have hδ0 : 0 < δ0 := lt_min hδc (lt_min hδo hδw)
  refine ⟨Es, E, εAvg, hε, hεlim, δ0, hδ0, (min_le_left _ _).trans hδch, ?_⟩
  intro δ hδ hδle R
  have hδc' : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδo' : δ ≤ δo := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδw' : δ ≤ δw := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, S31, hcomp⟩ :=
    hc δ hδ hδc' R
  obtain ⟨Co, co, hco, hsum, hD⟩ := ho δ hδ hδo' R
  obtain ⟨Cw, hCw, hweight⟩ := hw δ hδ hδw' R (Pw p) (by dsimp [Pw]; positivity)
  let c := fp81s21_uniform_orbit_coefficient p Co
  let Kpred := s102_KV p.d (r p) (Pw p) c
  have hK : 0 ≤ Kpred := s102_KV_nonneg _ _ _ _
  refine ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, S31, Kpred, hK, ?_⟩
  intro L hL
  let H := L + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  obtain ⟨M2, hM2, Savg, ω, hω, hωlim, hSbound, q31, hq31, hq31lim,
    e, he, hepos, helim, hNall⟩ := hcomp H hH
  obtain ⟨P, hP⟩ := recent_operator p R E c hD L hL
  let eL : ℕ → ℝ := fun N => max 1 Kpred * (2 * e N)
  have heL : ∀ N, 0 ≤ eL N := by
    intro N
    dsimp [eL]
    exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) (mul_nonneg (by norm_num) (hepos N))
  have heLlim : Tendsto eL atTop (𝓝 0) := by
    simpa [eL] using (tendsto_const_nhds.mul (tendsto_const_nhds.mul helim))
  refine ⟨e, eL, hepos, helim, rfl, heL, heLlim, P, hP, ?_⟩
  intro N hN A G a ha
  let b := max (a - L) 0
  have hb0 : 0 ≤ b := le_max_right _ _
  have hT : 0 < b + H := by linarith
  have hDat := hD (b + H) hT
  obtain ⟨qN, hqN, hGall⟩ := hNall N hN A
  obtain ⟨XN, UN, VηN, UBN, XG, UG, VηG, UBG,
    hXN, hXN2, hUNtime, hVηNtime, hUNVηN, hUBN, hUBN2, hUBNtime,
    hUNpath, hNphysical, hXG, hXG2, hUGtime, hVηGtime, hUGVηG,
    hUBG, hUBG2, hUBGtime, hUGpath, hGphysical, hSqErr,
    hXNcm, hXNc2, hUBNcm, hUBNc2, hXGcm, hXGc2, hUBGcm, hUBGc2,
    hraw, hcenter⟩ := hGall G b hb0
  have hNcd : CD E A.P (fp81s21_particleEmpField R N A) b H XN := ⟨hXN, hXN2, hNphysical⟩
  have hGcd : CD E G.P (fun u ω f => OscDual.eval (G.Z u ω) f) b H XG := ⟨hXG, hXG2, hGphysical⟩
  have hmom : ∀ u ∈ I (b + H), Integrable (fun x : Euc p.d => jbracket x ^ (Pw p))
      (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) := by
    intro u hu
    exact (hweight N hN A u hu.1).1
  have hNid := fp81s21_particle_prediction_id p R E hN A L hL a ha c hDat
    (P a ha) (hP a ha).2 XN hNcd hmom
  obtain ⟨hmean, hGA, hGid⟩ := fp81s21_gaussian_prediction_id p R Es E εN εG εB S31
    G L hL a ha c hDat (P a ha) (hP a ha).2 XG hGcd
  let YN := fun ω => P a ha (cen A.P XN ω)
  let YG := fun ω => P a ha (cen G.P XG ω)
  have hYNm : Measurable YN := (P a ha).continuous.measurable.comp hXNcm
  have hYGm : Measurable YG := (P a ha).continuous.measurable.comp hXGcm
  have hYN2 : MemLp YN 2 A.P := hXNc2.continuousLinearMap_comp (P a ha)
  have hYG2 : MemLp YG 2 G.P := hXGc2.continuousLinearMap_comp (P a ha)
  let J := (P a ha).prodMap (ContinuousLinearMap.id ℝ (UH H))
  have hJ : ‖J‖ ≤ max 1 Kpred :=
    (fp81s21_predictionPhysical_prodMap_norm (V := UH H) (P a ha)).trans
      (max_le_max_left _ (hP a ha).1)
  have hmN : Measurable (fun ω => (cen A.P XN ω, cen A.P UBN ω)) := hXNcm.prodMk hUBNcm
  have hmG : Measurable (fun ω => (cen G.P XG ω, cen G.P UBG ω)) := hXGcm.prodMk hUBGcm
  have hmapN : law A.P (fun ω => (YN ω, cen A.P UBN ω)) =
      (law A.P (fun ω => (cen A.P XN ω, cen A.P UBN ω))).map J := by
    unfold law
    exact (AEMeasurable.map_map_of_aemeasurable J.continuous.measurable.aemeasurable hmN.aemeasurable).symm
  have hmapG : law G.P (fun ω => (YG ω, cen G.P UBG ω)) =
      (law G.P (fun ω => (cen G.P XG ω, cen G.P UBG ω))).map J := by
    unfold law
    exact (AEMeasurable.map_map_of_aemeasurable J.continuous.measurable.aemeasurable hmG.aemeasurable).symm
  have htransport : wassersteinE 2 (law A.P (fun ω => (YN ω, cen A.P UBN ω)))
      (law G.P (fun ω => (YG ω, cen G.P UBG ω))) ≤ ENNReal.ofReal (eL N) := by
    rw [hmapN, hmapG]
    calc
      _ ≤ ENNReal.ofReal ‖J‖ * wassersteinE 2
          (law A.P (fun ω => (cen A.P XN ω, cen A.P UBN ω)))
          (law G.P (fun ω => (cen G.P XG ω, cen G.P UBG ω))) :=
        HRS.Main.wassersteinE_map_clm_le J 2 (by norm_num) _ _
      _ ≤ ENNReal.ofReal ‖J‖ * ENNReal.ofReal (2 * e N) :=
        mul_le_mul_of_nonneg_left hcenter (by positivity)
      _ = ENNReal.ofReal (‖J‖ * (2 * e N)) := (ENNReal.ofReal_mul (norm_nonneg J)).symm
      _ ≤ ENNReal.ofReal (eL N) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hJ (mul_nonneg (by norm_num) (hepos N)))
  exact ⟨XN, XG, UBN, UBG, YN, YG, hNcd, hGcd, hUBNtime, hUBGtime,
    hmean, hGA, rfl, rfl, hYNm, hYN2, hYGm, hYG2, hNid, hGid, hraw, hcenter, htransport⟩

#print axioms HRS.Fp81.S21.fp81s21_physical_recent_prediction_comparison_centered
end HRS.Fp81.S21
