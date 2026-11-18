import HRS.MC.S7PIL4
import HRS.MC.S7PIJB3
import HRS.Sections.Q17Aux8

/-!
# Packet piL, part 5: `s7_PIB_lip_proj` (B2) and `s7_PIB_lip` (B4)

B2: for fixed `w`, `projHeatD .. w = gaussHeat obsCov ψ_w u 0` (`S7PIL_projHeatD_apply`), which is `(½ C_B cbNorm 5 Φ ∏‖w‖)`-Lipschitz
in `u` (`S7PIL_lip_g`), uniformly in `L`.  B4: pass to the limit `L → ∞` with `s7_PIB_proj_limit_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIL

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- **B2 (Lipschitz dependence on `u`, uniform in `L`, for the projected heat derivatives)**, proof. -/
theorem s7_PIB_lip_proj_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u)) :
    ∃ C : ℝ, ∀ (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T)), (∀ L w, Pj L w = projPoly m T hT.le L w) →
      ∀ (L : ℕ) (Φ : PathSpace d m T → ℝ), MemCb 5 Φ → ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T,
        ∀ j ≤ 3, ∀ y, ‖projHeatD γ Φ (Pj L) j u y - projHeatD γ Φ (Pj L) j v y‖ ≤ C * cbNorm 5 Φ * |u - v| := by
  obtain ⟨CB0, hCB0⟩ := HRS.MC.Sec7.S7PIB.s7_PIB_rate_bound_proof R m hm T hT
  set CB : ℝ := max CB0 0 with hCBdef
  have hCBnn : 0 ≤ CB := le_max_right _ _
  refine ⟨1 / 2 * CB, fun Pj hPj L Φ hΦ u hu v hv j hj y => ?_⟩
  obtain ⟨q, t, φ, Λ, hg⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_proj_proof (d := d) m T hT L
  have hφ := S7PIL_grid_smooth hT.le hg
  have hP : ∀ w, Pj L w = Λ (obsVec m T t φ w) := fun w => (hPj L w).trans (hg.2.2 w)
  have hlaw : ∀ u ∈ Set.Icc (0 : ℝ) T, (obsCov R.D R.ρ t φ u).PosSemidef := fun u hu =>
    (HRS.MC.Sec7.S7PIS3.s7_PIS_obs_law_proof R m T hT γ hγ t φ hg.1 hφ u hu).1
  have hCB : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ N : PathSpace d m T [×2]→L[ℝ] ℝ,
      |∑ i, ∑ j, obsRate R.D R.ρ t φ u i j *
        N ![Λ (EuclideanSpace.single i 1), Λ (EuclideanSpace.single j 1)]| ≤ CB * ‖N‖ :=
    fun u hu N => (hCB0 L q t φ Λ hg u hu N).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hcb : 0 ≤ cbNorm 5 Φ := S7PIL_cbNorm_nonneg hΦ y
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun w => ?_
  rw [ContinuousMultilinearMap.sub_apply,
    S7PIL_projHeatD_apply R m T hT γ hγ hg (Pj L) hP hΦ hj hu y w,
    S7PIL_projHeatD_apply R m T hT γ hγ hg (Pj L) hP hΦ hj hv y w, Real.norm_eq_abs]
  have key := S7PIL_lip_g t T (1 / 2 * (CB * (cbNorm 5 Φ * ∏ k, ‖w k‖))) hg.1
    (fun s => gaussHeat (obsCov R.D R.ρ t φ) (S7PIL_psi (iteratedFDeriv ℝ j Φ) (Pj L y) Λ w) s 0)
    (fun a b ha hab hb hno => S7PIL_piece R m T hT φ hg.1 hφ hlaw CB hCBnn hCB hΦ hj (Pj L y) w ha hab hb hno)
    hu hv
  refine key.trans (le_of_eq ?_)
  ring

/-- **B4 (Lipschitz time regularity of `D^j u_Φ`, `j ≤ 3`)**, proof. -/
theorem s7_PIB_lip_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) :
    ∃ C : ℝ, ∀ Φ : PathSpace d m T → ℝ, MemCb 5 Φ → ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T,
      ∀ j ≤ 3, ∀ y, ‖iteratedFDeriv ℝ j (heatFn γ Φ u) y - iteratedFDeriv ℝ j (heatFn γ Φ v) y‖ ≤
        C * cbNorm 5 Φ * |u - v| := by
  obtain ⟨C, hC⟩ := s7_PIB_lip_proj_proof R m hm T hT γ hγ
  obtain ⟨Pj, hPj1, -, hPj3, -⟩ := HRS.Sec7.projection_strong_proof (d := d) m T hT
  refine ⟨C, fun Φ hΦ u hu v hv j hj y => ?_⟩
  have hl1 := HRS.MC.Sec7.S7PIJ.s7_PIB_proj_limit_proof γ hγp Pj hPj3 hΦ j (by omega) u y
  have hl2 := HRS.MC.Sec7.S7PIJ.s7_PIB_proj_limit_proof γ hγp Pj hPj3 hΦ j (by omega) v y
  exact le_of_tendsto (hl1.sub hl2).norm
    (Filter.Eventually.of_forall fun L => hC Pj hPj1 L Φ hΦ u hu v hv j hj y)

end HRS.MC.Sec7.S7PIL

end
