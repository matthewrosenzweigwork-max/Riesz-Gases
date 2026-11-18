import HRS.MS.SA16Y3Ex7

/-!
# S.A.16 (SA16Y3) Ex8: SA16S item (iii) for general `φ ∈ W^{m,p}` (step (d2))

For `φ` with `wNormE m p φ < ∞` and the cut-off mollifiers `φ_n := cutmol n φ = ρ_n ⋆ (χ_{n+1} φ)`:
`sa16y3_iii`: `wNormE m p φ_n ≤ C · wNormE m p φ` (uniform in `n`), and `wNormE m p (φ_n - φ) → 0`.
Both come from the extensions `T_n` on `WmpSpace` (`‖T_n‖ ≤ C`, zeroth component `cutmol_n`):
`T_n G` is a lift of `φ_n`, and `T_n G - G` is a lift of `φ_n - φ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution

variable {d : ℕ}

theorem sa16y3_iii {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
      (∀ n : ℕ, wNormE m p (sa16y3_cutmol d n φ) ≤ ENNReal.ofReal C * wNormE m p φ) ∧
      Tendsto (fun n : ℕ => wNormE m p (fun x => sa16y3_cutmol d n φ x - φ x)) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hex⟩ := sa16y3_extend_cutmol (d := d) hp m
  choose T hTn hTJ using hex
  refine ⟨C, hC0, fun φ hφ => ⟨fun n => ?_, ?_⟩⟩
  · -- the lifts of `φ` and the bound on the lifts of `φ_n`
    have key : ∀ G : WmpSpace d m p, (fun x => wrep d m p G x) =ᵐ[volume] φ →
        wNormE m p (sa16y3_cutmol d n φ) ≤ ENNReal.ofReal (C * ‖G‖) := by
      intro G hG
      have hcut : sa16y3_cutmol d n (wrep d m p G) = sa16y3_cutmol d n φ :=
        sa16y3_cutmol_congr n hG
      have hl : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
          wrep d m p (T n G) x = sa16y3_cutmol d n φ x := by
        filter_upwards [sa16y3_T_wrep n (T n) (hTn n) (hTJ n) G] with x hx
        rw [hx, congrFun hcut x]
      have hle : ‖T n G‖ ≤ C * ‖G‖ := ((T n).le_opNorm G).trans (mul_le_mul_of_nonneg_right (hTn n) (norm_nonneg _))
      unfold wNormE
      exact (iInf_le_of_le (T n G) (iInf_le _ hl)).trans (ENNReal.ofReal_le_ofReal hle)
    -- lifts with small norm
    have hlift : ∀ δ : ℝ≥0∞, 0 < δ → ∃ G : WmpSpace d m p, (fun x => wrep d m p G x) =ᵐ[volume] φ ∧
        ENNReal.ofReal ‖G‖ < wNormE m p φ + δ := by
      intro δ hδ
      have h : wNormE m p φ < wNormE m p φ + δ := ENNReal.lt_add_right hφ.ne hδ.ne'
      unfold wNormE at h ⊢
      obtain ⟨G, hG⟩ := iInf_lt_iff.1 h
      obtain ⟨hP, hlt⟩ := iInf_lt_iff.1 hG
      exact ⟨G, hP, hlt⟩
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hεr : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.2 hε
    set δ : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / (C + 1)) with hδdef
    have hδpos : 0 < δ := ENNReal.ofReal_pos.2 (div_pos hεr (by linarith))
    obtain ⟨G, hG, hGlt⟩ := hlift δ hδpos
    calc wNormE m p (sa16y3_cutmol d n φ) ≤ ENNReal.ofReal (C * ‖G‖) := key G hG
      _ = ENNReal.ofReal C * ENNReal.ofReal ‖G‖ := ENNReal.ofReal_mul hC0
      _ ≤ ENNReal.ofReal C * (wNormE m p φ + δ) := mul_le_mul' le_rfl hGlt.le
      _ = ENNReal.ofReal C * wNormE m p φ + ENNReal.ofReal C * δ := mul_add _ _ _
      _ ≤ ENNReal.ofReal C * wNormE m p φ + (ε : ℝ≥0∞) := by
          apply add_le_add le_rfl
          rw [hδdef, ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          have hfrac : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          calc C * ((ε : ℝ) / (C + 1)) = (ε : ℝ) * (C / (C + 1)) := by ring
            _ ≤ (ε : ℝ) * 1 := mul_le_mul_of_nonneg_left hfrac hεr.le
            _ = (ε : ℝ) := mul_one _
  · -- convergence along a fixed lift
    have hlift0 : ∃ G : WmpSpace d m p, (fun x => wrep d m p G x) =ᵐ[volume] φ := by
      have h : wNormE m p φ < wNormE m p φ + 1 := ENNReal.lt_add_right hφ.ne one_ne_zero
      unfold wNormE at h
      obtain ⟨G, hG⟩ := iInf_lt_iff.1 h
      obtain ⟨hP, _⟩ := iInf_lt_iff.1 hG
      exact ⟨G, hP⟩
    obtain ⟨G, hG⟩ := hlift0
    have hbound : ∀ n : ℕ, wNormE m p (fun x => sa16y3_cutmol d n φ x - φ x) ≤
        ENNReal.ofReal ‖T n G - G‖ := by
      intro n
      have hcut : sa16y3_cutmol d n (wrep d m p G) = sa16y3_cutmol d n φ :=
        sa16y3_cutmol_congr n hG
      have hl : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
          wrep d m p (T n G - G) x = (fun x => sa16y3_cutmol d n φ x - φ x) x := by
        filter_upwards [sa16y3_wrep_sub (T n G) G, sa16y3_T_wrep n (T n) (hTn n) (hTJ n) G, hG]
          with x h1 h2 h3
        rw [h1, h2, congrFun hcut x, h3]
      unfold wNormE
      exact iInf_le_of_le (T n G - G) (iInf_le _ hl)
    have hlim : Tendsto (fun n => ENNReal.ofReal ‖T n G - G‖) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (sa16y3_T_tendsto hp m hC0 T hTn hTJ G)
      rwa [ENNReal.ofReal_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound

end HRS.Whole.AppendixA.Phase2SA16R
