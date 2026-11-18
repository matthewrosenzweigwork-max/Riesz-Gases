import HRS.MS.CovMeasAux10

/-!
# S10.1 (worker S101B), part 11: a.e.-measurability of `τ ↦ D_τ(W_{s,α}, W_{s',β})`

`s101_W_tendsto`: `W_{t_n(τ),α} → W_{τ,α}` along the dyadic times `t_n(τ) ↓ τ`.
`s101_D_W_aem`: for `s, s' ∈ [0,T]`, the function `τ ↦ D_τ(W_{s,α}, W_{s',β})` is a.e.-measurable on `[0,T]`: on `τ < s ∧ s'` it is
`2ν z^τ(∇U^{τ,s}φ_α · ∇U^{τ,s'}φ_β)` (hypothesis `R2JIntegrandMeas`), on the other pieces the vectors `W_{s,α}` may be replaced by `W_{τ,α}`
(same pairing function) and the dyadic approximation `s101_aem_diag` applies.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

lemma s101_Ind_tendsto {m T : ℝ} (e : OscDual d m) {τ : ℝ} (hτ : 0 ≤ τ) {tn : ℕ → ℝ}
    (h1 : ∀ n, τ ≤ tn n) (h2 : Tendsto tn atTop (𝓝 τ)) :
    Tendsto (fun n => s101Ind m T (tn n) e) atTop (𝓝 (s101Ind m T τ e)) := by
  unfold s101Ind
  refine tendsto_indicatorConstLp_set (by norm_num) ?_
  have hb : ∀ n, (volume.restrict (Icc (0 : ℝ) T)) (symmDiff (Icc 0 (tn n)) (Icc 0 τ)) ≤ ENNReal.ofReal (tn n - τ) := by
    intro n
    refine (Measure.restrict_apply_le _ _).trans ?_
    calc volume (symmDiff (Icc 0 (tn n)) (Icc 0 τ)) ≤ volume (Ioc τ (tn n)) := by
          refine measure_mono fun x hx => ?_
          rcases Set.mem_symmDiff.1 hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
          · exact ⟨not_le.1 fun h => hx2 ⟨hx1.1, h⟩, hx1.2⟩
          · exact absurd ⟨hx1.1, hx1.2.trans (h1 n)⟩ hx2
      _ = ENNReal.ofReal (tn n - τ) := Real.volume_Ioc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hb
  have : Tendsto (fun n => tn n - τ) atTop (𝓝 0) := by
    simpa using h2.sub_const τ
  simpa using ENNReal.tendsto_ofReal this

lemma s101_W_tendsto {m T : ℝ} (α : MultiIndex d) {τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T) :
    Tendsto (fun n => s101W m T (s101tn T n τ) α) atTop (𝓝 (s101W m T τ α)) := by
  have hInd := s101_Ind_tendsto (T := T) (s101e m α) hτ (fun n => (s101tn_lt hτ hτT n).le)
    (s101tn_tendsto hτ hτT)
  have hc : Continuous fun a' : L2Path d m T => (s55fE (d := d) m T).symm (0, (a', s101e m α)) :=
    (s55fE (d := d) m T).symm.continuous.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  exact (hc.tendsto _).comp hInd

end HRS.MS.CovMeas
