import HRS.MS.SuppU1Aux1

/-!
# U1 aux 4: dominated convergence in `L^r`, shifted-ball integrals of the profile.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HRS.Whole.U1

/-- dominated convergence for `L^r` norms (`r > 0`) along a sequence converging a.e. -/
lemma u1_tendsto_eLpNorm_of_dom {α : Type*} [MeasurableSpace α] (P : Measure α) {r : ℝ} (hr : 0 < r)
    (f : ℕ → α → ℝ) (g bd : α → ℝ) (hf : ∀ n, AEMeasurable (f n) P) (hg : AEMeasurable g P)
    (hbd : ∀ n, ∀ᵐ x ∂P, |f n x - g x| ≤ bd x)
    (hint : ∫⁻ x, ENNReal.ofReal (bd x ^ r) ∂P ≠ ⊤)
    (hlim : ∀ᵐ x ∂P, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) (ENNReal.ofReal r) P) atTop (𝓝 0) := by
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => f n x - g x) P := fun n =>
    ((hf n).sub hg).aestronglyMeasurable
  have key : ∀ n, eLpNorm (fun x => f n x - g x) (ENNReal.ofReal r) P
      = (∫⁻ x, ‖f n x - g x‖ₑ ^ r ∂P) ^ (1 / r) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hmeas n), ENNReal.toReal_ofReal hr.le]
  simp_rw [key]
  have hT : Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ r ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := P)
      (F := fun n x => ‖f n x - g x‖ₑ ^ r) (f := fun _ => 0)
      (fun x => ENNReal.ofReal (bd x ^ r))
      (fun n => ((hmeas n).enorm.pow_const r)) ?_ hint ?_
    · simpa using this
    · intro n
      filter_upwards [hbd n] with x hx
      have h0 : 0 ≤ bd x := le_trans (abs_nonneg _) hx
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr.le]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) hx hr.le)
    · filter_upwards [hlim] with x hx
      have : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => f n x - g x) atTop (𝓝 0) := by
          simpa using hx.sub_const (g x)
        simpa [Function.comp_def] using (continuous_enorm (E := ℝ)).tendsto 0 |>.comp h1
      have := (ENNReal.continuous_rpow_const (y := r)).tendsto 0 |>.comp this
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hr] using this
  have := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0 |>.comp hT
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr), ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)] using this

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- shifted-ball integral of the profile: `∫_{B(x,a)} Vs(|x - y|)^r dy ≤ a^d Vs(a)^r J_r`. -/
lemma u1_lintegral_Vs_shift {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (x : E) {a : ℝ} (ha : 0 < a) :
    ∫⁻ y in ball x a, ENNReal.ofReal (u1Vs s ‖x - y‖ ^ r) ∂μ
      ≤ ENNReal.ofReal (a ^ Module.finrank ℝ E * u1Vs s a ^ r) * u1J μ s r := by
  have hmp : MeasurePreserving (fun y : E => x - y) μ μ := Measure.measurePreserving_sub_left μ x
  have hemb : MeasurableEmbedding (fun y : E => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have hpre : (fun y : E => x - y) ⁻¹' ball (0 : E) a = ball x a := by
    ext y
    simp [mem_ball_iff_norm, dist_eq_norm, norm_sub_rev]
  rw [← hpre, hmp.setLIntegral_comp_preimage_emb hemb (fun z => ENNReal.ofReal (u1Vs s ‖z‖ ^ r))]
  exact u1_lintegral_Vs_ball μ hs hr ha

end HRS.Whole.U1
