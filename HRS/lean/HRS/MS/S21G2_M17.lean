import HRS.MS.S21G2_M16

/-!
# S21G2 M17 -- joint continuity of the heat derivatives in (index, spatial point) (R26-T3.M17)

For `Φ` in the `C_b^5` unit ball every `D^j Φ`, `j ≤ 4`, is 1-Lipschitz, so
`‖D^j u_w(y') - D^j u_v(y)‖ ≤ ‖y' - y‖ + ‖Γ_w - Γ_v‖_{L¹}` with `D^j u_v(y) = ∫ D^jΦ(y + Γ_v)` (M16).
Together with the `L¹`-continuity hypothesis this gives joint continuity.  Contract verbatim; helpers `s21g2_m17_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section Aux

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem s21g2_m17_le_one {Φ : B → ℝ} (hΦ : Φ ∈ HRS.CbUnitBall B 5) {k : ℕ} (hk : k ≤ 5) (y : B) :
    ‖iteratedFDeriv ℝ k Φ y‖ ≤ 1 := by
  refine le_trans (le_ciSup (f := fun z => ‖iteratedFDeriv ℝ k Φ z‖) (hΦ.2.1 k hk) y) ?_
  refine le_trans ?_ hΦ.2.2
  unfold HRS.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
    (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

theorem s21g2_m17_lip {Φ : B → ℝ} (hΦ : Φ ∈ HRS.CbUnitBall B 5) {j : ℕ} (hj : j ≤ 4) (x x' : B) :
    ‖iteratedFDeriv ℝ j Φ x - iteratedFDeriv ℝ j Φ x'‖ ≤ ‖x - x'‖ := by
  have hd : ∀ z, DifferentiableAt ℝ (iteratedFDeriv ℝ j Φ) z := fun z =>
    hΦ.1.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : j < 5)) z
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ j Φ) (C := 1)
    (fun z _ => hd z) (fun z _ => by
      rw [norm_fderiv_iteratedFDeriv]; exact s21g2_m17_le_one hΦ (by omega) z)
    convex_univ (mem_univ x') (mem_univ x)
  simpa using this

end Aux

theorem s21g2_m17_diff {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} (Γ : I → Ω → B) (hm : ∀ v, AEStronglyMeasurable (Γ v) P)
    {Φ : B → ℝ} (hΦ : Φ ∈ HRS.CbUnitBall B 5) {j : ℕ} (hj : j ≤ 4) (v w : I) (y y' : B)
    (hfin : eLpNorm (fun ω => Γ w ω - Γ v ω) 1 P < ⊤) :
    ‖(∫ ω, iteratedFDeriv ℝ j Φ (y' + Γ w ω) ∂P) - ∫ ω, iteratedFDeriv ℝ j Φ (y + Γ v ω) ∂P‖ ≤
      ‖y' - y‖ + (eLpNorm (fun ω => Γ w ω - Γ v ω) 1 P).toReal := by
  have hc : Continuous (iteratedFDeriv ℝ j Φ) := hΦ.1.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j ≤ 5))
  have hint : ∀ (u : I) (z : B), Integrable (fun ω => iteratedFDeriv ℝ j Φ (z + Γ u ω)) P := fun u z =>
    Integrable.of_bound (C := 1) ((hc.comp (continuous_const.add continuous_id)).comp_aestronglyMeasurable
      (hm u)) (ae_of_all _ fun ω => s21g2_m17_le_one hΦ (by omega) _)
  have hsub : AEStronglyMeasurable (fun ω => Γ w ω - Γ v ω) P := (hm w).sub (hm v)
  have hdn : Integrable (fun ω => ‖Γ w ω - Γ v ω‖) P := by
    refine ⟨hsub.norm, ?_⟩
    have := hfin
    rw [eLpNorm_one_eq_lintegral_enorm hsub] at this
    simpa [HasFiniteIntegral, enorm_norm] using this
  rw [← integral_sub (hint w y') (hint v y)]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb : ∫ ω, ‖Γ w ω - Γ v ω‖ ∂P = (eLpNorm (fun ω => Γ w ω - Γ v ω) 1 P).toReal := by
    rw [integral_norm_eq_lintegral_enorm hsub, eLpNorm_one_eq_lintegral_enorm hsub]
  calc ∫ ω, ‖iteratedFDeriv ℝ j Φ (y' + Γ w ω) - iteratedFDeriv ℝ j Φ (y + Γ v ω)‖ ∂P
      ≤ ∫ ω, (‖y' - y‖ + ‖Γ w ω - Γ v ω‖) ∂P :=
        integral_mono ((hint w y').sub (hint v y)).norm ((integrable_const _).add hdn) fun ω => by
          refine (s21g2_m17_lip hΦ hj _ _).trans ?_
          calc ‖y' + Γ w ω - (y + Γ v ω)‖ = ‖(y' - y) + (Γ w ω - Γ v ω)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
    _ = ‖y' - y‖ + (eLpNorm (fun ω => Γ w ω - Γ v ω) 1 P).toReal := by
        rw [integral_add (integrable_const _) hdn, hb]; simp

theorem r26t3_heat_time_continuity {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [TopologicalSpace I] (Γ : I → Ω → B)
    (hm : ∀ v, AEStronglyMeasurable (Γ v) P)
    (hc : ∀ v, Tendsto (fun w => eLpNorm (fun ω => Γ w ω-Γ v ω) 1 P) (𝓝 v) (𝓝 0))
    (Φ : B → ℝ) (hΦ : Φ∈HRS.CbUnitBall B 5) :
    ∀ j≤4, Continuous (fun z : I × B => iteratedFDeriv ℝ j (r26t3_heat P (Γ z.1) Φ) z.2) := by
  intro j hj
  have hform : ∀ (z : I × B), iteratedFDeriv ℝ j (r26t3_heat P (Γ z.1) Φ) z.2 =
      ∫ ω, iteratedFDeriv ℝ j Φ (z.2 + Γ z.1 ω) ∂P := fun z =>
    (r26t3_heat_bounds P (Γ z.1) (hm z.1) Φ hΦ).2 j (by omega) z.2
  simp_rw [hform]
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hfin : ∀ᶠ z in 𝓝 p, eLpNorm (fun ω => Γ z.1 ω - Γ p.1 ω) 1 P < ⊤ :=
    (continuous_fst.tendsto p).eventually
      (((hc p.1).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).mono fun w hw =>
        hw.trans ENNReal.one_lt_top)
  have hg : Tendsto (fun z : I × B => ‖z.2 - p.2‖ +
      (eLpNorm (fun ω => Γ z.1 ω - Γ p.1 ω) 1 P).toReal) (𝓝 p) (𝓝 0) := by
    have h1 : Tendsto (fun z : I × B => ‖z.2 - p.2‖) (𝓝 p) (𝓝 0) := by
      have := ((continuous_snd.tendsto p).sub_const p.2)
      simpa using this.norm
    have h2 : Tendsto (fun z : I × B => (eLpNorm (fun ω => Γ z.1 ω - Γ p.1 ω) 1 P).toReal) (𝓝 p) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ((hc p.1).comp (continuous_fst.tendsto p))
      simpa [Function.comp_def] using this
    simpa using h1.add h2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
  filter_upwards [hfin] with z hz
  exact s21g2_m17_diff P Γ hm hΦ hj p.1 z.1 p.2 z.2 hz

end HRS.MS.R26T3
