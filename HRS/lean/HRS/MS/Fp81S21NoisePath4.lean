import HRS.MS.Fp81S21NoisePath3

/-! Sixth-moment bound for the measurable reconstructed path. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.GenPath HRS.MS.R26T3
open HRS.MP.RdRem HRS.MS.U9

/-- A universal sixth-power Hilbert BDG constant. -/
def fp81s21_noisePathBDG : ℝ := Classical.choose fp81s21_noisePath_uniform_bdg

/-- The reconstructed path is measurable and matches every oscillator coordinate
at every clamped rational local time on one common full-measure event. -/
theorem fp81s21_noisePath_moment_match
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b))
    (hC : OscAdjointInput (r26t3_coeff R)
      ((wholeSpaceIndex p.d : ℕ) : ℝ) (b + H))
    (hK : ∀ (a : Fin p.d) (r : ℝ), r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      S105WinK (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ) H b a r x)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a r, r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B) :
    ∃ G : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H,
      AEMeasurable G A.P ∧
      Integrable (fun ζ => ‖G ζ‖ ^ 6) A.P ∧
      (∫ ζ, ‖G ζ‖ ^ 6 ∂A.P) ≤
        (3 + Real.sqrt H) ^ 6 * fp81s21_noisePathBDG *
          (H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)) ^ 3 ∧
      ∀ᵐ ζ ∂A.P, ∀ (α : MultiIndex p.d) (q : ℚ),
        OscDual.coord (OscPath.at' (G ζ) ⟨mrrClamp H (q : ℝ), mrrClamp_mem hH.le (q : ℝ)⟩) α =
          fp81s21_shiftedNoiseDiff p R A F b (b + mrrClamp H (q : ℝ)) α ζ := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let M := Classical.choose (fp81s21_shiftedNoise_feature_martingale p R hN A F hH hb hphysical)
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil F.ℱ b.toNNReal
  have hIto := (Classical.choose_spec (fp81s21_shiftedNoise_feature_martingale
    p R hN A F hH hb hphysical)).1
  have hMm : ∀ t, Measurable (M t) := fun t => (hIto.adapted t).mono (ℱb.le t) le_rfl
  have hrecm : ∀ t, Measurable fun ζ => reconstructPath m H M ζ t := fun t => by
    unfold reconstructPath
    exact (((s56_evalA_cont hH.le t).measurable.comp (hMm H)).sub
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm H))).add
      (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm t))
  have hcont : ∀ ζ, ContinuousOn (fun t => reconstructPath m H M ζ t) (Icc 0 H) := by
    intro ζ
    exact continuousOn_iff_continuous_domRestrict.2
      (HRS.MS.U9.u9_continuous_recon hH.le M ζ (hIto.cont ζ).continuousOn)
  let G : A.Ω → OscPath p.d m H := fun ζ => windowPathOf m H 0 (fun t => reconstructPath m H M ζ t)
  have hG : AEMeasurable G A.P := by
    have hm := HRS.GF.gfb4_aemeasurable_windowPath A.P hH.le
      (fun t ζ => reconstructPath m H M ζ t) (fun t _ => hrecm t)
      (Filter.Eventually.of_forall hcont)
    rwa [← s56_wpo_eq_windowPath] at hm
  let Sg : ℝ → A.Ω → KSpace p.d m H →L[ℝ] KSpace p.d m H →L[ℝ] ℝ :=
    fun u ζ => hsCovForm (s105Phi
      (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
      (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X) u ζ)
  have hHM : IsHilbertMartingaleWithCovariation A.P ℱb H M Sg :=
    (Classical.choose_spec (fp81s21_shiftedNoise_feature_martingale p R hN A F hH hb hphysical)).2
  let K : ℝ := H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)
  have hβinv : 0 ≤ p.β⁻¹ := inv_nonneg.mpr p.hβ.le
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have htrace : ∀ᵐ ζ ∂A.P, ∫ u in Icc (0 : ℝ) H, traceNormForm (Sg u ζ) ≤ K :=
    fp81s21_shiftedNoise_trace_integral p R hN A F hH hb hphysical B hB hbound
  have hmax := (Classical.choose_spec fp81s21_noisePath_uniform_bdg).2
    m H hH.le p.d A.P ℱb M Sg hHM K hK0 htrace
  have hpoint : ∀ ζ, ENNReal.ofReal ‖G ζ‖ ≤
      ⨆ t : Icc (0 : ℝ) H, ENNReal.ofReal ‖reconstructPath m H M ζ t‖ := by
    intro ζ
    let V : ℝ≥0∞ := ⨆ t : Icc (0 : ℝ) H, ENNReal.ofReal ‖reconstructPath m H M ζ t‖
    change ENNReal.ofReal ‖G ζ‖ ≤ V
    by_cases hV : V = ⊤
    · rw [hV]; exact le_top
    have hn : ‖G ζ‖ ≤ V.toReal := by
      refine (ContinuousMap.norm_le (show C(Icc (0 : ℝ) H, OscDual p.d m) from G ζ)
        ENNReal.toReal_nonneg).2 fun t => ?_
      rw [show (show C(Icc (0 : ℝ) H, OscDual p.d m) from G ζ) t =
        reconstructPath m H M ζ t from s56_wpo_apply (hcont ζ) t]
      have ht : ENNReal.ofReal ‖reconstructPath m H M ζ t‖ ≤ V := by
        dsimp [V]
        exact le_iSup (fun t : Icc (0 : ℝ) H => ENNReal.ofReal ‖reconstructPath m H M ζ t‖) t
      have ht' := ENNReal.toReal_mono hV ht
      simpa using ht'
    calc ENNReal.ofReal ‖G ζ‖ ≤ ENNReal.ofReal V.toReal := ENNReal.ofReal_le_ofReal hn
      _ = V := ENNReal.ofReal_toReal hV
  have hpower : ∫⁻ ζ, ENNReal.ofReal (‖G ζ‖ ^ 6) ∂A.P ≤
      ENNReal.ofReal ((3 + Real.sqrt H) ^ 6 * fp81s21_noisePathBDG * K ^ 3) := by
    calc
      _ ≤ ∫⁻ ζ, (⨆ t : Icc (0 : ℝ) H,
          ENNReal.ofReal ‖reconstructPath m H M ζ t‖) ^ 6 ∂A.P := by
        apply lintegral_mono
        intro ζ
        dsimp only
        rw [ENNReal.ofReal_pow (norm_nonneg _)]
        exact pow_le_pow_left' (hpoint ζ) 6
      _ ≤ _ := hmax
  have hnonneg : ∀ ζ, 0 ≤ ‖G ζ‖ ^ 6 := fun ζ => by positivity
  have hint : Integrable (fun ζ => ‖G ζ‖ ^ 6) A.P := by
    refine ⟨(hG.norm.pow_const 6).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
    exact lt_of_le_of_lt hpower ENNReal.ofReal_lt_top
  have hC0 : 0 ≤ fp81s21_noisePathBDG := (Classical.choose_spec fp81s21_noisePath_uniform_bdg).1
  have hreal : (∫ ζ, ‖G ζ‖ ^ 6 ∂A.P) ≤
      (3 + Real.sqrt H) ^ 6 * fp81s21_noisePathBDG * K ^ 3 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
      hint.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpower
    rwa [ENNReal.toReal_ofReal (by positivity :
      0 ≤ (3 + Real.sqrt H) ^ 6 * fp81s21_noisePathBDG * K ^ 3)] at h
  refine ⟨G, hG, hint, hreal, ?_⟩
  have heq : ∀ᵐ ζ ∂A.P, ∀ (α : MultiIndex p.d) (q : ℚ),
      OscDual.coord (reconstructPath m H M ζ (mrrClamp H (q : ℝ))) α =
        fp81s21_shiftedNoiseDiff p R A F b (b + mrrClamp H (q : ℝ)) α ζ := by
    apply ae_all_iff.2
    intro α
    apply ae_all_iff.2
    intro q
    exact fp81s21_shiftedNoise_reconstruction_at p R hN A F hH hb
      hphysical hC hK (mrrClamp_mem hH.le (q : ℝ)) α
  filter_upwards [heq] with ζ hζ α q
  rw [show OscPath.at' (G ζ) ⟨mrrClamp H (q : ℝ), mrrClamp_mem hH.le (q : ℝ)⟩ =
    reconstructPath m H M ζ (mrrClamp H (q : ℝ)) from
      s56_wpo_apply (hcont ζ) ⟨_, _⟩]
  exact hζ α q

#print axioms HRS.Fp81.S21.fp81s21_noisePath_moment_match
end HRS.Fp81.S21
