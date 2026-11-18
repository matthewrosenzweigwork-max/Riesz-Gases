import HRS.MS.Fp81S21NoisePath

/-! A measurable continuous reconstructed path and its simultaneous rational identities. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.GenPath HRS.MS.R26T3
open HRS.MP.RdRem

/-- The reconstructed path is measurable and matches every oscillator coordinate
at every clamped rational local time on one common full-measure event. -/
theorem fp81s21_noisePath_match
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b))
    (hC : OscAdjointInput (r26t3_coeff R)
      ((wholeSpaceIndex p.d : ℕ) : ℝ) (b + H))
    (hK : ∀ (a : Fin p.d) (r : ℝ), r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      S105WinK (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ) H b a r x) :
    ∃ G : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H,
      AEMeasurable G A.P ∧
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
  refine ⟨G, hG, ?_⟩
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

#print axioms HRS.Fp81.S21.fp81s21_noisePath_match
end HRS.Fp81.S21
