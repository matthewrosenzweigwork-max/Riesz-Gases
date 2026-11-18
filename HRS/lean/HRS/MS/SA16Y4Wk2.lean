import HRS.MS.SA16Y4S5d
import HRS.MS.SA16Y4Wk1

/-!
# S.A.16 (SA16Y4) Wk2: pairings of a jet COMPONENT with test functions converging in `L^{p'}`

`sa16y4_cmp τ H x = (H x) τ`; `sa16y4_comp_Lq_bound`: `|∫ H_τ N| ≤ ‖H‖ ‖N‖_{L^{p'}}`;
`sa16y4_comp_tendsto_Lq`: bounded weakly convergent `g_j ⇀ G` and `N_j → N` in `L^{p'}` give `∫ (g_j)_τ N_j → ∫ G_τ N`
(the derivative-on-`y` form of the transport and nonlocal terms: only `C^0` convergence of the coefficients is needed).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Wk2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the component `τ` of an element of `WmpSpace` -/
def sa16y4_cmp (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (τ : WIndex d m) (H : WmpSpace d m p)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((H : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x τ

lemma sa16y4_cmp_aesm {m : ℕ} (τ : WIndex d m) (H : WmpSpace d m p) :
    AEStronglyMeasurable (fun x => sa16y4_cmp d m p τ H x) volume :=
  (continuous_apply τ).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (H : WLp d m p))

lemma sa16y4_cmp_eLp {m : ℕ} (τ : WIndex d m) (H : WmpSpace d m p) :
    eLpNorm (fun x => sa16y4_cmp d m p τ H x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ‖H‖ := by
  have hcoe : MemLp (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume := Lp.memLp (H : WLp d m p)
  have hfin := hcoe.eLpNorm_lt_top.ne
  have hn : ‖H‖ = (eLpNorm (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume).toReal := Lp.norm_def (H : WLp d m p)
  have hdiff : ENNReal.ofReal ‖H‖ = eLpNorm (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
      (ENNReal.ofReal p) volume := by
    rw [hn, ENNReal.ofReal_toReal hfin]
  calc eLpNorm (fun x => sa16y4_cmp d m p τ H x) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ‖((H : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x‖)
          (ENNReal.ofReal p) volume :=
        eLpNorm_mono_real (sa16y4_cmp_aesm τ H) (fun x => norm_le_pi_norm
          (((H : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x) τ)
    _ = eLpNorm (((H : WLp d m p)) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ))
          (ENNReal.ofReal p) volume := eLpNorm_norm _ hcoe.aestronglyMeasurable
    _ = ENNReal.ofReal ‖H‖ := hdiff.symm

lemma sa16y4_cmp_memLp {m : ℕ} (τ : WIndex d m) (H : WmpSpace d m p) :
    MemLp (fun x => sa16y4_cmp d m p τ H x) (ENNReal.ofReal p) volume :=
  (sa16y4_cmp_eLp τ H).trans_lt ENNReal.ofReal_lt_top

theorem sa16y4_comp_Lq_bound {m : ℕ} (τ : WIndex d m) (G : WmpSpace d m p) {N : Euc d → ℝ}
    (hNm : AEStronglyMeasurable N volume) (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume) :
    |∫ x, sa16y4_cmp d m p τ G x * N x| ≤ ‖G‖ * (eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal := by
  haveI := sa16y4_holderConj (p := p)
  have hw : AEStronglyMeasurable (fun x => sa16y4_cmp d m p τ G x) volume := sa16y4_cmp_aesm τ G
  have h1 : |∫ x, sa16y4_cmp d m p τ G x * N x| ≤ ∫ x, ‖sa16y4_cmp d m p τ G x * N x‖ := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := (volume : Measure (Euc d)))
      (fun x => sa16y4_cmp d m p τ G x * N x)
  refine h1.trans ?_
  have hmul : AEStronglyMeasurable (fun x => sa16y4_cmp d m p τ G x * N x) volume := hw.mul hNm
  rw [integral_norm_eq_lintegral_enorm hmul]
  have h2 : eLpNorm (fun x => sa16y4_cmp d m p τ G x * N x) 1 volume ≤
      eLpNorm (fun x => sa16y4_cmp d m p τ G x) (ENNReal.ofReal p) volume *
        eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume := by
    have := eLpNorm_smul_le_mul_eLpNorm (μ := (volume : Measure (Euc d))) (p := ENNReal.ofReal p)
      (q := ENNReal.conjExponent (ENNReal.ofReal p)) (r := 1) hw hNm
    exact this
  rw [← eLpNorm_one_eq_lintegral_enorm hmul]
  have h3 := sa16y4_cmp_eLp τ G
  have hfin : eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume ≠ ⊤ := hN.eLpNorm_lt_top.ne
  have h4 : eLpNorm (fun x => sa16y4_cmp d m p τ G x * N x) 1 volume ≤
      ENNReal.ofReal ‖G‖ * eLpNorm N (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    h2.trans (mul_le_mul' h3 le_rfl)
  have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h4
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at h5

theorem sa16y4_comp_tendsto_Lq {m : ℕ} (τ : WIndex d m) {Bm : ℝ} (gs : ℕ → WmpSpace d m p) (G : WmpSpace d m p)
    (hbd : ∀ j, ‖gs j‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (gs j)) atTop (𝓝 (ℓ G)))
    (Nn : ℕ → Euc d → ℝ) (N : Euc d → ℝ)
    (hNjm : ∀ j, AEStronglyMeasurable (Nn j) volume) (hNm : AEStronglyMeasurable N volume)
    (hNj : ∀ j, MemLp (Nn j) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hN : MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hconv : Tendsto (fun j => (eLpNorm (fun x => Nn j x - N x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, sa16y4_cmp d m p τ (gs j) x * Nn j x) atTop (𝓝 (∫ x, sa16y4_cmp d m p τ G x * N x)) := by
  have hBm : 0 ≤ Bm := (norm_nonneg _).trans (hbd 0)
  have hwj : ∀ j, MemLp (fun x => sa16y4_cmp d m p τ (gs j) x) (ENNReal.ofReal p) volume := fun j => sa16y4_cmp_memLp τ _
  have h1 : Tendsto (fun j => ∫ x, sa16y4_cmp d m p τ (gs j) x * N x) atTop (𝓝 (∫ x, sa16y4_cmp d m p τ G x * N x)) := by
    have := hw ((sa16so_pairN d m p τ hN).comp (WmpSpace d m p).subtypeL)
    simp only [ContinuousLinearMap.comp_apply, sa16so_pairN_apply] at this
    exact this
  have hdiff : ∀ j, |(∫ x, sa16y4_cmp d m p τ (gs j) x * Nn j x) - ∫ x, sa16y4_cmp d m p τ (gs j) x * N x| ≤
      Bm * (eLpNorm (fun x => Nn j x - N x) (ENNReal.conjExponent (ENNReal.ofReal p)) volume).toReal := by
    intro j
    have hi1 : Integrable (fun x => sa16y4_cmp d m p τ (gs j) x * Nn j x) :=
      (hwj j).integrable_mul (hNj j)
    have hi2 : Integrable (fun x => sa16y4_cmp d m p τ (gs j) x * N x) := (hwj j).integrable_mul hN
    have : (∫ x, sa16y4_cmp d m p τ (gs j) x * Nn j x) - ∫ x, sa16y4_cmp d m p τ (gs j) x * N x =
        ∫ x, sa16y4_cmp d m p τ (gs j) x * (Nn j x - N x) := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [this]
    exact (sa16y4_comp_Lq_bound τ (gs j) ((hNjm j).sub hNm) ((hNj j).sub hN)).trans
      (mul_le_mul_of_nonneg_right (hbd j) ENNReal.toReal_nonneg)
  have h2 : Tendsto (fun j => (∫ x, sa16y4_cmp d m p τ (gs j) x * Nn j x) - ∫ x, sa16y4_cmp d m p τ (gs j) x * N x)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) (by simpa using hconv.const_mul Bm)
    rw [Real.norm_eq_abs]; exact hdiff j
  simpa using h2.add h1

end Wk2

end HRS.Whole.AppendixA.Phase2SA16R
