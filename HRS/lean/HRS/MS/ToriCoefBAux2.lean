import HRS.MS.ToriCoefBAux1

/-!
# MS-TORI-COEFB, helper file 2: regularity and bounds of `T_k g` by induction on the order

`g ∈ C^{n+2}` with `‖D^i g‖ ≤ Bd` (`i ≤ n+2`) and `∫_{Q_L} ‖D^i g(x - z)‖ dz ≤ Bc` (`i ≤ n`) give
`T g ∈ C^n` and `‖D^i (T g)‖ ≤ a Bd + Kf Bc` (`i ≤ n`).  The induction runs over all Banach targets `W`
(`D (T g) = T (D g)` with `W' = E →L W`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- Sup bound for `T g`. -/
theorem tcb_T_norm_le {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (g : Euc d → W)
    (hg : Differentiable ℝ g) (B0 B1 : ℝ) (h0 : ∀ y, ‖g y‖ ≤ B0) (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ B1)
    (Bc : ℝ) (x : Euc d) (hBc : ∫ z in tcb_Q d L, ‖g (x - z)‖ ≤ Bc) :
    ‖tcb_T L k g x‖ ≤ tcb_a k * B1 + Kf * Bc := by
  have hint2 : Integrable (fun z => ‖g (x - z)‖) (volume.restrict (tcb_Q d L)) := by
    have : IsFiniteMeasure (volume.restrict (tcb_Q d L)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact tcb_measure_Q_lt_top L⟩
    refine Integrable.mono' (integrable_const B0) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (hg.continuous.comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable
    · rw [norm_norm]; exact h0 _
  have hint1 : Integrable ((tcb_N d).indicator (fun z => |k z| * ‖z‖ * B1))
      (volume.restrict (tcb_Q d L)) := by
    rw [integrable_indicator_iff tcb_measurableSet_N]
    exact (hk.intN.mul_const B1).mono_measure (Measure.restrict_mono_measure Measure.restrict_le_self _)
  have hle : ‖tcb_T L k g x‖ ≤ ∫ z in tcb_Q d L,
      ((tcb_N d).indicator (fun z => |k z| * ‖z‖ * B1) z + Kf * ‖g (x - z)‖) := by
    unfold tcb_T
    refine norm_integral_le_of_norm_le (hint1.add (hint2.const_mul Kf)) ?_
    filter_upwards [ae_restrict_mem (tcb_measurableSet_Q L)] with z hz
    exact tcb_F_bound hk g hg B1 h1 x z hz
  refine hle.trans ?_
  rw [integral_add hint1 (hint2.const_mul Kf), integral_const_mul,
    setIntegral_indicator tcb_measurableSet_N, Set.inter_eq_right.2 (tcb_N_subset_Q hk.hL),
    integral_mul_const]
  have := mul_le_mul_of_nonneg_left hBc hk.hKf
  unfold tcb_a
  linarith

theorem tcb_main {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (Bd Bc : ℝ) :
    ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (g : Euc d → W),
      ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) g →
      (∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Bd) →
      (∀ i ≤ n, ∀ x, ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ i g (x - z)‖ ≤ Bc) →
      ContDiff ℝ (n : WithTop ℕ∞) (tcb_T L k g) ∧
      ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (tcb_T L k g) x‖ ≤ tcb_a k * Bd + Kf * Bc := by
  intro n
  induction n with
  | zero =>
    intro W _ _ _ g hg hD hc
    have hg2 : ContDiff ℝ 2 g := by exact_mod_cast hg
    have h0 : ∀ y, ‖g y‖ ≤ Bd := fun y => by
      have := hD 0 (by omega) y
      rwa [norm_iteratedFDeriv_zero] at this
    have h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
      have := hD 1 (by omega) y
      rwa [norm_iteratedFDeriv_one] at this
    have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ Bd := fun y => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hD 2 (by omega) y
    have hdiff := tcb_hasFDerivAt hk g hg2 Bd Bd Bd h0 h1 h2
    refine ⟨?_, fun i hi x => ?_⟩
    · have : Continuous (tcb_T L k g) := continuous_iff_continuousAt.2 fun x => (hdiff x).continuousAt
      exact contDiff_zero.2 this
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [norm_iteratedFDeriv_zero]
      refine tcb_T_norm_le hk g (hg2.differentiable (by norm_num)) Bd Bd h0 h1 Bc x ?_
      have := hc 0 le_rfl x
      simpa [norm_iteratedFDeriv_zero] using this
  | succ n ih =>
    intro W _ _ _ g hg hD hc
    have hg2 : ContDiff ℝ 2 g := by
      refine hg.of_le ?_
      exact_mod_cast (by omega : 2 ≤ n + 1 + 2)
    have h0 : ∀ y, ‖g y‖ ≤ Bd := fun y => by
      have := hD 0 (by omega) y
      rwa [norm_iteratedFDeriv_zero] at this
    have h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
      have := hD 1 (by omega) y
      rwa [norm_iteratedFDeriv_one] at this
    have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ Bd := fun y => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hD 2 (by omega) y
    have hdiff := tcb_hasFDerivAt hk g hg2 Bd Bd Bd h0 h1 h2
    have hfd : fderiv ℝ (tcb_T L k g) = tcb_T L k (fderiv ℝ g) := funext fun x => (hdiff x).fderiv
    have hg' : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fderiv ℝ g) := by
      refine hg.fderiv_right ?_
      push_cast
      exact le_of_eq (by ring)
    have hD' : ∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i (fderiv ℝ g) y‖ ≤ Bd := fun i hi y => by
      rw [norm_iteratedFDeriv_fderiv]
      exact hD (i + 1) (by omega) y
    have hc' : ∀ i ≤ n, ∀ x, ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ i (fderiv ℝ g) (x - z)‖ ≤ Bc :=
      fun i hi x => by
        simp_rw [norm_iteratedFDeriv_fderiv]
        exact hc (i + 1) (by omega) x
    have IH := ih (Euc d →L[ℝ] W) (fderiv ℝ g) hg' hD' hc'
    refine ⟨?_, fun i hi x => ?_⟩
    · have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (tcb_T L k g) := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨fun x => (hdiff x).differentiableAt, by simp, ?_⟩
        rw [hfd]
        exact IH.1
      exact_mod_cast this
    · rcases i with _ | i
      · rw [norm_iteratedFDeriv_zero]
        refine tcb_T_norm_le hk g (hg2.differentiable (by norm_num)) Bd Bd h0 h1 Bc x ?_
        have := hc 0 (by omega) x
        simpa [norm_iteratedFDeriv_zero] using this
      · rw [← norm_iteratedFDeriv_fderiv, hfd]
        exact IH.2 i (by omega) x

end HRS.MS.ToriCoefB
