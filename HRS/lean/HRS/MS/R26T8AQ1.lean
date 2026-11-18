import HRS.MS.R26T8AP11s

/-!
# S8.2 Taylor split (Q), step 1: generic convolution potential `Wg` of a smooth compactly supported source
`Wg alpha src Y w = ∫ ‖w-v‖^(alpha-d) src(Y + v/2, v) dv` (`src` vanishing for `|v| > 2`): joint smoothness (`r26t8a_Wg_contDiff`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_Wg (alpha : ℝ) (src : Euc d × Euc d → ℝ) (Y w : Euc d) : ℝ :=
  ∫ v, ‖w - v‖ ^ (alpha - (d : ℝ)) * src (Y + (1 / 2 : ℝ) • v, v)

theorem r26t8a_Wg_conv (alpha : ℝ) (src : Euc d × Euc d → ℝ) (Y w : Euc d) :
    r26t8a_Wg alpha src Y w = ∫ u, ‖u‖ ^ (alpha - (d : ℝ)) *
      (fun Yw : Euc d × Euc d => src (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.2)) (Y, w - u) := by
  unfold r26t8a_Wg
  rw [← integral_sub_left_eq_self (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ)) *
    (fun Yw : Euc d × Euc d => src (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.2)) (Y, w - u)) volume w]
  congr 1
  funext v
  simp only [sub_sub_cancel]

theorem r26t8a_Wg_contDiff (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (src : Euc d × Euc d → ℝ) {n : ℕ} (hsrc : ContDiff ℝ (n : WithTop ℕ∞) src)
    (hSv : ∀ Y v : Euc d, 2 < ‖v‖ → src (Y, v) = 0) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Wg alpha src Yw.1 Yw.2) := by
  obtain ⟨CK, hCK0, -, -, hKm⟩ := r26t8a_riesz_potential_jets d hd alpha halpha had 0
  have hKi : ∀ r : ℝ, IntegrableOn (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) (ball (0 : Euc d) r) := by
    intro r
    by_cases hr : 0 < r
    · exact (hKm r hr).1
    · rw [ball_eq_empty.2 (not_lt.1 hr)]
      exact integrableOn_empty
  have hKloc : LocallyIntegrable (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) (volume : Measure (Euc d)) := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Euc d)
    exact (hKi r).mono_set hr
  have hSc : ContDiff ℝ ⊤ (r26t8a_sh_S (E := Euc d) (1 / 2)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (r26t8a_sh_S (E := Euc d) (1 / 2))
  have hS' : ContDiff ℝ (n : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => src (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.2)) :=
    hsrc.comp (hSc.of_le le_top)
  have hvan : ∀ (Y : Euc d), ∀ x : Euc d, Y ∈ (Set.univ : Set (Euc d)) → x ∉ closedBall (0 : Euc d) 2 →
      (fun Y x => src (Y + (1 / 2 : ℝ) • x, x)) Y x = 0 := by
    intro Y x _ hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hSv _ x hx
  have hconv := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (n := (n : ℕ∞)) (ContinuousLinearMap.mul ℝ ℝ) (f := fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ)))
    (g := fun Y x : Euc d => src (Y + (1 / 2 : ℝ) • x, x)) (s := Set.univ)
    (k := closedBall (0 : Euc d) 2) isOpen_univ (isCompact_closedBall _ _) hvan hKloc
    (by
      have : ContDiff ℝ (n : ℕ∞) (Function.uncurry fun Y x : Euc d => src (Y + (1 / 2 : ℝ) • x, x)) :=
        by exact_mod_cast hS'
      exact this.contDiffOn)
  have hcd : ContDiff ℝ (n : ℕ∞)
      (fun q : Euc d × Euc d => ((fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun x : Euc d => src (q.1 + (1 / 2 : ℝ) • x, x))) q.2) := by
    rw [← contDiffOn_univ]
    simpa using hconv
  have heq : (fun Yw : Euc d × Euc d => r26t8a_Wg alpha src Yw.1 Yw.2) =
      fun q : Euc d × Euc d => ((fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun x : Euc d => src (q.1 + (1 / 2 : ℝ) • x, x))) q.2 := by
    funext q
    rw [r26t8a_Wg_conv, convolution_def]
    rfl
  rw [heq]
  exact_mod_cast hcd

end HRS.MS.R26T8A
