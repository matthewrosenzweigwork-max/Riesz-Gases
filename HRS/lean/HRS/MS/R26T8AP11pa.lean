import HRS.MS.R26T8AP11s

/-!
# S8.2 nonlocal layer: smoothness of the far-from-zero part of the local Riesz integral (P11e, part 3b, piece A)
`r26t8a_loc_partA`: for `psi(v) = chi(v/delta)` (`= 1` on `|v| <= delta`) the integral
`I_A(x,y) = int ‖x-y-v‖^(alpha-d) chi(v) (1 - psi(v)) F(y+v,y) dv` is `C^n` on all of `E × E`
(a parametrised convolution of the locally integrable kernel with a `C^n` compactly supported source).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_loc_partA (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ) {n : ℕ}
    (hF : ContDiffOn ℝ n (Function.uncurry F) {p | p.1 ≠ p.2}) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun xy : Euc d × Euc d => ∫ v : Euc d, ‖xy.1 - xy.2 - v‖ ^ (alpha - (d : ℝ)) *
      (chi v * (1 - chi (δ⁻¹ • v)) * F (xy.2 + v) xy.2)) := by
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
  set SA : Euc d × Euc d → ℝ := fun ys => chi ys.2 * (1 - chi (δ⁻¹ • ys.2)) * F (ys.1 + ys.2) ys.1 with hSA
  -- smoothness of the source
  have hSAc : ContDiff ℝ (n : WithTop ℕ∞) SA := by
    rw [contDiff_iff_contDiffAt]
    intro ys
    by_cases hs : ‖ys.2‖ < δ
    · have hev : SA =ᶠ[𝓝 ys] fun _ => 0 := by
        have hopen : IsOpen {p : Euc d × Euc d | ‖p.2‖ < δ} :=
          isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
        filter_upwards [hopen.mem_nhds hs] with p hp
        have : 1 - chi (δ⁻¹ • p.2) = 0 := by
          have h1 : ‖δ⁻¹ • p.2‖ ≤ 1 := by
            rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hδ]
            have hp' : ‖p.2‖ < δ := hp
            linarith
          rw [hchi.2.2.2.1 _ h1]; ring
        simp only [hSA, this, mul_zero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · push Not at hs
      have hne : ys.2 ≠ 0 := by
        intro h; rw [h, norm_zero] at hs; linarith
      have hchic : ContDiff ℝ (n : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
      have h1 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun p : Euc d × Euc d => chi p.2) ys :=
        (hchic.comp contDiff_snd).contDiffAt
      have h2 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun p : Euc d × Euc d => 1 - chi (δ⁻¹ • p.2)) ys :=
        (contDiff_const.sub (hchic.comp ((contDiff_const_smul δ⁻¹).comp contDiff_snd))).contDiffAt
      have hlin : ContDiff ℝ (n : WithTop ℕ∞) (fun p : Euc d × Euc d => (p.1 + p.2, p.1)) :=
        (contDiff_fst.add contDiff_snd).prodMk contDiff_fst
      have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
      have hmem : (ys.1 + ys.2, ys.1) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
        show ys.1 + ys.2 ≠ ys.1
        intro h; apply hne; simpa using h
      have h3 : ContDiffAt ℝ (n : WithTop ℕ∞) (fun p : Euc d × Euc d => F (p.1 + p.2) p.1) ys :=
        ContDiffAt.comp (g := Function.uncurry F) ys (hF.contDiffAt (hopen.mem_nhds hmem)) hlin.contDiffAt
      exact (h1.mul h2).mul h3
  have hvan : ∀ (p : Euc d × Euc d), ∀ s : Euc d, p ∈ (Set.univ : Set (Euc d × Euc d)) →
      s ∉ closedBall (0 : Euc d) 2 → (fun (p : Euc d × Euc d) (s : Euc d) => SA (p.2, s)) p s = 0 := by
    intro p s _ hs
    rw [mem_closedBall, dist_zero_right, not_le] at hs
    simp only [hSA, hchi.2.2.2.2 s hs.le, zero_mul]
  have hv : ContDiffOn ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun p : Euc d × Euc d => p.1 - p.2) Set.univ :=
    (contDiff_fst.sub contDiff_snd).contDiffOn
  have hconv := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (n := (n : ℕ∞)) (ContinuousLinearMap.mul ℝ ℝ) (s := (Set.univ : Set (Euc d × Euc d)))
    (v := fun p : Euc d × Euc d => p.1 - p.2) (f := fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ)))
    (g := fun (p : Euc d × Euc d) (s : Euc d) => SA (p.2, s)) (k := closedBall (0 : Euc d) 2)
    hv isOpen_univ
    (isCompact_closedBall _ _) hvan hKloc
    (by
      have : ContDiff ℝ (n : ℕ∞) (Function.uncurry fun (p : Euc d × Euc d) (s : Euc d) => SA (p.2, s)) := by
        have h := hSAc.comp (contDiff_snd.comp contDiff_fst |>.prodMk contDiff_snd :
          ContDiff ℝ (n : WithTop ℕ∞) fun q : (Euc d × Euc d) × Euc d => (q.1.2, q.2))
        exact_mod_cast h
      exact this.contDiffOn)
  have hcd : ContDiff ℝ (n : ℕ∞) (fun p : Euc d × Euc d =>
      ((fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun s : Euc d => SA (p.2, s))) (p.1 - p.2)) := by
    rw [← contDiffOn_univ]; exact hconv
  have heq : (fun xy : Euc d × Euc d => ∫ v : Euc d, ‖xy.1 - xy.2 - v‖ ^ (alpha - (d : ℝ)) *
      (chi v * (1 - chi (δ⁻¹ • v)) * F (xy.2 + v) xy.2)) =
      fun p : Euc d × Euc d => ((fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun s : Euc d => SA (p.2, s))) (p.1 - p.2) := by
    funext p
    rw [convolution_def]
    rw [← integral_sub_left_eq_self (fun u : Euc d => (ContinuousLinearMap.mul ℝ ℝ) (‖u‖ ^ (alpha - (d : ℝ)))
      (SA (p.2, p.1 - p.2 - u))) volume (p.1 - p.2)]
    congr 1
    funext v
    simp only [sub_sub_cancel, ContinuousLinearMap.mul_apply', hSA]
  rw [heq]
  exact_mod_cast hcd

end HRS.MS.R26T8A
