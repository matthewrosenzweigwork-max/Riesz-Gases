import HRS.MS.R26T8AP06d6
import HRS.MS.R26T8AP01b

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 7): continuous extension of the nested jets of `midPair F`
`r26t8a_nest_ext`: if `Conormal (k+1) b M sigma A F` with `k < -sigma`, then for `p + q <= k` the nested jet `nest p q (midPair F)`
(a `Mult^p(E; Mult^q(E; R))`-valued function of `(X,z)`, `z != 0`) has a continuous extension to `E x E`.
Route: `nest_swap` (the nested jet is the `q`-th `z`-jet of `D^p_X midPair F [u]`), P06c (uniform limit jets, rate `|z|^eps`), completeness, `cauchy_ext`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_jbracket_continuous : Continuous (fun x : Euc d => jbracket x) := by
  unfold jbracket
  exact Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))

theorem r26t8a_nest_midPair_eq {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2})
    {p i : ℕ} (hpi : p + i ≤ k + 1) {z0 : Euc d} (hz0 : z0 ≠ 0) (X : Euc d) (u : Fin p → Euc d) :
    iteratedFDeriv ℝ i (fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
      (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z'')) z0 =
        (mixedJet p i F X z0) u := by
  have hn : 0 < ‖z0‖ := norm_pos_iff.2 hz0
  set R : ℝ := 2 * ‖z0‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2 with hΨ
  have hΨd : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Ψ := r26t8a_gtilde_contDiff hchi hRpos hF
  have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.2‖} := isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) =ᶠ[𝓝 (X, z0)] Ψ := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖(X, z0).2‖ by show R / 4 < ‖z0‖; rw [hR]; linarith)] with w hw
    simp only [hΨ, r26t8a_psiCut_one hchi hRpos (le_of_lt hw), one_mul]
  have hev2 := r26t8a_iterDir_nhds hev ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
  have hev3 : (fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
      (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z'')) =ᶠ[𝓝 z0]
      (fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) Ψ (X, z'')) :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually hev2
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [(hev3.iteratedFDeriv ℝ i).self_of_nhds]
  have hΨ' : ContDiff ℝ ((p + i : ℕ) : WithTop ℕ∞) Ψ := hΨd.of_le (by exact_mod_cast hpi)
  rw [← r26t8a_nest_swap p i hΨ' X z0 u v, r26t8a_nest_gtilde hchi hRpos p i X z0 (by rw [hR]; linarith)]

theorem r26t8a_contDiffAt_h {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2})
    {p : ℕ} (hp : p ≤ k) {z0 : Euc d} (hz0 : z0 ≠ 0) (X : Euc d) (u : Fin p → Euc d) :
    ContDiffAt ℝ (((k - p) + 1 : ℕ) : WithTop ℕ∞)
      (fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
        (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z'')) z0 := by
  have hn : 0 < ‖z0‖ := norm_pos_iff.2 hz0
  set R : ℝ := 2 * ‖z0‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2 with hΨ
  have hΨd : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Ψ := r26t8a_gtilde_contDiff hchi hRpos hF
  have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.2‖} := isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) =ᶠ[𝓝 (X, z0)] Ψ := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖(X, z0).2‖ by show R / 4 < ‖z0‖; rw [hR]; linarith)] with w hw
    simp only [hΨ, r26t8a_psiCut_one hchi hRpos (le_of_lt hw), one_mul]
  have hev2 := r26t8a_iterDir_nhds hev ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
  have hev3 : (fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
      (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z'')) =ᶠ[𝓝 z0]
      (fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) Ψ (X, z'')) :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually hev2
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev3
  have h1 : ContDiff ℝ ((((k - p) + 1 : ℕ) : WithTop ℕ∞)) (r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) Ψ) :=
    r26t8a_iterDir_contDiff _ _ Ψ (by
      refine hΨd.of_le ?_
      simp only [List.length_map, List.length_ofFn]
      exact_mod_cast (by omega : (k - p) + 1 + p ≤ k + 1))
  exact (h1.comp (contDiff_const.prodMk contDiff_id)).contDiffAt

end HRS.MS.R26T8A
