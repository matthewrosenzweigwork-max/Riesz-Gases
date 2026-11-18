import HRS.MS.R26T8AP11f8
import HRS.MS.R26T8AP11a3

/-!
# S8.2 T8A P15c: centre and relative directional derivatives of a pair function
`r26t8a_pdir u F x y = D(midPair F)(X, z) u` with `(X, z) = ((x+y)/2, x-y)`.  `midPair (pdir u F) = D(midPair F) u` exactly.
* `Conormal (k+1) b M σ A F → Conormal k b M σ A (pdir (v,0) F)` (centre derivative costs no pole), `‖v‖ ≤ 1`;
* `Conormal (k+1) b M σ A F → Conormal k b M (σ+1) A (pdir (0,v) F)` (relative derivative costs one), `‖v‖ ≤ 1`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- Directional derivative of `midPair F` in centre/relative coordinates, as a pair function. -/
def r26t8a_pdir (u : Euc d × Euc d) (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  fderiv ℝ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) ((1 / 2 : ℝ) • (x + y), x - y) u

theorem r26t8a_pdir_arg (Y w : Euc d) :
    ((1 / 2 : ℝ) • ((Y + (1 / 2 : ℝ) • w) + (Y - (1 / 2 : ℝ) • w)), (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w)) =
      (Y, w) := by
  exact Prod.ext (by module) (by module)

theorem r26t8a_midPair_pdir (u : Euc d × Euc d) (F : Euc d → Euc d → ℝ) (Y w : Euc d) :
    midPair (r26t8a_pdir u F) Y w = fderiv ℝ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (Y, w) u := by
  show r26t8a_pdir u F (Y + (1 / 2 : ℝ) • w) (Y - (1 / 2 : ℝ) • w) = _
  unfold r26t8a_pdir
  rw [r26t8a_pdir_arg]

theorem r26t8a_pdir_contDiffOn {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2}) (u : Euc d × Euc d) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry (r26t8a_pdir u F)) {p | p.1 ≠ p.2} := by
  have hopen : IsOpen {Yw : Euc d × Euc d | Yw.2 ≠ 0} := isOpen_ne.preimage continuous_snd
  have hG : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) {Yw | Yw.2 ≠ 0} :=
    r26t8a_midPair_contDiffOn hF
  have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (fderiv ℝ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2))
      {Yw | Yw.2 ≠ 0} := hG.fderiv_of_isOpen hopen (by push_cast; exact le_rfl)
  have h2 := h1.clm_apply (contDiffOn_const (c := u))
  have hL : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2)) :=
    ((contDiff_fst.add contDiff_snd).const_smul (1 / 2 : ℝ)).prodMk (contDiff_fst.sub contDiff_snd)
  refine (h2.comp hL.contDiffOn (fun p hp => ?_))
  simpa [sub_eq_zero] using hp

/-- The jet identity: with `Ψ = psiCut * midPair F`, near `z ≠ 0`, `D midPair F = D Ψ`. -/
theorem r26t8a_pdir_eq_Psi {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {F : Euc d → Euc d → ℝ} (u : Euc d × Euc d)
    {z : Euc d} (hz : z ≠ 0) (Y w : Euc d) (hw : ‖w - z‖ < ‖z‖ / 2) :
    midPair (r26t8a_pdir u F) Y w =
      fderiv ℝ (fun Yw : Euc d × Euc d => r26t8a_psiCut chi (2 * ‖z‖) Yw.2 * midPair F Yw.1 Yw.2) (Y, w) u := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hR : 0 < 2 * ‖z‖ := by positivity
  rw [r26t8a_midPair_pdir]
  have hwn : ‖z‖ / 2 < ‖w‖ := by
    have := norm_sub_norm_le z w
    rw [norm_sub_rev] at this; linarith
  have hopen : IsOpen {Yw : Euc d × Euc d | ‖z‖ / 2 < ‖Yw.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) =ᶠ[𝓝 (Y, w)]
      fun Yw => r26t8a_psiCut chi (2 * ‖z‖) Yw.2 * midPair F Yw.1 Yw.2 := by
    filter_upwards [hopen.mem_nhds hwn] with Yw hYw
    have hYw' : ‖z‖ / 2 < ‖Yw.2‖ := hYw
    rw [r26t8a_psiCut_one hchi hR (by linarith), one_mul]
  rw [hev.fderiv_eq]

set_option maxHeartbeats 1600000 in
theorem r26t8a_pdir_jet_X {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2}) (v : Euc d) (hv : ‖v‖ ≤ 1)
    (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) (hz : z ≠ 0) :
    ‖mixedJet p q (r26t8a_pdir (v, 0) F) X z‖ ≤ ‖mixedJet (p + 1) q F X z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hR : 0 < 2 * ‖z‖ := by positivity
  have hl : 2 * ‖z‖ / 4 < ‖z‖ := by linarith
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi (2 * ‖z‖) Yw.2 * midPair F Yw.1 Yw.2 with hΨdef
  have hΨ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Ψ := r26t8a_gtilde_contDiff hchi hR hF
  have hΨ' : ContDiff ℝ ((p + q + 1 : ℕ) : WithTop ℕ∞) Ψ :=
    hΨ.of_le (by exact_mod_cast (by omega : p + q + 1 ≤ k + 1))
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hmj : mixedJet p q (r26t8a_pdir (v, 0) F) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_pdir (v, 0) F) Yw.1 Yw.2) X z := rfl
  have hcong : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_pdir (v, 0) F) Yw.1 Yw.2) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => fderiv ℝ Ψ Yw (v, 0)) X z :=
    r26t8a_nest_congr_ball p q _ _ (ρ := ‖z‖ / 2) (by positivity) X z
      (fun Y w hw => r26t8a_pdir_eq_Psi hchi (F := F) (v, 0) hz Y w hw)
  have hsplit : (fun Yw : Euc d × Euc d => fderiv ℝ Ψ Yw (v, 0)) =
      fun Yw => (ContinuousLinearMap.apply ℝ ℝ v) (r26t8a_dY Ψ Yw) := by
    funext Yw
    simp [r26t8a_dY]
  have hC1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dY Ψ) := r26t8a_p06b_dY_contDiff hΨ'
  have hLn : ∀ T : Euc d →L[ℝ] ℝ, ‖(ContinuousLinearMap.apply ℝ ℝ v) T‖ ≤ ‖T‖ := fun T => by
    show ‖T v‖ ≤ ‖T‖
    calc ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = ‖T‖ := mul_one _
  have t1 := r26t8a_nest_clm' (ContinuousLinearMap.apply ℝ ℝ v) hLn p q (r26t8a_dY Ψ) X z hC1
  have t1' := r26t8a_nest_dY_le q p Ψ X z hΨ'
  have g1 : r26t8a_nest (p + 1) q Ψ X z = mixedJet (p + 1) q F X z :=
    r26t8a_nest_gtilde hchi hR (F := F) (p + 1) q X z hl
  rw [hmj, hcong, hsplit]
  calc _ ≤ ‖r26t8a_nest p q (r26t8a_dY Ψ) X z‖ := t1
    _ ≤ ‖r26t8a_nest (p + 1) q Ψ X z‖ := t1'
    _ = _ := by rw [g1]

set_option maxHeartbeats 1600000 in
theorem r26t8a_pdir_jet_Z {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p | p.1 ≠ p.2}) (v : Euc d) (hv : ‖v‖ ≤ 1)
    (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) (hz : z ≠ 0) :
    ‖mixedJet p q (r26t8a_pdir (0, v) F) X z‖ ≤ ‖mixedJet p (q + 1) F X z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hR : 0 < 2 * ‖z‖ := by positivity
  have hl : 2 * ‖z‖ / 4 < ‖z‖ := by linarith
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi (2 * ‖z‖) Yw.2 * midPair F Yw.1 Yw.2 with hΨdef
  have hΨ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Ψ := r26t8a_gtilde_contDiff hchi hR hF
  have hΨ' : ContDiff ℝ ((p + q + 1 : ℕ) : WithTop ℕ∞) Ψ :=
    hΨ.of_le (by exact_mod_cast (by omega : p + q + 1 ≤ k + 1))
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hmj : mixedJet p q (r26t8a_pdir (0, v) F) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_pdir (0, v) F) Yw.1 Yw.2) X z := rfl
  have hcong : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_pdir (0, v) F) Yw.1 Yw.2) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => fderiv ℝ Ψ Yw (0, v)) X z :=
    r26t8a_nest_congr_ball p q _ _ (ρ := ‖z‖ / 2) (by positivity) X z
      (fun Y w hw => r26t8a_pdir_eq_Psi hchi (F := F) (0, v) hz Y w hw)
  have hsplit : (fun Yw : Euc d × Euc d => fderiv ℝ Ψ Yw (0, v)) =
      fun Yw => (ContinuousLinearMap.apply ℝ ℝ v) (r26t8a_dw Ψ Yw) := by
    funext Yw
    rw [r26t8a_dw_eq hΨd]
    simp
  have hC2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dw Ψ) := r26t8a_dw_contDiff hΨ'
  have hLn : ∀ T : Euc d →L[ℝ] ℝ, ‖(ContinuousLinearMap.apply ℝ ℝ v) T‖ ≤ ‖T‖ := fun T => by
    show ‖T v‖ ≤ ‖T‖
    calc ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = ‖T‖ := mul_one _
  have t2 := r26t8a_nest_clm' (ContinuousLinearMap.apply ℝ ℝ v) hLn p q (r26t8a_dw Ψ) X z hC2
  have t2' := r26t8a_nest_succ p q Ψ X z
  have g2 : r26t8a_nest p (q + 1) Ψ X z = mixedJet p (q + 1) F X z :=
    r26t8a_nest_gtilde hchi hR (F := F) p (q + 1) X z hl
  rw [hmj, hcong, hsplit]
  calc _ ≤ ‖r26t8a_nest p q (r26t8a_dw Ψ) X z‖ := t2
    _ = ‖r26t8a_nest p (q + 1) Ψ X z‖ := t2'.symm
    _ = _ := by rw [g2]

theorem r26t8a_pdir_conormal_X {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A : ℝ} (_hA : 0 ≤ A)
    {F : Euc d → Euc d → ℝ} (hF : Conormal (k + 1) b M σ A F) (v : Euc d) (hv : ‖v‖ ≤ 1) :
    Conormal k b M σ A (r26t8a_pdir (v, 0) F) := by
  refine ⟨r26t8a_pdir_contDiffOn hF.1 _, fun p q hpq X z hz => ?_⟩
  exact (r26t8a_pdir_jet_X hchi hF.1 v hv p q hpq X z hz).trans (hF.2 (p + 1) q (by omega) X z hz)

theorem r26t8a_pdir_conormal_Z {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A : ℝ} (_hA : 0 ≤ A)
    {F : Euc d → Euc d → ℝ} (hF : Conormal (k + 1) b M σ A F) (v : Euc d) (hv : ‖v‖ ≤ 1) :
    Conormal k b M (σ + 1) A (r26t8a_pdir (0, v) F) := by
  refine ⟨r26t8a_pdir_contDiffOn hF.1 _, fun p q hpq X z hz => ?_⟩
  refine (r26t8a_pdir_jet_Z hchi hF.1 v hv p q hpq X z hz).trans ((hF.2 p (q + 1) (by omega) X z hz).trans ?_)
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hexp2 : (min 1 ‖z‖) ^ (-(σ + ((q + 1 : ℕ) : ℝ))) = (min 1 ‖z‖) ^ (-((σ + 1) + (q : ℝ))) := by
    congr 1; push_cast; ring
  rw [hexp2]

end HRS.MS.R26T8A
