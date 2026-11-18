import HRS.MS.R26T8AP01a
import HRS.MS.R26T8AMix

/-!
# S8.2 local Newton layer, packet T8A.P01 (part b): nested Leibniz for the annulus-weighted source
* `r26t8a_nest_product_bound`: scalar product `a (w) G (Y,w)` (nested Leibniz of `R26T8AMix`);
* `r26t8a_gtilde_contDiff`: `psiCut(w) midPair F Y w` is globally `C^k` (the singularity of `F` on the diagonal is cut off);
* `r26t8a_nest_gtilde`: at `|z| >= R/2` its nested jets are the `mixedJet`s of `F`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_nest_product_bound (p q : ℕ) (a : Euc d → ℝ) (G : Euc d × Euc d → ℝ) (X z : Euc d)
    (ha : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) a) (hG : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G) :
    ‖r26t8a_nest p q (fun Yw => a Yw.2 * G Yw) X z‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i a z‖ * ‖r26t8a_nest p (q - i) G X z‖ := by
  have h := r26t8a_nest_bilinear q p (ContinuousLinearMap.mul ℝ ℝ) a G X z ha hG
  have hn : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i a z‖ *
      ‖r26t8a_nest p (q - i) G X z‖ := Finset.sum_nonneg fun i _ => by positivity
  refine le_trans (le_of_eq ?_) (h.trans ((mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.opNorm_mul_le ℝ ℝ) hn).trans (le_of_eq (one_mul _))))
  rfl

theorem r26t8a_midPair_contDiffOn {F : Euc d → Euc d → ℝ} {k : ℕ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) :
    ContDiffOn ℝ k (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) {Yw | Yw.2 ≠ 0} := by
  have hL : ContDiff ℝ k (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) :=
    (contDiff_fst.add (contDiff_snd.const_smul _)).prodMk (contDiff_fst.sub (contDiff_snd.const_smul _))
  refine hF.comp hL.contDiffOn (fun Yw hYw => ?_)
  simp only [Set.mem_setOf_eq] at hYw ⊢
  intro h
  apply hYw
  set u : Euc d := (1 / 2 : ℝ) • Yw.2 with hu
  have h1 : u = -u := add_left_cancel (h.trans (sub_eq_add_neg _ _))
  have h2 : (2 : ℝ) • u = 0 := by
    rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel u
  have h3 : u = 0 := (smul_eq_zero.1 h2).resolve_left (by norm_num)
  exact (smul_eq_zero.1 h3).resolve_left (by norm_num)

theorem r26t8a_gtilde_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} {k : ℕ} (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) :
    ContDiff ℝ k (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hpsi : ContDiff ℝ k (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2) :=
    ((r26t8a_psiCut_contDiff hchi R).of_le (by exact_mod_cast le_top)).comp contDiff_snd
  by_cases hw : x.2 = 0
  · have hev : (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) =ᶠ[𝓝 x]
        fun _ => 0 := by
      have hopen : IsOpen {Yw : Euc d × Euc d | ‖Yw.2‖ < R / 8} :=
        isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
      filter_upwards [hopen.mem_nhds (by simp [hw]; positivity)] with Yw hYw
      rw [r26t8a_psiCut_zero hchi hR (le_of_lt hYw), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hopen : IsOpen {Yw : Euc d × Euc d | Yw.2 ≠ 0} := isOpen_ne.preimage continuous_snd
    exact hpsi.contDiffAt.mul ((r26t8a_midPair_contDiffOn hF).contDiffAt (hopen.mem_nhds hw))

theorem r26t8a_nest_gtilde {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} (p r : ℕ) (X z : Euc d) (hz : R / 4 < ‖z‖) :
    r26t8a_nest p r (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z =
      mixedJet p r F X z := by
  unfold r26t8a_nest mixedJet
  congr 1
  funext Y
  have hev : (fun w : Euc d => r26t8a_psiCut chi R w * midPair F Y w) =ᶠ[𝓝 z] midPair F Y := by
    have hopen : IsOpen {w : Euc d | R / 4 < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds hz] with w hw
    rw [r26t8a_psiCut_one hchi hR (le_of_lt hw), one_mul]
  exact (hev.iteratedFDeriv ℝ r).self_of_nhds

end HRS.MS.R26T8A
