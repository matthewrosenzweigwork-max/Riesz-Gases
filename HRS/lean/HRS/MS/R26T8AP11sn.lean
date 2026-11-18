import HRS.MS.R26T8AP11mj
import HRS.MS.R26T8AP11pv
import HRS.MS.R26T8ATsum

/-!
# S8.2 nonlocal layer: nested jets of the full (un-cut-off) local Riesz integral (P11e, part 3a/4)
`r26t8a_Sfun Y w = ∫ ‖w-v‖^(alpha-d) chi(v) F(Y - w/2 + v, Y - w/2) dv` is the sum of the annular pieces for `w ≠ 0`
(`r26t8a_loc_partition`).  `r26t8a_Sfun_nest`: `‖nest p q Sfun X z‖ <= C A jb(X)^(2M) (1 + |z|^(alpha-sigma-q) (1+|log|z||)^(b+1))`
for `0 < |z| < 2`, `p + q <= k`, by `r26t8a_nest_tsum`, the majorant `r26t8a_loc_majorant` and the dyadic sum `r26t8a_loc_sum_nest`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

/-- The local Riesz integral in centre/relative coordinates, without the outer cutoff. -/
def r26t8a_Sfun {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (Y w : Euc d) : ℝ :=
  ∫ v : Euc d, ‖w - v‖ ^ (alpha - (d : ℝ)) *
    (chi v * F (Y + (-(1 / 2 : ℝ)) • w + v) (Y + (-(1 / 2 : ℝ)) • w))

theorem r26t8a_nest_congr {d : ℕ} (p q : ℕ) (Φ Φ' : Euc d × Euc d → ℝ)
    (hΦ : ∀ Y w : Euc d, w ≠ 0 → Φ (Y, w) = Φ' (Y, w)) (X z : Euc d) (hz : z ≠ 0) :
    r26t8a_nest p q Φ X z = r26t8a_nest p q Φ' X z := by
  unfold r26t8a_nest
  have h : ∀ Y : Euc d, iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z = iteratedFDeriv ℝ q (fun w => Φ' (Y, w)) z := by
    intro Y
    have hopen : IsOpen {w : Euc d | w ≠ 0} := isOpen_ne
    have hev : (fun w => Φ (Y, w)) =ᶠ[𝓝 z] fun w => Φ' (Y, w) := by
      filter_upwards [hopen.mem_nhds hz] with w hw using hΦ Y w hw
    exact (hev.iteratedFDeriv ℝ q).self_of_nhds
  simp only [h]

theorem r26t8a_locV_contDiff (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) (F : Euc d → Euc d → ℝ) {n : ℕ}
    (hF : ContDiffOn ℝ n (Function.uncurry F) {p | p.1 ≠ p.2}) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi R F Yw.1 Yw.2) := by
  have h := r26t8a_locW_contDiff d hd alpha halpha had chi hchi hR F hF
  exact h.comp ((contDiff_fst.add (contDiff_snd.const_smul (-(1 / 2 : ℝ)))).prodMk contDiff_snd)

theorem r26t8a_Sfun_nest (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal k b M sigma A F →
      ∀ X z : Euc d, z ≠ 0 → ‖z‖ < 2 → ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ ≤
          C * A * jbracket X ^ (2 * M) *
            (1 + ‖z‖ ^ (alpha - sigma - q) * (1 + |Real.log ‖z‖|) ^ (b + 1)) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_loc_sum_nest d hd k b alpha M sigma halpha had hM hsigma hsd chi hchi
  refine ⟨C, hC0, ?_⟩
  intro F A hA hF X z hz0 hz2 p q hpq
  obtain ⟨r, hr0, hr1, Φ, hΦ0, hΦ, hΦb⟩ :=
    r26t8a_loc_majorant d hd k b alpha M sigma halpha had hM hsigma hsd chi hchi F A hA hF X z hz0 hz2
  have hFc : ContDiffOn ℝ (p + q : ℕ) (Function.uncurry F) {p | p.1 ≠ p.2} :=
    hF.1.of_le (by exact_mod_cast hpq)
  have hsum : ∀ Y w : Euc d, w ≠ 0 → r26t8a_Sfun alpha chi F Y w =
      ∑' n : ℕ, r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Y w := fun Y w hw =>
    (r26t8a_loc_partition d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F hF Y w hw).tsum_eq.symm
  rw [r26t8a_nest_congr p q _ (fun Yw : Euc d × Euc d => ∑' n : ℕ,
    r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Yw.1 Yw.2) (fun Y w hw => hsum Y w hw) X z hz0]
  have hnt := r26t8a_nest_tsum (d := d) p q
    (fun n Yw => r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Yw.1 Yw.2)
    (fun n => r26t8a_locV_contDiff d hd alpha halpha had chi hchi (by positivity) F hFc) X z hr0 Φ hΦ0 hΦ
    (fun n i hi j hj Y hY w hw => hΦb n i j (by omega) Y hY w hw)
  refine hnt.trans ?_
  refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun N => ?_
  exact hC F A hA hF X z hz0 hz2.le p q hpq N

end HRS.MS.R26T8A
