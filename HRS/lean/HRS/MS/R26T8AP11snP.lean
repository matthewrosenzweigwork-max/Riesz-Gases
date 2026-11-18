import HRS.MS.R26T8AP11sn
import HRS.MS.R26T8AP11mjP

/-!
# S8.2 nonlocal layer: nested jets of the un-cut-off local Riesz integral for the PURE conormal class (any sign of the order)
Copies of the `Conormal`/`0 <= sigma` versions with `ConormalP` (see `R26T8AP01p`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_Sfun_nestP (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → ConormalP k b M sigma A F →
      ∀ X z : Euc d, z ≠ 0 → ‖z‖ < 2 → ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ ≤
          C * A * jbracket X ^ (2 * M) *
            (1 + ‖z‖ ^ (alpha - sigma - q) * (1 + |Real.log ‖z‖|) ^ (b + 1)) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_loc_sum_nestP d hd k b alpha M sigma halpha had hM hsd chi hchi
  refine ⟨C, hC0, ?_⟩
  intro F A hA hF X z hz0 hz2 p q hpq
  obtain ⟨r, hr0, hr1, Φ, hΦ0, hΦ, hΦb⟩ :=
    r26t8a_loc_majorantP d hd k b alpha M sigma halpha had hM hsd chi hchi F A hA hF X z hz0 hz2
  have hFc : ContDiffOn ℝ (p + q : ℕ) (Function.uncurry F) {p | p.1 ≠ p.2} :=
    hF.1.of_le (by exact_mod_cast hpq)
  have hsum : ∀ Y w : Euc d, w ≠ 0 → r26t8a_Sfun alpha chi F Y w =
      ∑' n : ℕ, r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Y w := fun Y w hw =>
    (r26t8a_loc_partition d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F (hF.toConormal hA) Y w hw).tsum_eq.symm
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
