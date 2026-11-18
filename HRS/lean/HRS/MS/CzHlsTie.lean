import HRS.MS.CzHlsAux2

/-!
# HLS-GLUE tie: the `0 < θ < 1` conjunct of the frozen `lp_screened_negative_order`

`HRS.CZ.Hls.lp_screened_negative_order_lt_one` (`HRS/MS/CzHlsAux2.lean`) proves exactly the first conjunct of
`HRS.Whole.AppendixA.lp_screened_negative_order` (`AppendixAAdjoint.lean:897`), under weaker hypotheses (`1 < p`
instead of `2 ≤ p`, `Continuous Ω` instead of `IsOddSmooth Ω`).  The theorem below states this first conjunct with the
frozen hypotheses and conclusion verbatim.
-/

open MeasureTheory
open HRS.Whole.AppendixA

namespace HRS.CZ.Hls

theorem lp_screened_negative_order_first_conjunct {d : ℕ} (hd : 1 ≤ d) (θ p : ℝ) (hp : 2 ≤ p)
    (Ω : Euc d → ℝ) (hΩ : IsOddSmooth Ω) :
    (0 < θ → θ < 1 → 1 / p + (1 - θ) / d < 1 →
      ∃ C : ℝ, ∀ a W : Euc d → ℝ, MemLp a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume →
        MemLp W (ENNReal.ofReal p) volume →
        eLpNorm (pvOdd d θ Ω fun x => a x * W x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * eLpNorm a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume *
            eLpNorm W (ENNReal.ofReal p) volume) :=
  fun hθ0 hθ1 hq =>
    lp_screened_negative_order_lt_one hd θ p Ω hΩ.1.continuous hθ0 hθ1 (by linarith) hq

end HRS.CZ.Hls
