import HRS.MS.R26T8AP07o
import HRS.MS.R26T8AP07k
import HRS.MS.R26T8ATsum

/-!
# S8.2 local Newton layer, packet T8A.P07 (part p): nested jets of the series `N = sum_n annularNewton (1/2)^n`
`r26t8a_p07_N_nest` (`0 <= sigma < d`, `0 < |z| <= 3`, `p + q <= k`):
`‖nest p q (Y,w |-> sum_n annularNewton (1/2)^n F Y w) X z‖ <= C A <X>^(2M) (1 + |z|^(2-sigma-q) (1+|log|z||)^(b+1))`,
from `r26t8a_nest_tsum`, the local majorant `r26t8a_p07_majorant` and the dyadic sum `r26t8a_p07_series_bound`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_N_nest (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, ConormalP k b M σ A F →
      ∀ X z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 3 → ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d =>
          ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) X z‖ ≤
          C * A * jbracket X ^ (2 * M) * (1 + ‖z‖ ^ (2 - σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ (b + 1)) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_series_bound hd k b nu M σ hnu hM hσd hchi
  refine ⟨C, hC0, fun A hA F hF X z hz hz3 p q hpq => ?_⟩
  obtain ⟨r, hr0, -, -, Φ, hΦ0, hΦ, hΦb⟩ := r26t8a_p07_majorant hd k b nu M σ hnu hM hσd hchi A hA F hF X z hz hz3
  have hV : ∀ n : ℕ, ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d =>
      r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) := fun n =>
    r26t8a_p07_T_contDiff hd nu hchi (by positivity) (hF.1.of_le (by exact_mod_cast hpq))
  have hnt := r26t8a_nest_tsum (d := d) p q (fun n Yw => r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2)
    hV X z hr0 Φ hΦ0 hΦ (fun n i hi j hj Y hY w hw => hΦb n i j (by omega) Y hY w hw)
  refine hnt.trans ?_
  have := (hC A hA F hF p q hpq X z hz (by linarith)).2
  exact this

end HRS.MS.R26T8A
