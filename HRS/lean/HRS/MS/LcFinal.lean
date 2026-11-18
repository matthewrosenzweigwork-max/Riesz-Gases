import HRS.MS.LcFinalAux1
import HRS.MS.LcKolmAux2
import HRS.MS.LcUniqAux2
import HRS.MS.LcEngAux3
import HRS.MS.LcWtAux4
import HRS.MS.LcFlowAux2
import HRS.Stochastic.Wiener
import HRS.Whole.Adjoint

/-!
# LC-F: assembly of `HRS.Whole.local_decay` (supplement S4.11)

`local_decay_proof : type_of% @HRS.Whole.local_decay` (the frozen statement, with `hk : 2 ≤ k`).

Proof.  The constant `C` is the one of `lc_engine` (quantified before `ν, c, B`).  Data given on
`[0,T]` only are clamped to `c (min · T)`, `B (min · T)` (`lcHyp_clamp`, `lcDecay_clamp`), which agree
with the original data on `[0,T]`.  On a probability space with a Brownian filtration
(`exists_isBrownianFiltration_type`):
* existence: `lc_backward` for the clamped data and `f ∈ C^2` with bounded derivatives of order `≤ 2`
  (from `decayNormE k b f < ⊤`, `k ≥ 2`, `lcf_bdd_iteratedFDeriv`), transported to the original drift by
  `lcf_solution_congr` (a local backward solution only sees the drift on `[0,t]`);
* every solution `u` equals `lcSg · t f` on `[0,t]` by `lc_unique` (`‖c‖ ≤ Λc`, `‖B‖ ≤ ΛB` on `[0,t]`);
* the `C^k` regularity and the bound `decayNormE k b (u r) ≤ ofReal C * decayNormE k b f` are those of
  `lc_engine` for `lcSg`.
No statement adjustment is made.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.Lc

/-- **S4.11 `local_decay`**: proof (tie in `LcFinalTie`). -/
theorem local_decay_proof : type_of% @HRS.Whole.local_decay := by
  intro d hd s hs Q k hk T νstar bexp Λc ΛB hb
  obtain ⟨C, hC⟩ := lc_engine.{0} s hs Q k T νstar bexp Λc ΛB hb
  refine ⟨C, fun ν c B hνc hν hc hB hcb hBs t ht f hf hfd => ?_⟩
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  haveI := hP
  set c' : ℝ → Euc d := fun v => c (min v T) with hc'
  set B' : ℝ → Euc d → Euc d := fun v => B (min v T) with hB'
  have hH : LcHyp Q k Λc ΛB c' B' :=
    lcHyp_clamp hT0 hc hB hcb fun v hv =>
      ⟨by exact_mod_cast (hBs v hv).1, fun j hj x => (hBs v hv).2.1 j hj x⟩
  have hH2 : LcHyp Q 2 Λc ΛB c' B' :=
    lcHyp_clamp hT0 hc hB hcb fun v hv =>
      ⟨(hBs v hv).1.of_le (by exact_mod_cast (by omega : 2 + 1 ≤ k + 1)),
        fun j hj x => (hBs v hv).2.1 j (by omega) x⟩
  have hdec := lcDecay_clamp hT0 (fun v hv => (hBs v hv).2.2)
  -- the data
  have hfk : ContDiff ℝ (k : WithTop ℕ∞) f := by
    have : max k 2 = k := Nat.max_eq_left hk
    rw [this] at hf
    exact hf
  have hf2 : ContDiff ℝ 2 f := hfk.of_le (by exact_mod_cast hk)
  obtain ⟨M0, hM0⟩ := lcf_bdd_iteratedFDeriv hb.le hfd (Nat.zero_le k)
  obtain ⟨M1, hM1⟩ := lcf_bdd_iteratedFDeriv hb.le hfd (by omega : 1 ≤ k)
  obtain ⟨M2, hM2⟩ := lcf_bdd_iteratedFDeriv hb.le hfd hk
  have hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ max (max M0 M1) M2 := by
    intro i hi y
    interval_cases i
    · exact (hM0 y).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hM1 y).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hM2 y).trans (le_max_right _ _)
  have hν0 : ∀ r, 0 ≤ ν r := fun r => (hν r).1
  have hνs : ∀ r, ν r ≤ νstar := fun r => (hν r).2
  -- the drift agrees on `[0,t]`
  have hdr : ∀ r ∈ Icc 0 t, ∀ x : Euc d,
      -(Torus.matVec Q x) - c' r + B' r x = -(Torus.matVec Q x) - c r + B r x := by
    intro r hr x
    have : min r T = r := min_eq_left (hr.2.trans ht.2)
    simp only [hc', hB', this]
  have hsol : IsLocalBackwardSolution ν (fun r x => -(Torus.matVec Q x) - c r + B r x) t f
      (fun r => lcSg P W ν Q c' B' r t f) :=
    lcf_solution_congr hdr (lc_backward hW hνc hν0 hνs hH2 ht.1 hf2 hM)
  refine ⟨⟨_, hsol⟩, fun u hu r hr => ?_⟩
  have hBn : ∀ r ∈ Icc 0 t, ∀ x, ‖B r x‖ ≤ ΛB := by
    intro r hr x
    have := (hBs r ⟨hr.1, hr.2.trans ht.2⟩).2.1 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have huq := lc_unique ht.1 (fun r _ => hν r) (fun r hr => hcb r ⟨hr.1, hr.2.trans ht.2⟩) hBn
    hu hsol
  have hueq : u r = lcSg P W ν Q c' B' r t f := funext fun x => huq r hr x
  rw [hueq]
  exact hC P ℱ W ν c' B' hW hνc hν hH hdec r t hr.1 hr.2 ht.2 f hfk hfd

end HRS.MS.Lc
