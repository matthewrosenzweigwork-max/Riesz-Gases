import HRS.MS.MfeConfAux122

/-!
# S.B.1 (SB5), R1 (part 0): the statement of the vanishing-remainder hypothesis `hB`

`Sb1HBAll d` is the statement that the remainder `B^M` of the level-`M` source is `η_M`-small against the envelope
`P_M + ℓ` (the hypothesis `hB` of `sb1_bdd_entropy`), for all data of `Sb1Tr3` and every transport bound `Kf`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

/-- the vanishing remainder `SM`: `|B^M_r(Z)| ≤ η_M (1 + K(r)) (A₃ (P_M(Z) + ℓ(Z)) + A₄)` with `η_M → 0` -/
def Sb1HBAll (d : ℕ) : Prop :=
  ∀ (D : Whole.WholeDyn d) {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (_H : Sb1Tr3 D T C B C3 ρ) (hT : 0 < T) (N : ℕ),
    1 ≤ N → 0 < D.invβ → ∀ Kf : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t)) →
    ∃ (η : ℕ → ℝ) (A3 A4 : ℝ), Tendsto η atTop (𝓝 0) ∧ (∀ M, 0 ≤ η M) ∧ 0 < A3 ∧ 0 ≤ A4 ∧
      ∀ (M : ℕ), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N,
        |sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r Z| ≤ η M * (1 + Kf r) *
          (A3 * (sb1PM (sb1kM d D.s M) N Z + sb1ell d N Z) + A4)

end HRS.MS.MfeConf
