import HRS.MS.SA16Y3EnD13
import HRS.MS.SA16RDuh1

/-!
# S.A.16 (SA16Y3) M1: truncated mild solution with an energy bound free of the zeroth-order size of the drift

`sa16y3_mild_energy`: for a family `K_r = B_{b_r} - T1_r ι` (`b_r` smooth, `SA16BddCoef (m+1) B' (b_r)` with an arbitrary
constant `B'`, e.g. the truncated drift `χ_R b_r` with `B' = B'(R)`; the derivative constant `B` is `SA16DerCoef`),
bounded (`hKb`, qualitative) and strongly continuous (`hKc`), the mild solution `u ∈ C([0,T]; W^{m+2,p})` of
`sa16r_fixedn_mild` exists and
`jetEnergy_m(ι² u τ) ≤ jetEnergy_m(ι² φ) exp((p cTr(B) + p C_J CG) τ)`
with `C_J = sa16y3_CJ d m p` depending on `d, m, p` only.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section M1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_mild_energy {m : ℕ} {ν T B B' Bk CG : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16DerCoef (m + 1) B (bc r))
    (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ r ∈ Icc (0 : ℝ) T, (sa16r_iota d m p).comp (T1 r) = (T0 r).comp (sa16r_iota d m p))
    (hT0 : ∀ r ∈ Icc (0 : ℝ) T, ‖T0 r‖ ≤ CG)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - (T1 r).comp (sa16r_iota d (m + 1) p))
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk) (hBk : 0 ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p) :
    ∃ u : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn u (Icc 0 T) ∧
      (∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
        voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ) ∧
      ∀ τ ∈ Icc (0 : ℝ) T,
        jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
          jetEnergy d m p (sa16sz_iota2 d m p φ) *
            Real.exp ((p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) * τ) := by
  obtain ⟨u, hu, hsol, -⟩ := sa16r_fixedn_mild (p := p) hν hT hBk (m + 1) K hKb hKc φ
  exact ⟨u, hu, hsol, sa16y3_energy_solutionD hν hT bc hbc hbo T1 T0 hcomp hT0 K hK hKb hBk hKc φ hu hsol⟩

end M1

end HRS.Whole.AppendixA.Phase2SA16R
