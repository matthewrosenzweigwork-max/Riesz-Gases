import HRS.MS.SA16Y11Fr1

/-!
# S.A.16 (SA16Y11) Fr2: the fractional-order operator `sa16y5f_Gop` is Lipschitz in the density (sharp, order `m+2` only)

`sa16y11f_Gop_diff`: for smooth `a1, a2` with `C^{m+2}` bound `Wd` (existence) whose difference has `sa16z_Cb (m+2) δ`,
`‖(sa16y5f_Gop a1 - sa16y5f_Gop a2) y‖ ≤ K δ ‖y‖` for `y ∈ W^{m+2,p}`, `K = K(d,m,s,p,MB)`: the operator of the difference density is built from
`sa16y3_extend(A)` (bound linear in `δ`, `sa16y11f_exists`) and identified with `Gop a1 - Gop a2` by linearity of `SA16FOp` and uniqueness.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Fr2
variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem sa16y11f_Gop_diff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    {p : ℝ} [Fact (2 ≤ p)] (m : ℕ) (MB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ},
      (∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
        M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) →
      (∀ i j, |M i j| ≤ MB) → ∀ {a1 a2 : Euc d → ℝ}, ContDiff ℝ ∞ a1 → ContDiff ℝ ∞ a2 →
      ∀ {Wd : ℝ}, 0 ≤ Wd → sa16z_Cb (m + 2) Wd a1 → sa16z_Cb (m + 2) Wd a2 →
      ∀ {δ : ℝ}, 0 ≤ δ → sa16z_Cb (m + 2) δ (fun y => a1 y - a2 y) →
      ∀ y : WmpSpace d (m + 1 + 1) p,
        ‖(sa16y5f_Gop d m p s M a1 - sa16y5f_Gop d m p s M a2) y‖ ≤ K * δ * ‖y‖ := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < s := by linarith
  obtain ⟨K, hK0, hK⟩ := sa16y11f_exists hd hs0 hsd hs1 (p := p) m MB
  refine ⟨K, hK0, fun {M} hMC hM a1 a2 ha1 ha2 Wd hWd hC1 hC2 δ hδ hCd y => ?_⟩
  obtain ⟨T1, hT1, -⟩ := hK hMC hM ha1 hWd hC1
  obtain ⟨T2, hT2, -⟩ := hK hMC hM ha2 hWd hC2
  have hdiff : ContDiff ℝ ∞ (fun y => a1 y - a2 y) := ha1.sub ha2
  obtain ⟨Td, hTd, hTdn⟩ := hK hMC hM hdiff hδ hCd
  have hF : SA16FOp d m p s M (fun y => a1 y - a2 y) (T1 - T2) := by
    have h := sa16y5f_fop_add hd hs hsd M ha1 (contDiff_const.mul ha2) hT1
      (sa16y5f_fop_smul hd hs hsd M (-1) ha2 hT2)
    have e1 : (fun y => a1 y + (-1 : ℝ) * a2 y) = fun y => a1 y - a2 y := by funext y; ring
    have e2 : T1 + (-1 : ℝ) • T2 = T1 - T2 := ContinuousLinearMap.ext fun z => by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
      rw [sub_eq_add_neg]; congr 1; exact neg_one_smul ℝ (T2 z)
    rw [e1, e2] at h; exact h
  have h1 : sa16y5f_Gop d m p s M (fun y => a1 y - a2 y) = Td := sa16y5f_Gop_eq hTd
  have h2 : sa16y5f_Gop d m p s M (fun y => a1 y - a2 y) = T1 - T2 := sa16y5f_Gop_eq hF
  rw [sa16y5f_Gop_eq hT1, sa16y5f_Gop_eq hT2, ← h2, h1]
  calc ‖Td y‖ ≤ ‖Td‖ * ‖y‖ := Td.le_opNorm y
    _ ≤ K * δ * ‖y‖ := mul_le_mul_of_nonneg_right hTdn (norm_nonneg _)

end Fr2

end HRS.Whole.AppendixA.Phase2SA16R

end
