import HRS.MH.PairingRdDefs
import HRS.MH.DualityRdB1Aux
import HRS.Whole.Q09BAux2

/-!
# PairingRd packets PR9, PR10 (`pairKernelRdB_bound_rd`, `pairKernelRdB_measurable_rd`, `pairKernelRdB_symm_rd`)

Statements copied verbatim from `HRS/MH/PairingRdSpec.lean`.
* PR9: `pairKernelRdB f M s = (1/2) * pairKernelRd D f` for the dynamics `D = (s, M)` (helper `pkRdB_eq_pkRd`), then
  `HRS.MH.DualityRd.db1_pK_bound`.
* PR10a: `HRS.MH.DualityRd.db1_pK_measurable` transported by the same identity.
* PR10b: torus template `pairKernelB_symm` with `Whole.Q09B.q09b_rkg_neg` (`∇g(-z) = -∇g(z)`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- The symmetrized kernel is `1/2` times the whole-space kernel `pairKernelRd` of the dynamics `(s, M)`. -/
theorem pkRdB_eq_pkRd (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (x y : Euc d) :
    pairKernelRdB f M s x y = (1 / 2 : ℝ) * HRS.MH.DualityRd.pairKernelRd
      ({ s := s, M := M, V := 0, invβ := 0 } : Whole.WholeDyn d) f x y := by
  unfold pairKernelRdB HRS.MH.DualityRd.pairKernelRd
  split_ifs <;> simp

/-- **PR9** `pairKernelRdB_bound_rd` (proof). -/
theorem pairKernelRdB_bound_rd {s : ℝ} (hs0 : 0 ≤ s) (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ x y : Euc d, |pairKernelRdB f M s x y| ≤
      Kc * (Set.indicator (Metric.ball (0 : Euc d) 1) (fun z => ‖z‖ ^ (-s)) (x - y) + 1) := by
  obtain ⟨Kc, hKc0, hK⟩ := HRS.MH.DualityRd.db1_pK_bound
    (({ s := s, M := M, V := 0, invβ := 0 } : Whole.WholeDyn d)) hs0 hf
  refine ⟨Kc, hKc0, fun x y => ?_⟩
  have hb : |HRS.MH.DualityRd.pairKernelRd ({ s := s, M := M, V := 0, invβ := 0 } : Whole.WholeDyn d) f x y|
      ≤ Kc * (Set.indicator (Metric.ball (0 : Euc d) 1) (fun z => ‖z‖ ^ (-s)) (x - y) + 1) := hK x y
  have hI : 0 ≤ Set.indicator (Metric.ball (0 : Euc d) 1) (fun z => ‖z‖ ^ (-s)) (x - y) :=
    Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hpos : 0 ≤ Kc * (Set.indicator (Metric.ball (0 : Euc d) 1) (fun z => ‖z‖ ^ (-s)) (x - y) + 1) :=
    mul_nonneg hKc0 (by linarith)
  rw [pkRdB_eq_pkRd, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- **PR10a** `pairKernelRdB_measurable_rd` (proof). -/
theorem pairKernelRdB_measurable_rd {s : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) :
    Measurable (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2) := by
  have hm := HRS.MH.DualityRd.db1_pK_measurable
    (D := ({ s := s, M := M, V := 0, invβ := 0 } : Whole.WholeDyn d)) hf
  have e : (fun p : Euc d × Euc d => pairKernelRdB f M s p.1 p.2)
      = fun p => (1 / 2 : ℝ) * HRS.MH.DualityRd.pairKernelRd
          ({ s := s, M := M, V := 0, invβ := 0 } : Whole.WholeDyn d) f p.1 p.2 := by
    funext p
    exact pkRdB_eq_pkRd f M s p.1 p.2
  rw [e]
  exact hm.const_mul _

/-- **PR10b** `pairKernelRdB_symm_rd` (proof). -/
theorem pairKernelRdB_symm_rd {s : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) (f : Euc d → ℝ) (x y : Euc d) :
    pairKernelRdB f M s y x = pairKernelRdB f M s x y := by
  by_cases hxy : x = y
  · subst hxy
    rfl
  · have hyx : y ≠ x := fun h => hxy h.symm
    unfold pairKernelRdB
    rw [if_neg hxy, if_neg hyx]
    have e1 : y - x = -(x - y) := (neg_sub x y).symm
    have e2 : gradient f y - gradient f x = -(gradient f x - gradient f y) := (neg_sub _ _).symm
    have hneg : ∀ v : Euc d, Torus.matVec M (-v) = -Torus.matVec M v := fun v => by
      unfold Torus.matVec
      exact map_neg _ _
    rw [e1, e2, Whole.Q09B.q09b_rkg_neg, hneg, inner_neg_left, inner_neg_right, neg_neg]

end HRS.MH.PairingRdP
