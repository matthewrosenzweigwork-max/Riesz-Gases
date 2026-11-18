import HRS.MS.MfeConfAux172
import HRS.MS.MfeConfAux60
import HRS.MS.MfeConfAux19

/-!
# S.B.1 (SB5), R3d (part 4): `SuperMovEnt`, `SubMovEnt` and the frozen conclusions, modulo `Sb1HBAll`

* `sb1_superMovEnt_of_hB`, `sb1_subMovEnt_of_hB`: `SuperMovEnt d s`, `SubMovEnt d s a` from `Sb1HBAll d`;
* `sb1_super_of_hB`, `sb1_sub_of_hB`: the exact frozen conclusions of `mfe_confined_rd_gradient_super/_sub` (`d ≥ 2`, resp. `d ≥ 3`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_superMovEnt_of_hB (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hHB : Sb1HBAll d) :
    SuperMovEnt d s := by
  intro D hDs hV3 hB hcoer N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  obtain ⟨B, hB⟩ := hB
  obtain ⟨cV, CV, hcV, hconf⟩ := hcoer
  subst hDs
  exact sb1_movEnt_core hHB hd hs0 hsd ⟨hV3, hB⟩ hcV hconf hN hT h K hKi hK

theorem sb1_subMovEnt_of_hB (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (hHB : Sb1HBAll d) : SubMovEnt d s a := by
  intro D hDs Q b c q hq hQ hQq hVQ N hN T Λ r hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  have hd1 : 1 ≤ d := by omega
  have hsd' : D.s < d := by linarith
  obtain ⟨B, hPot⟩ := sb1_pot_quad Q b c hVQ
  obtain ⟨cV, CV, hcV, hconf⟩ := sb1_quad_confining Q b c hq hQq hVQ
  refine sb1_movEnt_core hHB hd1 hs0 hsd' hPot hcV hconf hN hT h K hKi fun t ht => ?_
  obtain ⟨L, F, hF0, hL, -, hLF⟩ := hK t ht
  set Qc : Euc d →L[ℝ] Euc d := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) Q with hQc
  have hgrad : ∀ x, gradient D.V x = Qc x + b := fun x => sb1_gradient_V hQ hVQ x
  refine ⟨L + ‖Qc‖₊, LipschitzWith.of_dist_le_mul fun x y => ?_, ?_⟩
  · rw [dist_eq_norm, dist_eq_norm]
    have h1 := hL.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 : ‖Qc x - Qc y‖ ≤ ‖Qc‖ * ‖x - y‖ := by
      rw [← map_sub]; exact Qc.le_opNorm _
    have e : Whole.mfeTransportW D (ρ t) x - Whole.mfeTransportW D (ρ t) y =
        (Whole.mfeTransport0W D (ρ t) x - Whole.mfeTransport0W D (ρ t) y) + (Qc x - Qc y) := by
      unfold Whole.mfeTransportW
      rw [hgrad, hgrad]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    push_cast
    nlinarith
  · push_cast
    linarith

theorem sb1_super_of_hB (hd2 : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s)
    (hHB : Sb1HBAll d) : type_of% (@sb1_super_of_movEnt d hd2 s hs0 hsd hsc (sb1_superMovEnt_of_hB (by omega) hs0 hsd hHB)) :=
  sb1_super_of_movEnt hd2 hs0 hsd hsc (sb1_superMovEnt_of_hB (by omega) hs0 hsd hHB)

theorem sb1_sub_of_hB (hd3 : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : ℝ)
    (ha : (d : ℝ) < a ∧ a < (d : ℝ) + 2) (hHB : Sb1HBAll d) :
    type_of% (@sb1_sub_of_movEnt d hd3 s hs0 hsd a ha (sb1_subMovEnt_of_hB hd3 hs0 hsd a hHB)) :=
  sb1_sub_of_movEnt hd3 hs0 hsd a ha (sb1_subMovEnt_of_hB hd3 hs0 hsd a hHB)

end HRS.MS.MfeConf
