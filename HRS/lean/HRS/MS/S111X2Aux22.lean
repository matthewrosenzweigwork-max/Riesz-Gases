import HRS.MS.S111X2Aux21

/-!
# S11.1 X2, packet E04 (time shift): autonomy of the classical propagator

`s111x2_cls_shift`: if `h'` is a classical adjoint solution on `[0,u+t]` then `q ↦ h'(q+u)` is a classical adjoint
solution on `[0,t]` with the same terminal datum (the thermal generator is autonomous).
`s111x2_prop_shift`: hence `U^{u+a,u+t} ψ = U^{a,t} ψ` on the thermal reference.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_cls_shift {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} (T : TD d s β ρ M C)
    {t u : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) {ψ : Euc d → ℝ} {h' : ℝ → Euc d → ℝ}
    (hh : IsClassicalAdjointW C (u + t) ψ h') :
    IsClassicalAdjointW C t ψ (fun q => h' (q + u)) := by
  have hmem : ∀ q ∈ Icc (0 : ℝ) t, q + u ∈ Icc (0 : ℝ) (u + t) := fun q hq =>
    ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨B0, B1, B2, -, -, -, hB⟩ := HRS.MS.S111X1.classical_bounds hh
  have hC : ∀ r ∈ Icc (0 : ℝ) (u + t), CbD (h' r) B1 B2 := fun r hr =>
    ⟨hh.c2 r hr, fun x => (hB r hr x).2.1, fun x => (hB r hr x).2.2⟩
  have hauto : ∀ q ∈ Icc (0 : ℝ) t, generatorW C q (h' (q + u)) = generatorW C (q + u) (h' (q + u)) := fun q hq =>
    (s111x2_gen_auto T (hC _ (hmem q hq)) q).trans (s111x2_gen_auto T (hC _ (hmem q hq)) (q + u)).symm
  have hshift : Continuous fun p : Icc (0 : ℝ) t × Euc d =>
      ((⟨p.1.1 + u, hmem p.1.1 p.1.2⟩ : Icc (0 : ℝ) (u + t)), p.2) :=
    (Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add continuous_const)
      (fun p => hmem p.1.1 p.1.2)).prodMk continuous_snd
  refine ⟨fun q hq => hh.c2 _ (hmem q hq), fun j hj => ?_, fun j hj => ?_, ?_, fun x q hq => ?_, ?_, ?_⟩
  · obtain ⟨B, hB'⟩ := hh.bdd j hj
    exact ⟨B, fun q hq x => hB' _ (hmem q hq) x⟩
  · exact (hh.cont_c2 j hj).comp hshift
  · show h' (t + u) = ψ
    rw [show t + u = u + t by ring]
    exact hh.terminal
  · have hq' : q + u ∈ Ioo (0 : ℝ) (u + t) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
    have := (hh.time_deriv x (q + u) hq').comp_add_const q u
    rw [← hauto q ⟨hq.1.le, hq.2.le⟩] at this
    exact this
  · have h2 := hh.cont_time_deriv.comp hshift
    refine h2.congr (fun p => ?_)
    simp only [Function.comp]
    rw [hauto p.1.1 p.1.2]
  · obtain ⟨B, hB'⟩ := hh.bdd_time_deriv
    refine ⟨B, fun q hq x => ?_⟩
    show |generatorW C q (h' (q + u)) x| ≤ B * (1 + ‖x‖)
    rw [hauto q hq]
    have := hB' (q + u) (hmem q hq) x
    exact this

/-- Time-shift invariance of the propagator on the thermal reference. -/
theorem s111x2_prop_shift (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {t u a' : ℝ} (hu : 0 ≤ u) (ha' : 0 ≤ a') (hat : a' ≤ t)
    {ψ : Euc d → ℝ} {h' : ℝ → Euc d → ℝ}
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (u + t) ψ h') :
    propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (u + a') (u + t) ψ =
      propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) a' t ψ := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  have ht : 0 ≤ t := ha'.trans hat
  have hg := s111x2_cls_shift T hu ht hh
  rw [s111x2_prop_eq hd hs0 hs ha hβ hρ (by linarith) hh ⟨by linarith, by linarith⟩,
    s111x2_prop_eq hd hs0 hs ha hβ hρ ht hg ⟨ha', hat⟩]
  show h' (u + a') = h' (a' + u)
  rw [add_comm a' u]

end HRS.MS.S111X2
