import HRS.MS.MfeConfAux6
import HRS.MP.RdGenerator
import HRS.MH.DualityRdC1b
import HRS.MH.DualityRdB1

/-!
# S.B.1, packet F1 (part 2): one density slice, the force `F = ∇g * ρ` and the flux `ρ u`

A *slice* `Sb1Slice d C h` is a probability density `h` on `ℝ^d` of class `C³` with the decay
`‖D^l h(y)‖ ≤ C (1+|y|)^{-(d+1)}`, `l ≤ 3` (`RgDecay 3`), with a constant `C` that is uniform along a trajectory
(it comes from the weighted bound `Λ` of `IsRegularDensityW`: `C = d^r max(Λ,0) 2^{d+3}`).

* `sb1_slice_of_regular`: `IsRegularDensityW r Λ ρ` (`3 ≤ r`) gives a slice.
* `sb1_Fk_*`: the components `F_k = (∇g * h)_k` (cancellation convention) are `C¹` with
  `D F_k = rgT κ_k (D h)` and uniform `C¹` bounds depending only on `(d,s,C)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen

variable {d : ℕ}

/-- A density slice with uniform decay constant `C` (`C³`, decay `(1+|y|)^{-(d+1)}` of `D^l`, `l ≤ 3`). -/
structure Sb1Slice (d : ℕ) (C : ℝ) (h : Euc d → ℝ) : Prop where
  dens : Whole.IsProbDensity h
  decay : RgDecay 3 (fun _ => C) h
  C_nonneg : 0 ≤ C

theorem sb1_slice_of_regular (hd : 1 ≤ d) {r : ℕ} (hr : 3 ≤ r) {Λ : ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hreg : Whole.IsRegularDensityW r Λ ρ) :
    Sb1Slice d ((d : ℝ) ^ r * max Λ 0 * 2 ^ ((d : ℝ) + 3)) ρ := by
  have hw : Whole.weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal Λ := le_trans le_add_self hreg.2.2
  have hfin : Whole.weightedSupE r ((d : ℝ) + 3) ρ < ⊤ := lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hΛ : (Whole.weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ max Λ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
    rw [ENNReal.toReal_ofReal'] at this
    exact this
  have hdec := rg_rho_decay hd hreg.2.1 hfin hΛ
  exact ⟨hρ, rg_decay_mono hr hdec, by positivity⟩

/-- Pointwise facts of a slice. -/
theorem sb1_slice_facts {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) :
    ContDiff ℝ 3 h ∧ (∀ y, ‖h y‖ ≤ C * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧
      (∀ y, ‖fderiv ℝ h y‖ ≤ C * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧ (∀ y, ‖fderiv ℝ h y‖ ≤ C) ∧
      (∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ C) ∧ (∀ y, ‖h y‖ ≤ C) := by
  have ha : ∀ l : ℕ, 0 ≤ (fun _ : ℕ => C) l := fun _ => S.C_nonneg
  obtain ⟨h2, h0, h1, h2'⟩ := rg_decay_parts (a := fun _ => C) (by norm_num : 2 ≤ 3) ha S.decay
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨S.decay.1, h0, h1, fun y => (h1 y).trans (mul_le_of_le_one_right S.C_nonneg (hw y)),
    h2', fun y => (h0 y).trans (mul_le_of_le_one_right S.C_nonneg (hw y))⟩

/-- The `k`-th component of the force `∇g * h` (cancellation convention). -/
def sb1F (d : ℕ) (s : ℝ) (h : Euc d → ℝ) (k : Fin d) (x : Euc d) : ℝ :=
  (Whole.convGradConvW (Whole.rieszKernelGrad d s) h x) k

theorem sb1F_eq_rgT (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C : ℝ} {h : Euc d → ℝ}
    (S : Sb1Slice d C h) (k : Fin d) :
    sb1F d s h k = rgT (fun z => (Whole.rieszKernelGrad d s z) k) h := by
  obtain ⟨hc, h0, h1, h1', -, -⟩ := sb1_slice_facts S
  funext x
  exact rg_force_comp hd hs0 hsd (hc.differentiable (by norm_num)) S.C_nonneg S.C_nonneg h0 h1' x k

/-- The uniform `C¹` bound of the force components. -/
def sb1BF (d : ℕ) (s C : ℝ) : ℝ :=
  Whole.movtr_sigma s * (C * rgNear d s + 4 ^ (s + 1) * C * rgW d)

theorem sb1F_contDiff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C : ℝ} {h : Euc d → ℝ}
    (S : Sb1Slice d C h) (k : Fin d) :
    ContDiff ℝ 1 (sb1F d s h k) ∧ ∀ l, l ≤ 1 → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ l (sb1F d s h k) x‖ ≤ sb1BF d s C := by
  rw [sb1F_eq_rgT hd hs0 hsd S k]
  have := rg_Tdiff hd hs0 hsd (rgKerComp_ok hs0 k) 1 (fun _ => C) (fun _ => S.C_nonneg) h
    (by simpa using S.decay)
  exact ⟨this.1, fun l hl x => (this.2 l hl x).trans (le_of_eq rfl)⟩

theorem sb1F_fderiv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C : ℝ} {h : Euc d → ℝ}
    (S : Sb1Slice d C h) (k : Fin d) (x : Euc d) :
    HasFDerivAt (sb1F d s h k) (rgT (fun z => (Whole.rieszKernelGrad d s z) k) (fderiv ℝ h) x) x := by
  rw [sb1F_eq_rgT hd hs0 hsd S k]
  exact rg_hasFDerivAt_decay hd hs0 hsd (rgKerComp_ok hs0 k) (by norm_num : 2 ≤ 3)
    (fun _ => S.C_nonneg) S.decay x

end HRS.MS.MfeConf
