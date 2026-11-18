import HRS.MS.S104eC2G

/-!
# S104E route C, packet C2, part H: linearity in the density and Lipschitz dependence on `ρ`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.

* `c2_Q_sub_density`: `Q_{ρ-ρ'} f = Q_ρ f - Q_ρ' f` for `ρ, ρ' ∈ U2Dec 1 L ·` (`L > d`) and `f ∈ HolB j η B` (the relayed form with `ρ` merely integrable
  and `f ∈ C^1` is false: the Bochner integrals of the cancellation form can be junk);
* `c2_Q_lip`: `‖D^i (Q_ρ f - Q_ρ' f)‖ ≤ C ε B` for `i ≤ j` if `ρ - ρ' ∈ U2Dec (j+3) L ε`, every admissible `η`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

theorem c2_Q_sub_density (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L A A' : ℝ} (hL : (d : ℝ) < L) {ρ ρ' : Euc d → ℝ}
    (hρ : U2Dec 1 L A ρ) (hρ' : U2Dec 1 L A' ρ') {j : ℕ} {B : ℝ} {f : Euc d → ℝ} (hf : HolB j η B f) :
    s103bQ d s (fun y => ρ y - ρ' y) f = fun x => s103bQ d s ρ f x - s103bQ d s ρ' f x := by
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hηd : s + 1 - η < (d : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hη0
    linarith
  have hf0 := s104c2_HolB_zero hηp hη1.le hf
  funext x
  unfold s103bQ
  have hF : ∀ i : Fin d, movForce d s (fun y => ρ y - ρ' y) x i = movForce d s ρ x i - movForce d s ρ' x i :=
    fun i => s104c2_conv_sub s x (s104c2_int_rho hd hs0 hsd hη1 hηd hηp hL hρ x)
      (s104c2_int_rho hd hs0 hsd hη1 hηd hηp hL hρ' x) i
  have hM : ∀ i : Fin d, movForce d s (fun y => (ρ y - ρ' y) * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i =
      movForce d s (fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i -
        movForce d s (fun y => ρ' y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) x i := fun i => by
    have e : (fun y => (ρ y - ρ' y) * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) =
        fun y => ρ y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) -
          ρ' y * fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ)) := by funext y; ring
    rw [e]
    exact s104c2_conv_sub s x (s104c2_int_k hd hs0 hsd hη1 hηd hηp hL hρ hf0 _ x)
      (s104c2_int_k hd hs0 hsd hη1 hηd hηp hL hρ' hf0 _ x) i
  simp only [hF, hM]
  have e1 : ∀ i : Fin d, (-1 : ℝ) * ((movForce d s ρ x i - movForce d s ρ' x i) *
      fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) =
      (-1 : ℝ) * (movForce d s ρ x i * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) -
        (-1 : ℝ) * (movForce d s ρ' x i * fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ))) := fun i => by ring
  simp only [e1, Finset.sum_sub_distrib]
  ring

theorem c2_Q_lip (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε A A' : ℝ) (ρ ρ' : Euc d → ℝ), 0 ≤ ε → U2Dec 1 L A ρ → U2Dec 1 L A' ρ' →
      U2Dec (j + 3) L ε (fun y => ρ y - ρ' y) →
      ∀ (B : ℝ) (f : Euc d → ℝ), HolB j η B f →
        Bd j (C * ε * B) (fun x => s103bQ d s ρ f x - s103bQ d s ρ' f x) := by
  obtain ⟨C, hC0, hC⟩ := s104c2_Q_bd_sharp hd hs0 hsd j hη0 hη1 hL
  refine ⟨C, hC0, fun ε A A' ρ ρ' hε hρ hρ' hdiff B f hf => ?_⟩
  have hL' : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ s := hs0
    linarith
  have hdiff' : U2Dec (j + 1) L ε (fun y => ρ y - ρ' y) :=
    ⟨hdiff.1.of_le (by exact_mod_cast (by omega : j + 1 ≤ j + 3)), fun m hm => hdiff.2 m (by omega)⟩
  have := hC ε (fun y => ρ y - ρ' y) hε hdiff' B f hf
  rwa [c2_Q_sub_density (by omega) hs0 hsd hη0 hη1 hL' hρ hρ' hf] at this

end HRS.MS.S104e.C

end
