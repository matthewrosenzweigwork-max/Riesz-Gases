import HRS.MC.S7PIDNMain
import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet T (part 7): `polyPath` as a continuous linear map of the finite node family
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDN

variable {d : ℕ}

theorem S7PIDT_Phi (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (c c' : ℝ) (hc : 0 ≤ c) (hcc : c < c') (hc' : c' ≤ T) (n : ℕ) :
    ∃ Φ : (Fin (2 ^ n + 1) → NegSobolev d m) →L[ℝ] PathSpace d m T,
      ∀ v : ℕ → NegSobolev d m, polyPath R.D R.ρ m T c c' n v = Φ (fun i => v i.1) := by
  obtain ⟨C₁, hC₁, hLip⟩ := S7PIDN_Phi_lip R m hm T hT
  have hsub : ∀ x y : Fin (2 ^ n + 1) → NegSobolev d m,
      S7PIDN_Phi R.D R.ρ m T c c' n x - S7PIDN_Phi R.D R.ρ m T c c' n y =
        S7PIDN_Phi R.D R.ρ m T c c' n (x - y) := by
    intro x y
    unfold S7PIDN_Phi
    rw [S7PIDN_polyPath_sub R m hm T hT c c' hc hcc hc' n]
    congr 1
    funext i
    by_cases h : i < 2 ^ n + 1 <;> simp [h]
  have h0 : S7PIDN_Phi R.D R.ρ m T c c' n 0 = 0 := by
    have := hsub 0 0
    rw [sub_self, sub_self] at this
    exact this.symm
  have hneg : ∀ y, S7PIDN_Phi R.D R.ρ m T c c' n (-y) = - S7PIDN_Phi R.D R.ρ m T c c' n y := by
    intro y
    have := hsub 0 y
    rw [zero_sub, h0, zero_sub] at this
    exact this.symm
  have hadd : ∀ x y, S7PIDN_Phi R.D R.ρ m T c c' n (x + y) =
      S7PIDN_Phi R.D R.ρ m T c c' n x + S7PIDN_Phi R.D R.ρ m T c c' n y := by
    intro x y
    have := hsub x (-y)
    rw [sub_neg_eq_add, hneg, sub_neg_eq_add] at this
    exact this.symm
  let f : (Fin (2 ^ n + 1) → NegSobolev d m) →+ PathSpace d m T :=
    { toFun := S7PIDN_Phi R.D R.ρ m T c c' n
      map_zero' := h0
      map_add' := hadd }
  have hcont : Continuous f := by
    have : LipschitzWith ⟨C₁, by linarith⟩ (S7PIDN_Phi R.D R.ρ m T c c' n) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]
        exact hLip c c' hc hcc hc' n x y
    exact this.continuous
  refine ⟨AddMonoidHom.toRealLinearMap f hcont, fun v => ?_⟩
  exact S7PIDN_Phi_eq R.D R.ρ m T c c' n v

end HRS.MC.Sec7.S7PIDT

end
