import HRS.MS.Fp81S21GaussG4U5
import HRS.MS.Fp81S21GaussG4U6
import HRS.MS.Fp81S21GaussG4U77

/-! A finite-combination stage toward the compact G4 passage. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- The old, new, and centered initial scalar estimates hold with one constant
on finite Hermite combinations.  This packages U5--U7; compact tests require a
separate propagated-energy limit argument. -/
theorem fp81s21_g4_combo_pieces (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
          ∀ v w, 0 ≤ v → v ≤ w →
            fp81s21_g4_initialValue R f v w ≤
                A * (w-v)^2 * fp81s21_g4_J p.d f ∧
            fp81s21_g4_Old R f v w ≤
                A * (w-v)^2 * fp81s21_g4_J p.d f ∧
            fp81s21_g4_New R f v w ≤
                A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f) := by
  obtain ⟨δo, hδo, hδohalf, hold⟩ := fp81s21_g4_old_combo p
  obtain ⟨δn, hδn, hδnhalf, hnew⟩ := fp81s21_g4_new_combo p
  obtain ⟨δi, hδi, hδihalf, hini⟩ := fp81s21_g4_initial_combo p
  let δ0 : ℝ := min δo (min δn δi)
  have hδ0 : 0 < δ0 := lt_min hδo (lt_min hδn hδi)
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left δo (min δn δi)).trans hδohalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδole : δ ≤ δo := hδle.trans (min_le_left δo (min δn δi))
  have hδnle : δ ≤ δn := hδle.trans
    ((min_le_right δo (min δn δi)).trans (min_le_left δn δi))
  have hδile : δ ≤ δi := hδle.trans
    ((min_le_right δo (min δn δi)).trans (min_le_right δn δi))
  obtain ⟨Ao, hAo, holdR⟩ := hold δ hδ hδole R
  obtain ⟨An, hAn, hnewR⟩ := hnew δ hδ hδnle R
  obtain ⟨Ai, hAi, hiniR⟩ := hini δ hδ hδile R
  let A : ℝ := max Ao (max An Ai)
  have hA : 0 ≤ A := le_trans hAo (le_max_left Ao (max An Ai))
  have hAoA : Ao ≤ A := le_max_left Ao (max An Ai)
  have hAnA : An ≤ A :=
    (le_max_left An Ai).trans (le_max_right Ao (max An Ai))
  have hAiA : Ai ≤ A :=
    (le_max_right An Ai).trans (le_max_right Ao (max An Ai))
  refine ⟨A, hA, ?_⟩
  intro f hf v w hv hvw
  have hcost : 0 ≤ fp81s21_g4_J p.d f := by
    unfold fp81s21_g4_J
    exact sq_nonneg _
  have hΔ : 0 ≤ w-v := sub_nonneg.mpr hvw
  have hΔsq : 0 ≤ (w-v)^2 := sq_nonneg _
  have hΔnew : 0 ≤ (w-v)+(w-v)^2 := add_nonneg hΔ hΔsq
  have hi := hiniR f hf v w hv hvw
  have ho := holdR f hf v w hv hvw
  have hn := hnewR f hf v w hv hvw
  refine ⟨hi.trans ?_, ho.trans ?_, hn.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAiA hΔsq) hcost
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAoA hΔsq) hcost
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAnA hΔnew) hcost

#print axioms fp81s21_g4_combo_pieces

end HRS.Fp81.S21
