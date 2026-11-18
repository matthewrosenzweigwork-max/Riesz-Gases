import HRS.MS.Mov63EAux8

/-!
# S6.3, packet N6 (part 9): `MovInSmallClass`

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.  **`mne_class`**: the mild solution `v` with `‖v t‖ ≤ r e^{-c₀t}` and `ρ_t ≥ 0` (`t ≥ 0`) gives
`MovInSmallClass d s q β ρ m r c₀ f0 mneP` with `f0 = V_0/√ρ` (`mneF0fun`): all fields (`solution`: density, second moment `mne_second_moment`, weak form;
`init`, `weighted`, `cont`, `regular`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Class

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ) {v : ℝ → OscSpace d (m : ℝ)}

include H in
lemma mne_second_moment (u : OscSpace d (m : ℝ)) : Integrable (fun x => ‖x‖ ^ 2 * mneRho ρ hm u x) := by
  obtain ⟨KG, hKG0, hKG⟩ := mne_flux_bound hm H ‖u‖
  refine mne_int_of_bound (K := KG) ((continuous_norm.pow 2).mul (mne_rho_cd hm H u).continuous) (fun x => ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), mul_comm]
  exact (hKG u le_rfl x).2.2.1

/-- The initial perturbation `f₀ = V_0/√ρ`. -/
def mneF0fun (d : ℕ) (ρ : Euc d → ℝ) (hm : (d : ℝ) / 2 + 3 < m) (v : ℝ → OscSpace d (m : ℝ)) (x : Euc d) : ℝ :=
  mneV hm (v 0) x / Real.sqrt (ρ x)

include H in
lemma mne_movV (t : ℝ) (ht : 0 ≤ t) : movV ρ (mneP d ρ hm v) t = mneV hm (v t) := by
  funext x
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 ((mnb_rhoData H).pos x)
  simp only [movV, mneP, max_eq_left ht, mnc_hu]
  field_simp
  ring

include H in
/-- **N6a (class)**: the signed mild solution, once nonnegative, is a member of `MovInSmallClass`
(`ρ_t = ρ + √ρ V_t`, `V_t` the `C³` representative of `v_t`). -/
theorem mne_class (hmild : MneMild H hm v) (hnn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ mneP d ρ hm v t x)
    (r c₀ : ℝ) (hbd : ∀ t, 0 ≤ t → ‖v t‖ ≤ r * Real.exp (-c₀ * t)) :
    MovInSmallClass d s q β ρ m r c₀ (mneF0fun d ρ hm v) (mneP d ρ hm v) where
  solution := fun T => by
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun ψ hψ t ht => ?_⟩
    · rw [mneP_eq hm ht.1]
      exact mne_isProb hm H (v t) (hmild.mass t ht.1) (fun x => by
        have := hnn t ht.1 x
        rwa [mneP_eq hm ht.1] at this)
    · rw [mneP_eq hm ht.1]
      exact mne_second_moment hm H (v t)
    · exact mne_weak hm H hmild hnn hψ ht.1
  init := fun x => by
    have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 ((mnb_rhoData H).pos x)
    have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := Real.mul_self_sqrt ((mnb_rhoData H).pos x).le
    simp only [mneP, mneF0fun, max_self, mnc_hu]
    set s0 := Real.sqrt (ρ x) with hs0
    set V0 := mn_repFun 3 m (mne_hn hm) (v 0) x with hV0
    rw [← hss]
    field_simp
    rfl
  weighted := fun t ht => by
    rw [mne_movV hm H t ht]
    exact ⟨mneV_memOsc hm (v t), by rw [mneV_norm hm (v t)]; exact hbd t ht⟩
  cont := by
    refine hmild.cont.congr (fun t ht => ?_)
    show OscSpace.ofFun (m : ℝ) (movV ρ (mneP d ρ hm v) t) = v t
    rw [mne_movV hm H t ht, mneV_ofFun hm (v t)]
  regular := fun t ht => by
    rw [mneP_eq hm ht]
    exact (mne_rho_cd hm H (v t)).continuous

end Class

end HRS.MS.Mov63

end
