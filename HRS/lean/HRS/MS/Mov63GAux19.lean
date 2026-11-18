import HRS.MS.Mov63GAux18

/-!
# S6.3, packet N8 (part 19): output for N9

Namespace `HRS.MS.Mov63`, prefix `mng_`.  **`mov63_decay_f0`**: combines `mov63_positive_solution_f0` (N7) with `mov63_decay_bounds`: for the thermal data `H`,
`j ≥ 1`, `m > d/2 + j + 6` there are `ε_*, r, c, C > 0` (depending only on `H, j, m`) such that for every datum `f₀ ∈ C³ ∩ C_b^{j+1}` with
`√ρ f₀ ∈ Σ^m` of mass zero and `‖f₀‖_{C_b^{j+1}} + ‖√ρ f₀‖_{Σ^m} ≤ ε_*` the N5-N7 solution `v` is a member of `MovInSmallClass .. r (c₁/2) f₀`, satisfies
`ρ/2 ≤ ρ_t ≤ 2ρ`, `MovDecayBounds` with amplitude `movInitialNorm` and with amplitude `ε_*` (same constants), and `∫_0^∞ ‖u_t‖_{C_b^j} dt < ∞`.
`movDecayBounds_mono`: monotonicity in the amplitude.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.PoisKolm

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

lemma movDecayBounds_mono {j m : ℕ} {c C K K' : ℝ} {ρ₁ : ℝ → Euc d → ℝ} (hC : 0 ≤ C) (hK : K ≤ K')
    (h : MovDecayBounds d s q β ρ j m c C K ρ₁) : MovDecayBounds d s q β ρ j m c C K' ρ₁ := by
  intro t ht
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h t ht
  have hm : C * K * Real.exp (-c * t) ≤ C * K' * Real.exp (-c * t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC) (Real.exp_pos _).le
  exact ⟨⟨h1, h2.trans hm⟩, h3, h4, h5.trans (ENNReal.ofReal_le_ofReal hm)⟩

theorem mov63_decay_f0 (H : Mov2dTh d s β q ρ) {j : ℕ} (hj : 1 ≤ j) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (m : ℕ) (hm : (d : ℝ) / 2 + j + 6 < m),
      ∃ εstar r c C : ℝ, 0 < εstar ∧ εstar ≤ 1 / 4 ∧ 0 < r ∧ 0 < c ∧ 0 ≤ C ∧
        ∀ (hm3 : (d : ℝ) / 2 + 3 < m) (f0 : Euc d → ℝ), ContDiff ℝ 3 f0 → MemCb (j + 1) f0 →
          ∀ hosc : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x),
          MovMassZero ρ (mnd_m_nonneg hm3) (OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x)) →
          movInitialNorm ρ j m f0 ≤ εstar →
          ∃ v : ℝ → OscSpace d (m : ℝ), MneMild H hm3 v ∧
            v 0 = OscSpace.ofFun (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ∧
            MovInSmallClass d s q β ρ m r (c₁ / 2) f0 (mneP d ρ hm3 v) ∧
            (∀ t, 0 ≤ t → ∀ x, ρ x / 2 ≤ mneP d ρ hm3 v t x ∧ mneP d ρ hm3 v t x ≤ 2 * ρ x) ∧
            MovDecayBounds d s q β ρ j m c C (movInitialNorm ρ j m f0) (mneP d ρ hm3 v) ∧
            MovDecayBounds d s q β ρ j m c C εstar (mneP d ρ hm3 v) ∧
            ∫⁻ t in Ioi (0 : ℝ), cbNormVecE j (movU d s q β (mneP d ρ hm3 v t)) < ⊤ := by
  obtain ⟨c7, hc7, h7⟩ := mov63_positive_solution_f0 H
  refine ⟨c7, hc7, fun m hm => ?_⟩
  have hm3 : (d : ℝ) / 2 + 3 < m := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  obtain ⟨ε7, C7, hε7, hC7, h7'⟩ := h7 m hm3
  obtain ⟨δ1, c, Cd, hδ1, hc, hcc, hCd0, hdec⟩ := mov63_decay_bounds H hj hm C7 (c7 / 2) hC7.le (by positivity)
  set εstar : ℝ := min (min ε7 δ1) (1 / 4) with hεstar
  have hεpos : 0 < εstar := by rw [hεstar]; positivity
  refine ⟨εstar, C7 * εstar, c, Cd, hεpos, min_le_right _ _, by positivity, hc, hCd0, ?_⟩
  intro hm3' f0 hf0 hcb hosc hmass hsmall
  have hcbnn : 0 ≤ cbNorm (j + 1) f0 := by
    unfold cbNorm
    exact Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hoscnn : 0 ≤ oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) := Real.sqrt_nonneg _
  set K : ℝ := movInitialNorm ρ j m f0 with hK
  have hKdef : K = cbNorm (j + 1) f0 + oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) := rfl
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  have hKε : K ≤ εstar := hsmall
  have hKε7 : K ≤ ε7 := hKε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hKδ1 : K ≤ δ1 := hKε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hosc7 : oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ≤ ε7 := by
    rw [hKdef] at hKε7; linarith
  have hsup : ∀ x, |f0 x| ≤ 1 / 4 := fun x => by
    have h1 := mnf_norm_le_cbNorm hcb (Nat.zero_le (j + 1)) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    have : K ≤ 1 / 4 := hKε.trans (min_le_right _ _)
    rw [hKdef] at this; linarith
  obtain ⟨v, hM, hv0, hbd, hcls, hrat⟩ := h7' f0 hf0 hosc hmass hosc7 hsup
  have hvd : ∀ t, 0 ≤ t → ‖v t‖ ≤ C7 * K * Real.exp (-(c7 / 2) * t) := fun t ht => by
    refine (hbd t ht).trans ?_
    have hosc_le : oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ≤ K := by rw [hKdef]; linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hosc_le hC7.le) (Real.exp_pos _).le
  have hQ0 : ∀ y, mneQ ρ hm3' (v 0) y = 1 + f0 y := fun y => by
    rw [mnf_Q_eq hm3' H (v 0) y]
    have := congrFun (mnf_F0_eq hm3' H hf0 hosc hv0) y
    simp only [mneF0fun] at this
    rw [this]
  have hratio : ∀ t, 0 ≤ t → ∀ y, ρ y / 2 ≤ mneP d ρ hm3' v t y ∧ mneP d ρ hm3' v t y ≤ 2 * ρ y := hrat
  obtain ⟨hD, hI⟩ := hdec hm3' v hM K f0 hK0 hKδ1 hvd hratio hQ0 hcb (by rw [hKdef]; linarith)
  refine ⟨v, hM, hv0, ?_, hratio, hD, movDecayBounds_mono hCd0 hKε hD, hI⟩
  exact hcls.mono_radius (by
    have : oscNorm (m : ℝ) (fun x => Real.sqrt (ρ x) * f0 x) ≤ εstar := by rw [hKdef] at hKε; linarith
    exact mul_le_mul_of_nonneg_left this hC7.le)

end HRS.MS.Mov63

end
