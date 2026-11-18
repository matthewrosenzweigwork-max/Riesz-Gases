import HRS.MS.Fp81S21GaussIncrFull

/-!
# HRS S2.1(iii), SOL71 G2: old-noise pointwise envelope

The two available G1 estimates combine to give a terminal-difference bound
with exponential decay in the distance from the earlier terminal.  This is
the pointwise estimate needed before integrating the old-noise contribution.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr

/-- For a fixed noise time `r ≤ v ≤ w`, the squared gradient difference
between terminals `v` and `w` is bounded by a time-integrable envelope.
The proof combines the terminal Lipschitz estimate with the two separate
gradient decay estimates; it does not assume a decayed Lipschitz export. -/
theorem fp81s21_gaussian_old_noise_gradient_sq_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ g g' c : ℝ, 0 ≤ g ∧ 0 ≤ g' ∧ 0 < c ∧
          ∀ r v w : ℝ, 0 ≤ r → r ≤ v → v ≤ w →
            ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
              ‖gradient (propagatorW (r26t3_coeff R) r w
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
                gradient (propagatorW (r26t3_coeff R) r v
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ^ 2 ≤
                2 * g * g' * (s104_b p.d α) ^ 2 * (w - v) *
                  Real.exp (-c * (v - r)) := by
  obtain ⟨δd, hδd, hδdhalf, hdecay⟩ :=
    fp81s21_gauss_incr_gradient_decay p
  obtain ⟨δl, hδl, hδlhalf, hlip⟩ :=
    fp81s21_gauss_incr_gradient_terminal_lipschitz p
  let δ0 := min δd δl
  have hδ0 : 0 < δ0 := lt_min hδd hδl
  have hδ0half : δ0 ≤ 1 / 2 := le_trans (min_le_left _ _) hδdhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδ0δ R
  obtain ⟨g, c, hg, hc, hdecayR⟩ :=
    hdecay δ hδ (hδ0δ.trans (min_le_left _ _)) R
  obtain ⟨g', hg', hlipR⟩ :=
    hlip δ hδ (hδ0δ.trans (min_le_right _ _)) R
  refine ⟨g, g', c, hg, hg', hc, ?_⟩
  intro r v w hr hrv hvw α x
  let b := s104_b p.d α
  let D := ‖gradient (propagatorW (r26t3_coeff R) r w
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
    gradient (propagatorW (r26t3_coeff R) r v
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖
  have hb : 0 ≤ b := s104_b_nonneg α
  have hd : 0 ≤ w - v := sub_nonneg.mpr hvw
  have habs : |w - v| = w - v := abs_of_nonneg hd
  have hLip := hlipR r v w hr hrv (hrv.trans hvw) α x
  have hDleA : D ≤ g' * b * (w - v) := by
    dsimp [D, b]
    rw [habs] at hLip
    exact hLip
  have hDecayW := (hdecayR r w hr (hrv.trans hvw) α x).1
  have hDecayV := (hdecayR r v hr hrv α x).1
  have hExpMono :
      Real.exp (-c * (w - r)) ≤ Real.exp (-c * (v - r)) := by
    apply Real.exp_le_exp.mpr
    have hdiff : v - r ≤ w - r := by linarith
    exact mul_le_mul_of_nonpos_left hdiff (by linarith)
  have hDleB : D ≤ 2 * g * b * Real.exp (-c * (v - r)) := by
    dsimp [D, b]
    calc
      _ ≤ ‖gradient (propagatorW (r26t3_coeff R) r w
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ +
          ‖gradient (propagatorW (r26t3_coeff R) r v
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ := norm_sub_le _ _
      _ ≤ g * s104_b p.d α * Real.exp (-c * (w - r)) +
          g * s104_b p.d α * Real.exp (-c * (v - r)) :=
        add_le_add hDecayW hDecayV
      _ ≤ g * s104_b p.d α * Real.exp (-c * (v - r)) +
          g * s104_b p.d α * Real.exp (-c * (v - r)) := by
        gcongr
      _ = 2 * g * s104_b p.d α * Real.exp (-c * (v - r)) := by ring
  have hA0 : 0 ≤ g' * b * (w - v) :=
    mul_nonneg (mul_nonneg hg' hb) hd
  have hD0 : 0 ≤ D := norm_nonneg _
  have hB0 : 0 ≤ 2 * g * b * Real.exp (-c * (v - r)) := by positivity
  calc
    D ^ 2 ≤ (g' * b * (w - v)) * D := by
      nlinarith [mul_le_mul_of_nonneg_right hDleA hD0]
    _ ≤ (g' * b * (w - v)) *
          (2 * g * b * Real.exp (-c * (v - r))) :=
      mul_le_mul_of_nonneg_left hDleB hA0
    _ = 2 * g * g' * b ^ 2 * (w - v) *
          Real.exp (-c * (v - r)) := by ring

#print axioms fp81s21_gaussian_old_noise_gradient_sq_bound

end HRS.Fp81.S21

end
