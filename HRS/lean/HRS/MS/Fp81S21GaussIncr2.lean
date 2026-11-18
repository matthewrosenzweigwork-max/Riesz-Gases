import HRS.MS.Fp81S21GaussIncr
import HRS.MS.Fp81S21WindowOrbitDecay
import HRS.MS.Fp81S21WindowFeature5
import HRS.MS.R2WinErrAux11

/-!
# HRS S2.1(iii), SOL71: all-time pointwise gradient envelopes

The orbit estimates control a bounded-jet norm of the Euclidean gradient.  The
conversion below extracts its order-zero term without changing the amplitude.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

private theorem fp81s21_gauss_incr_pointwise_gradient_of_orbit
    {d k : ℕ} {C : WholeCoeff d} {t r A c : ℝ} {φ : Euc d → ℝ}
    (hA : 0 ≤ A) (hc : 0 < c)
    (hOrbit : R2OrbitGrad C k t φ A c)
    (hr : r ∈ Icc (0 : ℝ) t) (x : Euc d) :
    ‖gradient (propagatorW C r t φ) x‖ ≤ A * Real.exp (-c * (t - r)) := by
  have hAE : 0 ≤ A * Real.exp (-c * (t - r)) := by positivity
  by_cases hex : ∃ f, IsClassicalAdjointW C t φ f
  · obtain ⟨f, hf⟩ := hex
    have hcanonical : IsClassicalAdjointW C t φ
        (fun z => propagatorW C z t φ) := by
      simpa using HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
    have hcb := (hOrbit (fun z => propagatorW C z t φ) hcanonical r hr).2
    have hpoint := HRS.MS.R2WinErr.s104_cbNormVecE_le hAE hcb
      0 (by omega) x
    simpa [norm_iteratedFDeriv_zero] using hpoint
  · have hzero : propagatorW C r t φ = 0 := by
      unfold propagatorW
      simp only [dif_neg hex]
    simpa [hzero, gradient] using hAE

/-- Both propagated terminal inputs have pointwise Euclidean gradient decay
with constants selected before all physical times and modes. -/
theorem fp81s21_gauss_incr_gradient_decay (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ g c : ℝ, 0 ≤ g ∧ 0 < c ∧
          ∀ r t : ℝ, 0 ≤ r → r ≤ t →
            ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
              ‖gradient (propagatorW (r26t3_coeff R) r t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
                g * s104_b p.d α * Real.exp (-c * (t - r)) ∧
              ‖gradient (propagatorW (r26t3_coeff R) r t
                  (generatorW (r26t3_coeff R) t
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x‖ ≤
                g * s104_b p.d α * Real.exp (-c * (t - r)) := by
  obtain ⟨δ0, hδ0, hδ0half, hdecay⟩ :=
    fp81s21_moving_orbit_gradient_decay p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨g, c, hg, hc, hsum, horbits⟩ := hdecay δ hδ hδle R
  refine ⟨g, c, hg, hc, ?_⟩
  intro r t hr hrt α x
  have ht : 0 ≤ t := hr.trans hrt
  have hrmem : r ∈ Icc (0 : ℝ) t := ⟨hr, hrt⟩
  have hA : 0 ≤ g * s104_b p.d α :=
    mul_nonneg hg (s104_b_nonneg α)
  have hPhi := (horbits α).1 t ht
  have hGen := (horbits α).2 t ht
  exact ⟨
    fp81s21_gauss_incr_pointwise_gradient_of_orbit hA hc hPhi hrmem x,
    fp81s21_gauss_incr_pointwise_gradient_of_orbit hA hc hGen hrmem x⟩

/-- A single radius supports the scalar derivative identity and both gradient
decay estimates; each amplitude is selected after the trajectory and before
the interval, start, mode, terminal time, and spatial point. -/
theorem fp81s21_gauss_incr_terminal_envelopes (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ B g c : ℝ, 0 ≤ B ∧ 0 ≤ g ∧ 0 < c ∧
          (∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
            ∀ α : MultiIndex p.d, ∀ t ∈ Icc b (b + H), ∀ x : Euc p.d,
              |s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (b + H) b t α x| ≤ B * s104_b p.d α ∧
              s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (b + H) b t α x =
                propagatorW (r26t3_coeff R) b t
                  (generatorW (r26t3_coeff R) t
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) ∧
          (∀ r t : ℝ, 0 ≤ r → r ≤ t →
            ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
              ‖gradient (propagatorW (r26t3_coeff R) r t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
                g * s104_b p.d α * Real.exp (-c * (t - r)) ∧
              ‖gradient (propagatorW (r26t3_coeff R) r t
                  (generatorW (r26t3_coeff R) t
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x‖ ≤
                g * s104_b p.d α * Real.exp (-c * (t - r))) := by
  obtain ⟨δs, hδs, hδshalf, hscalar⟩ :=
    fp81s21_gauss_incr_scalar_terminal_bound p
  obtain ⟨δg, hδg, hδghalf, hgradient⟩ :=
    fp81s21_gauss_incr_gradient_decay p
  let δ0 : ℝ := min δs δg
  have hδ0 : 0 < δ0 := lt_min hδs hδg
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδshalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨B, hB, hscalarR⟩ := hscalar δ hδ
    (hδle.trans (min_le_left _ _)) R
  obtain ⟨g, c, hg, hc, hgradientR⟩ := hgradient δ hδ
    (hδle.trans (min_le_right _ _)) R
  exact ⟨B, g, c, hB, hg, hc, hscalarR, hgradientR⟩

#print axioms fp81s21_gauss_incr_gradient_decay
#print axioms fp81s21_gauss_incr_terminal_envelopes

end HRS.Fp81.S21

end
