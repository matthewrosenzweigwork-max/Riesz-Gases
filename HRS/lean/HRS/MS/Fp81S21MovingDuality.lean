import HRS.MS.Fp81S21MovingMeas
import HRS.MS.S21F_P00
import HRS.MS.GenPathAux27

/-!
# HRS S2.1(iii), packet 8.4: moving raw duality

The stationary source statements (and their direct imported sources) are:

* `HRS.MS.R2Interp.s102_duality` (`R2InterpAux80.lean`, importing
  `R2InterpAux79`, `R2InterpAux74`, and `GenPathAux27`): for `d ≥ 2`,
  `0 ≤ s < d/2`, `a, β > 0`, a thermal density `ρ`, a filtered strong solution
  on `[0,T]`, `t ∈ [0,T]`, and `m, α`, its exact conclusion is
  ```lean
  DualityIdentityRd P ℱ W' (quadraticGradientDyn d s a β) (fun _ => ρ) X t
    (fun r => propagatorW
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t
      (oscTestFun m α))
  ```
  It discharges `s56_duality_core` using thermal mean-field regularity and the
  thermal adjoint producer.
* `HRS.MS.R2Interp.s102_centered_identity` (`R2InterpAux84.lean`, importing
  `R2InterpAux83`) is unchanged; under its listed integrability, mean-zero, and
  raw-identity hypotheses its exact conclusion is:
  ```lean
  ∀ᵐ ζ ∂P, ∀ τ ∈ Icc (0 : ℝ) t,
    a τ ζ - ∫ ζ', a τ ζ' ∂P =
      (a 0 ζ - ∫ ζ', a 0 ζ' ∂P) + c * I τ ζ -
        ∫ r in Icc (0 : ℝ) τ, (e (r, ζ) - ∫ ζ', e (r, ζ') ∂P)
  ```
  from the raw identity, time × probability integrability of `e`, and a
  mean-zero integrable Itô integral `I`.
* `HRS.MS.R2Interp.s102_orbit_zeta` (`R2InterpAux87.lean`, importing
  `R2InterpAux86`) assumes the round-two density bounds, actual-law density
  control, filtered strong solution, and classical adjoint existence. Set
  `C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ)`,
  `μ := HRS.Whole.withDensityReal ρ`, and
  `f r := propagatorW C r t (oscTestFun m α)`. Its exact conclusion is:
  ```lean
  ∀ᵐ ζ ∂P, ∀ τ ∈ Icc (0 : ℝ) t,
    s102_zf P X ζ τ (propagatorW C τ t (oscTestFun m α)) =
      s102_zf P X ζ 0 (propagatorW C 0 t (oscTestFun m α)) +
      (Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N)) *
        itoIntegral P ℱ W' (s102_Ig (fun r => propagatorW C r t
          (oscTestFun m α)) t X) τ ζ +
      ∫ r in Icc (0 : ℝ) τ,
        (-(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r))
  ```

The moving wrapper below keeps the generic `s56_duality_core` conclusion and
replaces only the thermal discharge. The centered moving identity is in
`Fp81S21MovingDuality2.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd
open HRS.MS.R26T3 HRS.MS.R2Interp

/-- Moving raw duality for the chosen whole-space oscillator orbit. The only
trajectory regularity requested here is exactly the field consumed by
`s56_duality_core`; oscillator adjoints are produced from the trajectory. -/
theorem fp81s21_moving_duality
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (hreg : ∃ Λ : ℝ, IsRegularMFRd p.s 3 Λ H R.ρ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (α : MultiIndex p.d) :
    DualityIdentityRd A.P F.ℱ F.Wc (quadraticGradientDyn p.d p.s p.a p.β)
      R.ρ F.X t
      (fun r => propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
  classical
  let D : WholeDyn p.d := quadraticGradientDyn p.d p.s p.a p.β
  let C : WholeCoeff p.d := r26t3_coeff R
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hQ : (p.a • (1 : Matrix (Fin p.d) (Fin p.d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  obtain ⟨ΛV, G₀, hV⟩ := HRS.MS.Go.s55f_vhyp_quadV hQ 0 2
  have hVD : VHypRd 2 ΛV G₀ D.V := by
    show VHypRd 2 ΛV G₀ (confinement p.a)
    rw [HRS.MS.S21.s21_confinement_eq]
    exact hV
  obtain ⟨Λ, hΛ⟩ := hreg
  have hMF : IsWholeMeanFieldSolution D H R.ρ := by
    simpa [D] using R.resulting.global H
  have ht0 : 0 ≤ t := ht.1
  obtain ⟨ψ, hψ⟩ := HRS.MS.R2Interp.s102_osc_schwartz
    (wholeSpaceIndex p.d : ℝ) α
  have hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) := by
    constructor
    · rw [← hψ]
      exact ψ.smooth ⊤
    · rw [← hψ]
      exact (memOsc_schwartz ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ)
  obtain ⟨f₀, hf₀⟩ := fp81s21_adjoint_of_osc_test p R hφ ht0
  have hf₀' : IsClassicalAdjointW C t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α) f₀ := by
    simpa [C, r26t3_coeff, D] using hf₀
  have hf : IsClassicalAdjointW C t
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      (fun r => propagatorW C r t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) :=
    s102_propagator_classical ⟨f₀, hf₀'⟩
  have hX : IsWholeStrongSolution A.P D H A.X₀ A.W F.X := by
    simpa [D] using F.strong H
  have hres := HRS.MS.GenPath.s56_duality_core p.s Λ H ΛV G₀ D rfl
    p.hs0 hsd (inv_pos.2 p.hβ).le hVD R.ρ hMF hΛ A.P A.X₀ A.W F.X hX
    F.ℱ F.Wc F.filtered t ht (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
    (fun r => propagatorW C r t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) hf
  simpa [C, D, r26t3_coeff] using hres

#print axioms HRS.Fp81.S21.fp81s21_moving_duality

end HRS.Fp81.S21

end
