import HRS.MS.Fp81S21MovingItoRep3

/-!
# HRS S2.1(iii), packet 8.5: moving drift local L¹

Moving M1 controls the centered moving quadratic field on `A.X`. P00's
full-time indistinguishability event transfers that same field to the filtered
version `F.X`, which is the path used by the stochastic integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

private theorem fp81s21_moving_quadField_indist
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (F : FilteredParticle A)
    {ζ : A.Ω} (hζ : ∀ t : ℝ≥0, F.X t ζ = A.X t ζ)
    (hInd : ∀ᵐ ω ∂A.P, ∀ t : ℝ≥0, F.X t ω = A.X t ω)
    (u : ℝ) (f : Euc p.d → ℝ) :
    r2QuadField p.s (r26t3_mu R u) A.P F.X u ζ f =
      r2QuadField p.s (r26t3_mu R u) A.P A.X u ζ f := by
  unfold r2QuadField
  have hInt : (fun ω => pairEnergy
      (commutatorKernel p.d p.s (fun x => gradient f x))
      (F.X u.toNNReal ω) (r26t3_mu R u)) =ᵐ[A.P]
      (fun ω => pairEnergy
        (commutatorKernel p.d p.s (fun x => gradient f x))
        (A.X u.toNNReal ω) (r26t3_mu R u)) := by
    filter_upwards [hInd] with ω hω
    rw [hω u.toNNReal]
  rw [hζ u.toNNReal, integral_congr_ae hInt]

private theorem fp81s21_moving_transfer_drift
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (Mb : A.Ω → ℝ → ℝ) {r : ℕ} {c : MultiIndex p.d → ℝ}
    {ζ : A.Ω}
    (hA : S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H r ((p.d : ℝ) + 2)
      (fun u f => fp81s21_moving_r2QuadField R A u ζ f) (Mb ζ))
    (hζ : ∀ t : ℝ≥0, F.X t ζ = A.X t ζ)
    (hInd : ∀ᵐ ω ∂A.P, ∀ t : ℝ≥0, F.X t ω = A.X t ω) :
    S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H r ((p.d : ℝ) + 2)
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P F.X u ζ f) (Mb ζ) := by
  have hEq : ∀ u f,
      r2QuadField p.s (r26t3_mu R u) A.P F.X u ζ f =
        fp81s21_moving_r2QuadField R A u ζ f := by
    intro u f
    exact fp81s21_moving_quadField_indist p R A F hζ hInd u f
  obtain ⟨hZ, hM, hMbNonneg, hMbInt, hmeas⟩ := hA
  refine ⟨?_, ?_, hMbNonneg, hMbInt, ?_⟩
  · intro u hu
    have hfun : (fun f => r2QuadField p.s (r26t3_mu R u)
        A.P F.X u ζ f) = (fun f => fp81s21_moving_r2QuadField R A u ζ f) := by
      funext f
      exact hEq u f
    rw [hfun]
    exact hZ u hu
  · intro u hu f hf
    rw [hEq u f]
    exact hM u hu f hf
  · intro t ht α
    have hfun : (fun u => r2QuadField p.s (r26t3_mu R u)
        A.P F.X u ζ (propagatorW (r26t3_coeff R) u t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) =
      (fun u => fp81s21_moving_r2QuadField R A u ζ
        (propagatorW (r26t3_coeff R) u t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) := by
      funext u
      exact hEq u _
    rw [hfun]
    exact hmeas t ht α

/-- Moving drift assembly is progressively locally L¹. The local L¹ estimate
uses only moving M1 and P00 indistinguishability; no stationary reference
density or stationary actual-marginal bound is assumed. -/
theorem fp81s21_moving_bdE_locL1
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H r c hH)
    (hr : (p.d : ℝ) / 2 + 2 < r)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    (L : ℕ) :
    IsProgressiveLocL1 A.P F.ℱ
      (fp81s21_moving_bdE p R hH L p.s A.P F.X) := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  obtain ⟨Mb, hM1, _⟩ := fp81s21_moving_M1 p R hH hN A hstd hr hphys
  have hprog : IsProgressive F.ℱ
      (fp81s21_moving_bdE p R hH L p.s A.P F.X) := by
    unfold fp81s21_moving_bdE
    apply s102_prog_E
    intro i
    exact fp81s21_moving_bdc_progressive p R hH A.P F.X
      F.filtered.progressive hphys.density_joint L p.s i
      (s102_propagator_classical
        (hstd.hcls (s102_alk L i) _ (s102_tauk hH L i).2))
  refine ⟨hprog, fun T' => ?_⟩
  filter_upwards [hM1, F.indist] with ζ hM1ζ hInd
  have hζ : ∀ t : ℝ≥0, F.X t ζ = A.X t ζ := hInd
  have hA : S102Drift C m H r ((p.d : ℝ) + 2)
      (fun u f => fp81s21_moving_r2QuadField R A u ζ f) (Mb ζ) := by
    simpa [C, m] using hM1ζ
  have hF := fp81s21_moving_transfer_drift p R hH A F Mb
    (c := c) hA hζ F.indist
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  have hcoord : ∀ i : Fin (s102_q p.d L),
      IntegrableOn (fun u => fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ)
        (Icc (0 : ℝ) H) := by
    intro i
    have hh := s102_hh_integrableOn hP hstd.hD hF
      (s102_tauk hH L) (s102_alk L) i
    have hconst := hh.const_mul (-(Real.sqrt N)⁻¹)
    refine IntegrableOn.congr_fun hconst (fun u hu => ?_) measurableSet_Icc
    simp [fp81s21_moving_bdc, hu]
  have hglob : ∀ i : Fin (s102_q p.d L),
      Integrable (fun u => fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ) := by
    intro i
    have hinter : Integrable ((Icc (0 : ℝ) H).indicator
        (fun u => fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ)) :=
      (integrable_indicator_iff measurableSet_Icc).2 (hcoord i)
    have heq : (fun u => fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ) =
        (Icc (0 : ℝ) H).indicator
          (fun u => fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ) := by
      funext u
      by_cases hu : u ∈ Icc (0 : ℝ) H
      · simp [hu]
      · simp [fp81s21_moving_bdc, hu]
    rw [heq]
    exact hinter
  have hglobOn : ∀ i : Fin (s102_q p.d L),
      IntegrableOn (fun u => fp81s21_moving_bdc p R hH L p.s A.P F.X i u ζ)
        (Icc (0 : ℝ) T') := fun i => (hglob i).integrableOn
  exact s102_integrableOn_E _ hglobOn

#print axioms HRS.Fp81.S21.fp81s21_moving_bdE_locL1

end HRS.Fp81.S21

end
