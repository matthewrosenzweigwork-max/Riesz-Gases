import HRS.MS.Fp81S21MovingDuality2

/-!
# HRS S2.1(iii), packet 9c: shifted mild identity

The compiled identity used below is `fp81s21_moving_orbit_zeta`.  With
`C := r26t3_coeff R` and `φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α`, its
conclusion is, verbatim,

```
∀ᵐ ζ ∂A.P, ∀ τ ∈ Icc (0 : ℝ) t,
  s102_zf A.P F.X ζ τ (propagatorW C τ t φ) =
    s102_zf A.P F.X ζ 0 (propagatorW C 0 t φ) +
      (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) *
        itoIntegral A.P F.ℱ F.Wc (s102_Ig (fun r => propagatorW C r t φ) t F.X) τ ζ +
      ∫ r in Icc (0 : ℝ) τ,
        (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
          A.P F.X r ζ (propagatorW C r t φ))
```

The shifted noise difference below is defined as the terminal Itô integral minus
the initial Itô integral, with the compiled coefficient unchanged.  The shifted
drift is initially kept as the difference of the two compiled interval
integrals; this is exactly what subtraction proves without importing an
additional interval-integrability premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole
open HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2Mt

/-- The shifted noise term obtained by subtracting the two compiled moving-orbit
Itô terms.  The coefficient is exactly `√N * (√(2β⁻¹) / N)`. -/
def fp81s21_shiftedNoiseDiff
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (b t : ℝ) (α : MultiIndex p.d) (ζ : A.Ω) : ℝ :=
  (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) *
    (itoIntegral A.P F.ℱ F.Wc
      (s102_Ig (fun r => propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) t F.X) t ζ -
     itoIntegral A.P F.ℱ F.Wc
      (s102_Ig (fun r => propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) t F.X) b ζ)

/-- Subtracting the `τ = b` identity from the `τ = t` identity in
`fp81s21_moving_orbit_zeta` gives the shifted mild representation.  The event
is allowed to depend on the fixed terminal time `t`. -/
theorem fp81s21_shifted_mild_identity
    (p : Parameters) {δ b H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hb : 0 ≤ b) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A (b + H))
    {t : ℝ} (ht : t ∈ Icc b (b + H)) (α : MultiIndex p.d) :
    ∀ᵐ ζ ∂A.P,
      s102_zf A.P F.X ζ t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) =
        s102_zf A.P F.X ζ b
            (propagatorW (r26t3_coeff R) b t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) +
          fp81s21_shiftedNoiseDiff p R A F b t α ζ +
          ((∫ r in Icc (0 : ℝ) t,
              (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
                A.P F.X r ζ
                (propagatorW (r26t3_coeff R) r t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) -
            (∫ r in Icc (0 : ℝ) b,
              (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
                A.P F.X r ζ
                (propagatorW (r26t3_coeff R) r t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α))))) := by
  classical
  have ht0 : t ∈ Icc (0 : ℝ) (b + H) :=
    ⟨le_trans hb ht.1, ht.2⟩
  have hB0 : 0 < b + H := by linarith
  have horbit := fp81s21_moving_orbit_zeta p R hδ hδh hB0 hN A F hphys ht0 α
  obtain ⟨ψ, hψ⟩ := HRS.MS.R2Interp.s102_osc_schwartz
    (wholeSpaceIndex p.d : ℝ) α
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have hφ : IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ) φ := by
    change IsOscTest ((wholeSpaceIndex p.d : ℕ) : ℝ)
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
    constructor
    · rw [← hψ]
      exact ψ.smooth ⊤
    · rw [← hψ]
      exact memOsc_schwartz ((wholeSpaceIndex p.d : ℕ) : ℝ) ψ
  have hAdj : ∃ f, IsClassicalAdjointW (r26t3_coeff R) t φ f :=
    fp81s21_adjoint_of_osc_test p R hφ ht0.1
  have hdiag : propagatorW (r26t3_coeff R) t t φ = φ :=
    (HRS.MS.R2Interp.s102_propagator_classical hAdj).terminal
  have htI : t ∈ Icc (0 : ℝ) t := ⟨ht0.1, le_rfl⟩
  have hbI : b ∈ Icc (0 : ℝ) t := ⟨hb, ht.1⟩
  filter_upwards [horbit] with ζ hζ
  have htime := hζ t htI
  have hstart := hζ b hbI
  rw [hdiag] at htime
  have hsqrt : Real.sqrt (2 * p.β⁻¹) = Real.sqrt (p.β⁻¹ * 2) := by
    congr 1
    ring
  rw [hsqrt] at htime hstart
  dsimp [fp81s21_shiftedNoiseDiff, φ]
  simp_rw [mul_comm (2 : ℝ) p.β⁻¹]
  linear_combination htime - hstart

/-- The same shifted identity holds on one probability-one event for all
rationally parametrized points `b + H q`, `q ∈ [0,1]`.  These points form a
countable dense subset of `[b,b+H]`. -/
theorem fp81s21_shifted_mild_identity_rat
    (p : Parameters) {δ b H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hb : 0 ≤ b) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    (hphys : Fp81MovingPhysicalInputs R hN A (b + H)) (α : MultiIndex p.d) :
    ∀ᵐ ζ ∂A.P, ∀ q : ℚ, q ∈ Icc (0 : ℚ) 1 →
      s102_zf A.P F.X ζ (b + H * (q : ℝ))
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) =
        s102_zf A.P F.X ζ b
            (propagatorW (r26t3_coeff R) b (b + H * (q : ℝ))
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) +
          fp81s21_shiftedNoiseDiff p R A F b (b + H * (q : ℝ)) α ζ +
          ((∫ r in Icc (0 : ℝ) (b + H * (q : ℝ)),
              (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
                A.P F.X r ζ
                (propagatorW (r26t3_coeff R) r (b + H * (q : ℝ))
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) -
            (∫ r in Icc (0 : ℝ) b,
              (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
                A.P F.X r ζ
                (propagatorW (r26t3_coeff R) r (b + H * (q : ℝ))
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α))))) := by
  have hae : ∀ q : ℚ, ∀ᵐ ζ ∂A.P,
      q ∈ Icc (0 : ℚ) 1 →
        s102_zf A.P F.X ζ (b + H * (q : ℝ))
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) =
          s102_zf A.P F.X ζ b
              (propagatorW (r26t3_coeff R) b (b + H * (q : ℝ))
                (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) +
            fp81s21_shiftedNoiseDiff p R A F b (b + H * (q : ℝ)) α ζ +
            ((∫ r in Icc (0 : ℝ) (b + H * (q : ℝ)),
                (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
                  A.P F.X r ζ
                  (propagatorW (r26t3_coeff R) r (b + H * (q : ℝ))
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) -
              (∫ r in Icc (0 : ℝ) b,
                (-(Real.sqrt N)⁻¹ * r2QuadField p.s (r26t3_mu R r)
                  A.P F.X r ζ
                  (propagatorW (r26t3_coeff R) r (b + H * (q : ℝ))
                    (oscTestFun (wholeSpaceIndex p.d : ℝ) α))))) := by
    intro q
    by_cases hq : q ∈ Icc (0 : ℚ) 1
    · have hqreal : (q : ℝ) ∈ Icc (0 : ℝ) 1 := by
        rcases hq with ⟨hq0, hq1⟩
        exact ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩
      have hqt : b + H * (q : ℝ) ∈ Icc b (b + H) := by
        constructor <;> nlinarith [hH, hqreal.1, hqreal.2]
      filter_upwards [fp81s21_shifted_mild_identity p R hδ hδh hb hH hN A F
        hphys hqt α] with ζ hζ
      exact fun _ => hζ
    · filter_upwards with ζ
      simp [hq]
  filter_upwards [ae_all_iff.2 hae] with ζ hζ q hq
  exact hζ q hq

#print axioms HRS.Fp81.S21.fp81s21_shifted_mild_identity
#print axioms HRS.Fp81.S21.fp81s21_shifted_mild_identity_rat

end HRS.Fp81.S21

end
