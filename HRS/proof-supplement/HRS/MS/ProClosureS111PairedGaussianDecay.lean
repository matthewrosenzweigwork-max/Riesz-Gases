import HRS.MS.ProClosureS111ObservationMoments
import HRS.MS.S111X2Aux19

/-!
Sharp physical decay of the paired Gaussian difference. The common noise
cancels exactly on the actual constructed shared law. The remaining two
initial susceptibilities are bounded by the same physical centered orbit,
whose sharp decay is already accepted. The constant is chosen before the
density, preparation parameter, finite horizon, time, and test.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.S111T HRS.MS.R26T6

variable {d : ℕ}

/-- The deterministic variance left after the shared noise cancels has
the sharp squared exponential rate. Preparation zero and time zero need
no limiting argument. -/
theorem physical_initial_difference_variance_decay (hd : 2 ≤ d)
    (s a beta lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hlam : 0 < lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma → ∀ t : ℝ, 0 ≤ t →
      ∀ phi : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) phi →
      let f := propagatorW (r26t6_thermalCoeff d s a beta rho) 0 t phi
      HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma f f +
        HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) beta f f ≤
          A * Real.exp (-2 * (lam / beta) * t) *
            (∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) phi x ^ 2 ∂HRS.Whole.withDensityReal rho) := by
  obtain ⟨eta, heta, heta1, hsharp⟩ :=
    s111x2_sharp_decay hd s a beta lam beta hs0 hs ha hbeta hlam le_rfl
  refine ⟨2 * eta⁻¹, by positivity, fun rho hrho hP gamma hgamma t ht phi hphi => ?_⟩
  let C := r26t6_thermalCoeff d s a beta rho
  let mu := HRS.Whole.withDensityReal rho
  let f : ℝ → Euc d → ℝ := fun r => propagatorW C r t phi
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  have hf : IsClassicalAdjointW C t phi f :=
    x1_prop_classical (exist_of_thermal hd hs0 hs ha hbeta hrho t ht phi hphi)
  have hf0 : MemLp (f 0) 2 mu := x1_classical_memLp hf ⟨le_rfl, ht⟩ mu
  obtain ⟨hRF, hdec⟩ := hsharp rho hrho
  have hbetaUpper := (hRF beta ⟨hbeta.le, le_rfl⟩).coercive (f 0) hf0 |>.2
  obtain ⟨etaG, hetaG, hetaG1, hRFG⟩ :=
    s111x2_thermal_response_forms hd s a beta gamma hs0 hs ha hbeta hgamma
  have hgammaUpper := (hRFG rho hrho gamma ⟨hgamma, le_rfl⟩).coercive (f 0) hf0 |>.2
  have horbit : s111x2_centeredSquare mu (f 0) ≤
      eta⁻¹ * Real.exp (-2 * (lam / beta) * t) * s111x2_centeredSquare mu phi := by
    rcases ht.eq_or_lt with hzero | hpos
    · subst t
      have hterminal : f 0 = phi := hf.terminal
      rw [hterminal]
      simp only [mul_zero, Real.exp_zero, mul_one]
      have hinv : 1 ≤ eta⁻¹ := (one_le_inv₀ heta).2 heta1
      have hV : 0 ≤ s111x2_centeredSquare mu phi := integral_nonneg fun x => sq_nonneg _
      nlinarith
    · have h := hdec hP t hpos phi f hf t ⟨ht, le_rfl⟩
      simpa only [sub_self] using h
  change HRS.Whole.susceptibilityCov (rieszKernel d s) mu gamma (f 0) (f 0) +
    HRS.Whole.susceptibilityCov (rieszKernel d s) mu beta (f 0) (f 0) ≤ _
  calc
    _ ≤ s111x2_centeredSquare mu (f 0) + s111x2_centeredSquare mu (f 0) :=
      add_le_add hgammaUpper hbetaUpper
    _ = 2 * s111x2_centeredSquare mu (f 0) := by ring
    _ ≤ 2 * (eta⁻¹ * Real.exp (-2 * (lam / beta) * t) *
        s111x2_centeredSquare mu phi) := mul_le_mul_of_nonneg_left horbit (by norm_num)
    _ = _ := by
      unfold s111x2_centeredSquare
      ring

/-- An actual common probability law with sharp second- and fourth-moment
decay of every original oscillator observation difference. The Gaussian
law is constructed, not assumed. These are the scalar bounds used by the
paired coefficient-field construction. -/
theorem physical_shared_thermal_law_with_difference_decay (hd : 2 ≤ d)
    (s a beta lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hlam : 0 < lam) :
    ∃ A : ℝ, 0 < A ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d s a beta rho →
      IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma → ∀ H : ℝ, ∀ hH : 0 < H,
      ∃ P : Measure (PathPair d (wholeSpaceIndex d) H), IsProbabilityMeasure P ∧
        r26t6_SharedThermalLaw P s a beta gamma H rho
          (pairedProcess d (wholeSpaceIndex d) H hH.le) ∧
        ∀ t ∈ Icc (0 : ℝ) H, ∀ phi : Euc d → ℝ,
          IsOscTest (wholeSpaceIndex d) phi →
          let D : PathPair d (wholeSpaceIndex d) H → ℝ := fun w =>
            OscDual.eval (pairedProcess d (wholeSpaceIndex d) H hH.le 0 t w) phi -
            OscDual.eval (pairedProcess d (wholeSpaceIndex d) H hH.le 1 t w) phi
          let V := ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) phi x ^ 2 ∂HRS.Whole.withDensityReal rho
          MemLp D 4 P ∧
            (∫ w, D w ^ 2 ∂P) ≤ A * Real.exp (-2 * (lam / beta) * t) * V ∧
            (∫ w, D w ^ 4 ∂P) ≤ 3 * A ^ 2 * Real.exp (-4 * (lam / beta) * t) * V ^ 2 := by
  obtain ⟨A, hA, hdec⟩ := physical_initial_difference_variance_decay
    hd s a beta lam hs0 hs ha hbeta hlam
  refine ⟨A, hA, fun rho hrho hP gamma hgamma H hH => ?_⟩
  obtain ⟨P, hprob, hZ⟩ := physical_shared_thermal_law hd s a beta gamma H
    hs0 hs ha hbeta hgamma hH rho hrho
  letI : IsProbabilityMeasure P := hprob
  refine ⟨P, hprob, hZ, fun t ht phi hphi => ?_⟩
  let Z := pairedProcess d (wholeSpaceIndex d) H hH.le
  let D : PathPair d (wholeSpaceIndex d) H → ℝ := fun w =>
    OscDual.eval (Z 0 t w) phi - OscDual.eval (Z 1 t w) phi
  let V := ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal rho) phi x ^ 2 ∂HRS.Whole.withDensityReal rho
  have hV : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  obtain ⟨hD, hsecond, hfour⟩ := physical_shared_difference_moments
    hd hs0 hs ha hbeta hgamma hrho hZ ht hphi
  have hbound : (∫ w, D w ^ 2 ∂P) ≤ A * Real.exp (-2 * (lam / beta) * t) * V := by
    rw [hsecond]
    exact hdec rho hrho hP gamma hgamma t ht.1 phi hphi
  refine ⟨hD, hbound, ?_⟩
  have hexp : Real.exp (-2 * (lam / beta) * t) ^ 2 =
      Real.exp (-4 * (lam / beta) * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    (∫ w, D w ^ 4 ∂P) = 3 * (∫ w, D w ^ 2 ∂P) ^ 2 := hfour
    _ ≤ 3 * (A * Real.exp (-2 * (lam / beta) * t) * V) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (integral_nonneg fun w => sq_nonneg _) hbound 2) (by norm_num)
    _ = _ := by
      rw [mul_pow, mul_pow, hexp]
      ring

#print axioms physical_initial_difference_variance_decay
#print axioms physical_shared_thermal_law_with_difference_decay

end HRS.MS.ProClosureS111
