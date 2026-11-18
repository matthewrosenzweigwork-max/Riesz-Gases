import HRS.MS.Fp81S21WeightedMoments6
import HRS.MS.Fp81S21WeightedGenAdj

/-! Jointly measurable adjoints of bounded weighted-generator primal families. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The adjoint family is jointly measurable, retains the primal norm bound,
and acts on every input test by the weighted chart pairing. -/
theorem fp81s21_b3_adjoint
    {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (A : ℝ) (T : ℝ → fp81s21_F →L[ℝ] fp81s21_F)
    (hT : fp81s21_primal R Es E A T)
    (hm : ∀ j, Measurable (fun u : ℝ =>
      Es.encode
        (generatorW (r26t3_coeff R) (max u 0) (E.test j)))) :
    Measurable (fun uz : ℝ × fp81s21_F => (T uz.1).adjoint uz.2) ∧
    ∀ u, ‖(T u).adjoint‖ ≤ A ∧
      ∀ z f, fp81s21_Input p f →
        fp81s21_chartAction E ((T u).adjoint z) f =
          fp81s21_chartAction Es z
            (generatorW (r26t3_coeff R) (max u 0) f) := by
  letI : TopologicalSpace.SeparableSpace fp81s21_F :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology fp81s21_F :=
    UniformSpace.secondCountable_of_separable fp81s21_F
  have hP : (p.d : ℝ) < 2 * fp81s21_P p := by
    dsimp [fp81s21_P]
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  have htestInput (j : ℕ) : fp81s21_Input p (E.test j) := by
    change IsR2WeightedTest (fp81s21_q p + 2) (fp81s21_P p) (E.test j)
    exact (weightedTestSubmodule_iff).1
      (weighted_test_of_compact_smooth
        (r := fp81s21_q p + 2) (Pw := fp81s21_P p) hP
        (E.test_smooth j))
  let L : ℝ × fp81s21_F → fp81s21_F :=
    fun uz => (T uz.1).adjoint uz.2
  have hcoords : ∀ j, Measurable (fun uz : ℝ × fp81s21_F => L uz j) := by
    intro j
    let g : ℝ → fp81s21_F := fun u =>
      Es.encode
        (generatorW (r26t3_coeff R) (max u 0) (E.test j))
    have hg : Measurable g := by
      simpa [g] using hm j
    have hpairs : Measurable (fun uz : ℝ × fp81s21_F => (uz.2, g uz.1)) :=
      Measurable.prodMk measurable_snd (hg.comp measurable_fst)
    have hinner : Measurable (fun uz : ℝ × fp81s21_F =>
        inner ℝ uz.2 (g uz.1)) :=
      (continuous_fst.inner continuous_snd).measurable.comp hpairs
    have hformula : (fun uz : ℝ × fp81s21_F => L uz j) =
        (fun uz => inner ℝ uz.2 (g uz.1)) := by
      funext uz
      change ((T uz.1).adjoint uz.2) j =
        inner ℝ uz.2
          (Es.encode
            (generatorW (r26t3_coeff R) (max uz.1 0) (E.test j)))
      rw [fp81s21_adjoint_test_coordinate]
      rw [(hT uz.1).2 (E.test j) (htestInput j)]
    rw [hformula]
    exact hinner
  have hmeas : Measurable L := fp81s21_coeff_measurable L hcoords
  refine ⟨?_, ?_⟩
  · exact hmeas
  · intro u
    refine ⟨?_, ?_⟩
    · rw [fp81s21_adjoint_opNorm_eq]
      exact (hT u).1
    · intro z f hf
      change inner ℝ ((T u).adjoint z) (E.encode f) =
        inner ℝ z
          (Es.encode (generatorW (r26t3_coeff R) (max u 0) f))
      rw [ContinuousLinearMap.adjoint_inner_left]
      rw [(hT u).2 f hf]

#print axioms HRS.Fp81.S21.fp81s21_b3_adjoint

end HRS.Fp81.S21
