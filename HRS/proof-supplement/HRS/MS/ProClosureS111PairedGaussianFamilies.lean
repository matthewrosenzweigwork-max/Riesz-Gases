import HRS.MS.ProClosureS111GaussianLaw
import HRS.MS.S111BDAux4

/-!
The actual frozen mixed law, transported from its Euclidean Fin-indexed
vectors to arbitrary finite coordinate spaces. The paired native-test
specialization supplies the exact joint centered Gaussian hypothesis of
the accepted full-kernel Wick difference theorem S111K4J.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111X1

variable {d : ℕ} {Omega : Type} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {s a beta gamma H : ℝ} {rho : Euc d → ℝ}
variable {Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)}

/-- Every finite mixed observation vector has a genuinely centered Gaussian
law in the ordinary finite product space, not only in a chosen enumeration. -/
theorem shared_finite_observation_gaussian
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    {J : Type*} [Fintype J] (side : J → Fin 2) (ts : J → ℝ)
    (test : J → oscSub d (wholeSpaceIndex d))
    (hts : ∀ j, ts j ∈ Icc (0 : ℝ) H) :
    HRS.IsCenteredGaussian (P.map (fun w j =>
      OscDual.eval (Z (side j) (ts j) w) (test j : Euc d → ℝ))) := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let V : Omega → EuclideanSpace ℝ (Fin (Fintype.card J)) := fun w =>
    WithLp.toLp 2 (fun i => OscDual.eval (Z (side (e.symm i)) (ts (e.symm i)) w)
      (test (e.symm i) : Euc d → ℝ))
  have hVm : Measurable V := by
    refine (WithLp.measurable_toLp 2 (Fin (Fintype.card J) → ℝ)).comp
      (measurable_pi_iff.2 fun i => ?_)
    have hm := (gaussianOscEval (test (e.symm i))).continuous.measurable.comp
      ((hZ.evolution (side (e.symm i))).meas (ts (e.symm i)))
    have he : (fun w => OscDual.eval (Z (side (e.symm i)) (ts (e.symm i)) w)
        (test (e.symm i) : Euc d → ℝ)) =
        (gaussianOscEval (test (e.symm i))) ∘
          Z (side (e.symm i)) (ts (e.symm i)) := by
      funext w
      exact (gaussianOscEval_apply (test (e.symm i)) _).symm
    rw [he]
    exact hm
  have hcenter : HRS.IsCenteredGaussian (P.map V) := by
    change HRS.IsCenteredGaussian (P.map (fun w =>
      (WithLp.toLp 2 (fun i =>
        OscDual.eval (Z (side (e.symm i)) (ts (e.symm i)) w)
          (test (e.symm i) : Euc d → ℝ)) : EuclideanSpace ℝ (Fin (Fintype.card J)))))
    rw [hZ.joint (Fintype.card J) (fun i => side (e.symm i))
      (fun i => ts (e.symm i)) (fun i => (test (e.symm i) : Euc d → ℝ))
      (fun i => hts (e.symm i)) (fun i => (test (e.symm i)).property)]
    exact HRS.MS.S111BD.s111_isCenteredGaussian_mvg (Fintype.card J) _
  let ell : EuclideanSpace ℝ (Fin (Fintype.card J)) →L[ℝ] (J → ℝ) :=
    ContinuousLinearMap.pi fun j => EuclideanSpace.proj (e j)
  have he : (fun w j => OscDual.eval (Z (side j) (ts j) w) (test j : Euc d → ℝ)) =
      ell ∘ V := by
    funext w j
    simp [ell, V, Function.comp_def]
  rw [he, ← Measure.map_map ell.continuous.measurable hVm]
  letI : IsGaussian (P.map V) := hcenter.1
  refine ⟨inferInstance, fun L => ?_⟩
  rw [integral_map ell.continuous.measurable.aemeasurable L.continuous.aestronglyMeasurable]
  exact hcenter.2 (L.comp ell)

/-- The exact finite pair law required by accepted k4_wick_difference_L2.
Both sides and all their linear combinations belong to one Gaussian vector. -/
theorem shared_paired_test_gaussian
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) {n : ℕ}
    (test : Fin n → oscSub d (wholeSpaceIndex d)) :
    HRS.IsCenteredGaussian (P.map (fun w (i : Fin 2 × Fin n) =>
      if i.1 = 0 then OscDual.eval (Z 0 t w) (test i.2 : Euc d → ℝ)
      else OscDual.eval (Z 1 t w) (test i.2 : Euc d → ℝ))) := by
  have h := shared_finite_observation_gaussian hZ
    (fun i : Fin 2 × Fin n => i.1) (fun _ => t) (fun i => test i.2) (fun _ => ht)
  have he : (fun w (i : Fin 2 × Fin n) =>
      OscDual.eval (Z i.1 t w) (test i.2 : Euc d → ℝ)) =
      fun w (i : Fin 2 × Fin n) =>
        if i.1 = 0 then OscDual.eval (Z 0 t w) (test i.2 : Euc d → ℝ)
        else OscDual.eval (Z 1 t w) (test i.2 : Euc d → ℝ) := by
    funext w i
    rcases i with ⟨j, k⟩
    fin_cases j <;> simp
  rwa [he] at h

#print axioms shared_finite_observation_gaussian
#print axioms shared_paired_test_gaussian

end HRS.MS.ProClosureS111
