import HRS.MS.R26T8AB07a
import HRS.MS.R26T8AB07c

/-!
# S8.2 observed-time layer, packet T8A.B07b1: linearity of the source functional in the test function

`scalarForcing a beta rho` is additive on smooth test functions with bounded positive-order jets: the commutator
kernel is linear in the gradient, the integrals against `rho dx` are of integrable functions, and the centering
integral over the canonical law is of an integrable function (B07a).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b07b1_hmeas {d : ℕ} (f : Euc d → ℝ) :
    Measurable (Function.uncurry (hSource f)) := by
  have hGm : Measurable (gradient f) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  exact HRS.MS.Comm.comm_meas (s := criticalS d) (gradient f) hGm

theorem r26t8a_b07b1_hSource_sub {d : ℕ} (f1 f2 : Euc d → ℝ) (h1 : ContDiff ℝ ∞ f1)
    (h2 : ContDiff ℝ ∞ f2) :
    hSource (fun x => f1 x - f2 x) = fun x y => hSource f1 x y - hSource f2 x y := by
  have hg : ∀ z, gradient (fun x => f1 x - f2 x) z = gradient f1 z - gradient f2 z := by
    intro z
    unfold gradient
    rw [show (fun x => f1 x - f2 x) = f1 - f2 from rfl,
      fderiv_sub (h1.differentiable (by simp) z) (h2.differentiable (by simp) z), map_sub]
  funext x y
  unfold hSource commutatorKernel
  rw [hg x, hg y]
  rw [show gradient f1 x - gradient f2 x - (gradient f1 y - gradient f2 y) =
    (gradient f1 x - gradient f1 y) - (gradient f2 x - gradient f2 y) by abel, inner_sub_left]

theorem r26t8a_b07b1_cpf_sub {d N : ℕ} (g1 g2 : Euc d → Euc d → ℝ) (ν : Measure (Euc d))
    (hi1 : ∀ x, Integrable (fun y => g1 x y) ν) (hi2 : ∀ x, Integrable (fun y => g2 x y) ν)
    (ho1 : Integrable (fun x => ∫ y, g1 x y ∂ν) ν) (ho2 : Integrable (fun x => ∫ y, g2 x y ∂ν) ν)
    (X : EucConfig d N) :
    centeredPairFunctional (fun x y => g1 x y - g2 x y) X ν =
      centeredPairFunctional g1 X ν - centeredPairFunctional g2 X ν := by
  unfold centeredPairFunctional
  have e1 : ∀ x, ∫ y, (g1 x y - g2 x y) ∂ν = ∫ y, g1 x y ∂ν - ∫ y, g2 x y ∂ν :=
    fun x => integral_sub (hi1 x) (hi2 x)
  simp only [e1, integral_sub ho1 ho2, Finset.sum_sub_distrib]
  ring

theorem r26t8a_b07b1_sub (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f1 f2 : Euc d → ℝ) (A1 A2 : ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : TestBound (testOrder d) A1 f1) (h2 : TestBound (testOrder d) A2 f2) (X : EucConfig d N) :
    scalarForcing a beta rho (fun x => f1 x - f2 x) X =
      scalarForcing a beta rho f1 X - scalarForcing a beta rho f2 X := by
  classical
  obtain ⟨C0, hC0, hCb⟩ := r26t8a_b07a1_int_bound' d hd a beta ha hbeta
  obtain ⟨hprob, hbnd⟩ := hCb rho hrho
  haveI := hprob
  obtain ⟨c, K, hc, hK, hm, henv1, hL2, hE⟩ := r26t8a_b07a_explicit d N hd hN a beta ha hbeta rho hrho
  haveI hP0 : IsProbabilityMeasure (canonicalP d N a beta) :=
    HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hnull : ∀ᵐ Y ∂(canonicalP d N a beta), Y ∉ eucCollisionSet d N := by
    have := r26t8a_gibbs_pole_moments d N hd hN a beta ha hbeta (criticalS d)
      (HRS.MS.S82R.s82r_criticalS_pos (by omega)).le
    rw [ae_iff]; simpa using this.2
  have hint_env : Integrable (r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d))
      (canonicalP d N a beta) := hL2.integrable one_le_two
  -- integrability facts for a test function
  have hfacts : ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      (∀ x, Integrable (fun y => hSource f x y) (HRS.Whole.withDensityReal rho)) ∧
      Integrable (fun x => ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho))
        (HRS.Whole.withDensityReal rho) ∧
      Integrable (fun Y : EucConfig d N => centeredPairFunctional (hSource f) Y
        (HRS.Whole.withDensityReal rho)) (canonicalP d N a beta) := by
    intro f A hA hT
    have hhm := r26t8a_b07b1_hmeas f
    refine ⟨fun x => (hbnd f A hA hT x).1, ?_, ?_⟩
    · refine Integrable.of_bound (C := A * C0) ?_ (Filter.Eventually.of_forall fun x =>
        (hbnd f A hA hT x).2)
      exact (hhm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · have hDm := HRS.MS.Wr.wr14a_measurable_D (N := N) hhm (HRS.Whole.withDensityReal rho)
      refine Integrable.mono' (hint_env.const_mul (A * c)) hDm.aestronglyMeasurable ?_
      filter_upwards [hnull] with Y hY
      rw [Real.norm_eq_abs]
      exact (hE f A hA hT).1 Y hY
  obtain ⟨hi1, ho1, hP1⟩ := hfacts f1 A1 hA1 h1
  obtain ⟨hi2, ho2, hP2⟩ := hfacts f2 A2 hA2 h2
  have hsub := r26t8a_b07b1_hSource_sub f1 f2 h1.1 h2.1
  have key : ∀ Y : EucConfig d N, centeredPairFunctional (hSource (fun x => f1 x - f2 x)) Y
      (HRS.Whole.withDensityReal rho) =
      centeredPairFunctional (hSource f1) Y (HRS.Whole.withDensityReal rho) -
        centeredPairFunctional (hSource f2) Y (HRS.Whole.withDensityReal rho) := fun Y => by
    rw [hsub]; exact r26t8a_b07b1_cpf_sub _ _ _ hi1 hi2 ho1 ho2 Y
  unfold scalarForcing centerUnder
  simp only [key]
  rw [integral_sub hP1 hP2]
  ring

end HRS.MS.R26T8A
