import HRS.MS.S82WA05
import HRS.MS.R26T8AA09a2
import HRS.MS.R26T8AB07b1
import HRS.MS.R26T8AD00

/-!
# S8.2 observed-time layer, packet T8A.A09: exact centered normal form and graph-domain identity

`r26t8a_centered_identity_of_aSource` is the packet statement with the two additional hypotheses `0 ≤ M`, `0 ≤ A`
(needed by the merged envelope lemmas; `A ≥ 0` is automatic) and the integrability `haS` of the linear source
`∑ i, aSource f (Y i)` under the canonical law.  `haS` is genuinely needed: a `PairCorrector` only sees the doubly
centered source `HSource f` (poisson field), never the row mean `aSource f`, so nothing in the hypotheses of the packet
controls `∑ aSource f (Y i)`; when it is not integrable the Bochner centering constants in `scalarForcing` and in
`zetaActual` are junk and the constants of the identity need not match.  `r26t8a_centered_identity_of_testBound` is the statement
under `TestBound (testOrder d) A0 f`, which bounds `aSource f` uniformly (B07a1').

The proof follows the merged `normal_form_bound` but without any pin or moment hypothesis: closure of `correctedQ` from the
polynomial pole envelope (`w_pairstat_env` and `gibbs_graph_closure`), integrability of the error statistic from A09a2.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_centered_identity_of_aSource (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hA : 0 ≤ A) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ)
    (hQ : PairCorrector a beta rho M A f (Psi f))
    (haS : Integrable (fun Y : EucConfig d N => ∑ i, aSource (HRS.Whole.withDensityReal rho) f (Y i))
      (canonicalP d N a beta)) :
    GeneratorClosure a beta (r26t8a_correctedQ (N := N) a beta Psi f)
      (fun X => -scalarForcing a beta rho f X + r26t8a_correctedD a beta rho Psi f X) ∧
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      scalarForcing a beta rho f X =
        -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
          (r26t8a_correctedQ a beta Psi f) X + r26t8a_correctedD a beta rho Psi f X := by
  classical
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.MS.S82W.w_mu_prob hd ha hbeta hrho
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) :=
    HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  set P := canonicalP d N a beta with hP
  set c1 : ℝ := ∫ Y, pairStatistic (Psi f) Y ∂P with hc1
  obtain ⟨hFcd, A', M'', hA', hM'', hbF⟩ := HRS.MS.S82W.w_pairstat_env (N := N) hd hM hQ hA c1
  have hcQ : correctedQ (N := N) a beta Psi f = fun X => pairStatistic (Psi f) X - c1 := rfl
  have hFcd0 : ContDiffOn ℝ 2 (fun X : EucConfig d N => pairStatistic (Psi f) X)
      (eucCollisionSet d N)ᶜ := by
    have := hFcd.add (contDiffOn_const (c := c1))
    simpa using this
  obtain ⟨hclos, hmean⟩ := gibbs_graph_closure d N hd hN a beta ha hbeta
    (correctedQ (N := N) a beta Psi f) (by rw [hcQ]; exact hFcd) M'' A' hM'' hA'
    (fun X hX => hbF X hX)
  have hLmem := hclos.2.1
  have hA02 := HRS.MS.S82V.s82v_lifted_pair_generator d N hd hN a beta M A ha hbeta rho hrho f (Psi f) hQ
  have hErr := (r26t8a_a09a2_err_memLp d N hd hN a beta M A ha hbeta hM hA rho hrho f (Psi f)
    hQ).integrable one_le_two
  have hident := HRS.MS.S82W.w_forcing_identity hd hN hFcd0 hA02 hErr hLmem hmean haS
  have hae0 : ∀ᵐ X ∂P, X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  refine ⟨?_, hident⟩
  refine HRS.MS.S82W.w_closure_congr hclos ?_
  filter_upwards [hae0] with X hX
  rw [hident X hX]; ring

theorem r26t8a_centered_identity_of_testBound (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta M A A0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hA : 0 ≤ A) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (f : Euc d → ℝ) (hA0 : 0 ≤ A0)
    (hf : TestBound (testOrder d) A0 f)
    (hQ : PairCorrector a beta rho M A f (Psi f)) :
    GeneratorClosure a beta (r26t8a_correctedQ (N := N) a beta Psi f)
      (fun X => -scalarForcing a beta rho f X + r26t8a_correctedD a beta rho Psi f X) ∧
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      scalarForcing a beta rho f X =
        -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
          (r26t8a_correctedQ a beta Psi f) X + r26t8a_correctedD a beta rho Psi f X := by
  classical
  obtain ⟨C0, hC0, hCb⟩ := r26t8a_b07a1_int_bound' d hd a beta ha hbeta
  obtain ⟨hprob, hbnd⟩ := hCb rho hrho
  haveI := hprob
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) :=
    HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  refine r26t8a_centered_identity_of_aSource d N hd hN a beta M A ha hbeta hM hA rho hrho Psi f hQ ?_
  have hsm : StronglyMeasurable (fun x => ∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho)) :=
    (r26t8a_b07b1_hmeas f).stronglyMeasurable.integral_prod_right'
  have ham : Measurable (aSource (HRS.Whole.withDensityReal rho) f) := by
    unfold aSource
    exact (hsm.measurable).const_mul _
  have hab : ∀ x, |aSource (HRS.Whole.withDensityReal rho) f x| ≤ A0 * C0 := fun x => by
    have h1 := (hbnd f A0 hA0 hf x).2
    rw [Real.norm_eq_abs] at h1
    unfold aSource
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : 0 ≤ A0 * C0 := mul_nonneg hA0 hC0
    have h2 : |∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho)| ≤ A0 * C0 := h1
    nlinarith [abs_nonneg (∫ y, hSource f x y ∂(HRS.Whole.withDensityReal rho))]
  refine Integrable.of_bound (C := N * (A0 * C0)) ?_ (Eventually.of_forall fun Y => ?_)
  · exact (Finset.measurable_sum _ fun i _ => ham.comp (measurable_pi_apply i)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    calc |∑ i, aSource (HRS.Whole.withDensityReal rho) f (Y i)|
        ≤ ∑ i, |aSource (HRS.Whole.withDensityReal rho) f (Y i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, A0 * C0 := Finset.sum_le_sum fun i _ => hab _
      _ = N * (A0 * C0) := by simp

end HRS.MS.R26T8A
