import HRS.MS.ProClosureS111ChartWickAllTests
import HRS.MS.ProClosureS111KernelContraction

/-!
The physical linear coefficient field acts on every finite weighted test.
Its covariance with every terminal Gaussian observation is the pairing
with the original frozen cross-density.  No measurability in the time
parameter is added to that cross-density predicate.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111X1

variable {d r : ℕ} {Pw : ℝ}

/-- Absolute integrability in the relative-density pairing gives the raw
Lebesgue integral required by the frozen covariance source formula. -/
theorem cross_density_single_integrable (rho chi f : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho) (hpos : ∀ x, 0 < rho x)
    (hi : Integrable (fun x => f x * (chi x / rho x))
      (HRS.Whole.withDensityReal rho)) :
    Integrable (fun x => f x * chi x) volume := by
  have hm : Measurable (fun x => ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp hrho.measurable
  unfold HRS.Whole.withDensityReal at hi
  have hw := (integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).1 hi
  refine hw.congr (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hrho.nonneg x), smul_eq_mul]
  have hx : rho x ≠ 0 := ne_of_gt (hpos x)
  field_simp

/-- This theorem extends the actual countable chart coordinates, rather
than choosing a new random functional for each test. The finite sections
converge both in coefficient l2 and in physical spatial L2. -/
theorem physical_chart_linear_cross_density_all_tests (hd : 2 ≤ d)
    {s a beta gamma T u H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hu : 0 ≤ u)
    (hH : u + T ≤ H) (hr : (2 : ℝ) + (d : ℝ) / 2 < r)
    (hP : (d : ℝ) < 2 * Pw) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    (E : r26t6_WeightedChart d r Pw) (side : Fin 2)
    (tau : Fin 3 → Icc (0 : ℝ) T) (phi : Fin 3 → Euc d → ℝ)
    (hphi : ∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (phi i))
    (chi : Fin 3 → ℝ → Euc d → ℝ)
    (hchi : IsR2CrossDensities d s a beta (r26t6_preparation beta gamma side)
      rho T u tau phi chi)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (u + T))
    (q : Omega → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, (fun w => q w j) =ᵐ[P]
      (fun w => OscDual.eval (Z side t w) (E.test j))) :
    ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f → ∀ k : Fin 3,
      Integrable (fun x => f x * chi k t x) volume ∧
      Integrable (fun w => inner ℝ (q w) (E.encode f) *
        OscDual.eval (Z side (u + tau k) w) (phi k)) P ∧
      (∫ w, inner ℝ (q w) (E.encode f) *
        OscDual.eval (Z side (u + tau k) w) (phi k) ∂P) =
          ∫ x, f x * chi k t x := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hX : X1Input d s a beta 0 rho :=
    x1Input_of_exist hd hs0 hs ha hbeta 0 hrho
      (exist_of_thermal hd hs0 hs ha hbeta hrho)
  have htH : t ∈ Icc (0 : ℝ) H := ⟨ht.1, ht.2.trans hH⟩
  have hterm : ∀ k, u + (tau k : ℝ) ∈ Icc (0 : ℝ) H := fun k =>
    ⟨add_nonneg hu (tau k).property.1,
      (add_le_add_right (tau k).property.2 u).trans hH⟩
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators hd s a beta Pw r
    hs0 hs ha hbeta hr hP rho hrho
  obtain ⟨G, hG, hmem⟩ := physical_observation_gaussian_space Z hZ
  intro f hf k
  let X : Omega → ℝ := fun w => OscDual.eval (Z side (u + tau k) w) (phi k)
  let v : Euc d → ℝ := fun x => chi k t x / rho x
  have hX2 : MemLp X 2 P :=
    ((hG X (hmem side _ (hterm k) (phi k) (hphi k))).1).mono_exponent (by norm_num)
  have hv : MemLp v 2 mu := (hchi k t ht).1
  let c := E.encode f
  let fn : ℕ → compactSmoothSubmodule d := chartSection E c
  let Yn : ℕ → Omega → ℝ := fun n w => inner ℝ (q w) (coeffSection c n)
  let Y : Omega → ℝ := fun w => inner ℝ (q w) c
  have hfn : ∀ n, IsR2WeightedTest r Pw (fn n) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
      (show IsR2Test (fn n : Euc d → ℝ) from (fn n).property))
  have hfn2 : ∀ n, MemLp (fn n : Euc d → ℝ) 2 mu := fun n => (hOp _ (hfn n)).1
  have hf2 : MemLp f 2 mu := (hOp _ hf).1
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n => hq.inner_const _
  have hY : MemLp Y 2 P := hq.inner_const _
  have hfinite : ∀ n, (∫ w, Yn n w * X w ∂P) =
      ∫ x, (fn n : Euc d → ℝ) x * v x ∂mu := by
    intro n
    have hobs : Yn n =ᵐ[P] fun w =>
        OscDual.eval (Z side t w) (fn n : Euc d → ℝ) := by
      filter_upwards [ae_all_iff.2 hcoord] with w hw
      dsimp [Yn]
      rw [inner_coeffSection, chartSection_eval]
      exact Finset.sum_congr rfl fun j _ => by rw [hw j]
    have hfo : IsOscTest (wholeSpaceIndex d : ℝ) (fn n : Euc d → ℝ) :=
      r2Test_isOscTest _
        (show IsR2Test (fn n : Euc d → ℝ) from (fn n).property)
    have hsecond := physical_shared_observation_second hd hs0 hs ha hbeta hgamma hrho hZ
      2 (fun _ => side) ![t, u + tau k] ![(fn n : Euc d → ℝ), phi k]
      (by intro j; fin_cases j; exact htH; exact hterm k)
      (by intro j; fin_cases j; exact hfo; exact hphi k) 0 1
    calc
      _ = ∫ w, OscDual.eval (Z side t w) (fn n : Euc d → ℝ) * X w ∂P :=
        integral_congr_ae (hobs.mul (Filter.Eventually.of_forall fun _ => rfl))
      _ = linearGaussianCov (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          (HRS.Whole.susceptibilityCov (rieszKernel d s) mu
            (r26t6_preparation beta gamma side)) t (u + tau k)
            (fn n : Euc d → ℝ) (phi k) := by
        simpa [linearGaussianCov, X] using hsecond
      _ = ∫ x, (fn n : Euc d → ℝ) x * chi k t x :=
        ((hchi k t ht).2 (fn n : Euc d → ℝ) hfo).2.symm
      _ = ∫ x, (fn n : Euc d → ℝ) x * v x ∂mu := by
        symm
        rw [show (fun x => (fn n : Euc d → ℝ) x * v x) =
          (fun x => v x * (fn n : Euc d → ℝ) x) by funext x; ring]
        exact cross_density_pair_relative rho (chi k t) (fn n : Euc d → ℝ)
          hrho.1.1 hX.pos
  have hrandom := integral_mul_tendsto_of_square_error P Yn Y X hYn hY hX2
    (inner_pairing_square_tendsto P q hq c (coeffSection c) (coeffSection_tendsto c))
  have herror : Tendsto (fun n => ∫ x, ((fn n : Euc d → ℝ) x - f x) ^ 2 ∂mu)
      atTop (𝓝 0) := by
    have he := chartSection_error_tendsto E hP f hf
    have hu : Tendsto (fun n => B *
        (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal ^ 2)
        atTop (𝓝 0) := by simpa using (he.pow 2).const_mul B
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => integral_nonneg fun _ => sq_nonneg _)
      (fun n => (hOp _ (chartSection_error_weighted E hP f hf n)).2.1)
  have hspatial := integral_mul_tendsto_of_square_error mu
    (fun n => (fn n : Euc d → ℝ)) f v hfn2 hf2 hv herror
  have heq : (∫ w, Y w * X w ∂P) = ∫ x, f x * v x ∂mu := by
    apply tendsto_nhds_unique hrandom
    simpa only [hfinite] using hspatial
  refine ⟨cross_density_single_integrable rho (chi k t) f hrho.1.1 hX.pos
    (hf2.integrable_mul hv), hY.integrable_mul hX2, ?_⟩
  calc
    _ = ∫ x, f x * v x ∂mu := heq
    _ = ∫ x, f x * chi k t x := by
      rw [show (fun x => f x * v x) = (fun x => v x * f x) by funext x; ring]
      exact cross_density_pair_relative rho (chi k t) f hrho.1.1 hX.pos

/-- The exceptional set of times depends only on the field coordinates
and their sectional L2 membership, and precedes the arbitrary weighted
test quantifier. -/
theorem physical_chart_linear_cross_density_all_tests_ae (hd : 2 ≤ d)
    {s a beta gamma T u H : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hu : 0 ≤ u)
    (hH : u + T ≤ H) (hr : (2 : ℝ) + (d : ℝ) / 2 < r)
    (hP : (d : ℝ) < 2 * Pw) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : r26t6_SharedThermalLaw P s a beta gamma H rho Z)
    (E : r26t6_WeightedChart d r Pw) (side : Fin 2)
    (basis : ℕ → Euc d → ℝ) (qLin qQuad : ℝ × Omega → r26t6_Coeff)
    (hfields : r26t6_PhysicalChartFields P rho s H E basis (Z side) qLin qQuad)
    (tau : Fin 3 → Icc (0 : ℝ) T) (phi : Fin 3 → Euc d → ℝ)
    (hphi : ∀ i, IsOscTest (wholeSpaceIndex d : ℝ) (phi i))
    (chi : Fin 3 → ℝ → Euc d → ℝ)
    (hchi : IsR2CrossDensities d s a beta (r26t6_preparation beta gamma side)
      rho T u tau phi chi) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (u + T)),
      ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f → ∀ k : Fin 3,
        Integrable (fun x => f x * chi k t x) volume ∧
        Integrable (fun w => inner ℝ (qLin (t,w)) (E.encode f) *
          OscDual.eval (Z side (u + tau k) w) (phi k)) P ∧
        (∫ w, inner ℝ (qLin (t,w)) (E.encode f) *
          OscDual.eval (Z side (u + tau k) w) (phi k) ∂P) =
            ∫ x, f x * chi k t x := by
  have hle : volume.restrict (Icc (0 : ℝ) (u + T)) ≤
      volume.restrict (Icc (0 : ℝ) H) :=
    Measure.restrict_mono (Set.Icc_subset_Icc le_rfl hH) le_rfl
  filter_upwards [(coeff_field_sections_memLp (volume.restrict (Icc (0 : ℝ) H)) P qLin
    hfields.linear_measurable hfields.linear_moment).filter_mono (ae_mono hle),
    hfields.linear_coordinates.filter_mono (ae_mono hle),
    ae_restrict_mem measurableSet_Icc] with t hq hc ht
  exact physical_chart_linear_cross_density_all_tests hd hs0 hs ha hbeta hgamma hu hH
    hr hP hrho P Z hZ E side tau phi hphi chi hchi ht (fun w => qLin (t,w)) hq hc

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_chart_linear_cross_density_all_tests
#print axioms HRS.MS.ProClosureS111.physical_chart_linear_cross_density_all_tests_ae
