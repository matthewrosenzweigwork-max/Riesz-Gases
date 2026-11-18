import HRS.MS.FinNoiseAux40

/-!
# S8.6 `finite_noise`: the expected symmetric-root cost over all charts (S86b)

`s86_expected_core`: integrating the pointwise bound `s86_pointwise` over the particles (Tonelli over the charts, the
measurable relative forms `s86_relQuad_meas`, the per-chart expectation `s86_chart_relQuad`) gives
`E ∑_k ‖(S - Sb₀)e_k‖² ≤ 2 ∑_{(j,a)} ‖R_{ja}‖² (4κ/lo_j) (∑_k √d_k)² 2 max(hi_j,0) (|Cin|/N + (Cin δ)²)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Uniform HRS.Uniform.ChartAux

variable {d : ℕ}

theorem s86_emp_mass (N : ℕ) (hN : 1 ≤ N) {X : Type*} [MeasurableSpace X] (pts : Fin N → X) :
    ((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)) Set.univ ≤ 1 := by
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact le_of_eq (ENNReal.inv_mul_cancel (by exact_mod_cast (show N ≠ 0 by omega)) (by simp))

set_option maxHeartbeats 1600000 in
theorem s86_expected_core (r : ℕ) (hr : d < r) {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] {ιK : Type*} [Countable ιK] (e : HilbertBasis ιK ℝ K)
    {J : Type*} [Countable J] (U : J → Set (Euc d)) (hU : ∀ j, MeasurableSet (U j))
    (ψ : J → Euc d → Torus d) (hψ : ∀ j, Measurable (ψ j)) (χ : J → Euc d → ℝ)
    (hχm : ∀ j, Measurable (χ j)) (hχ1 : ∀ x, HasSum (fun j => χ j x ^ 2) 1)
    (κ : ℝ) (hκ : 0 < κ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (Γ : Fin d → Euc d → K) (hΓm : ∀ a, Measurable (Γ a)) (B : ℝ) (hΓb : ∀ a x, ‖Γ a x‖ ≤ B)
    (R : J → Fin d → FeatureSpace d →L[ℝ] K)
    (hR : ∀ j a x, χ j x • Γ a x = (U j).indicator
      (fun x => R j a (chartFeature (d := d) r (ψ j x))) x)
    (hRs : Summable fun p : J × Fin d => ‖R p.1 p.2‖ ^ 2)
    (lo hi : J → ℝ) (hlo0 : ∀ j, 0 < lo j)
    (hlo : ∀ j, ENNReal.ofReal (lo j) • (volume : Measure (Torus d)) ≤ (μ.restrict (U j)).map (ψ j))
    (hle : ∀ j, (μ.restrict (U j)).map (ψ j) ≤ ENNReal.ofReal (hi j) • (volume : Measure (Torus d)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → Euc d) (hxs : ∀ i, Measurable (xs i)) (δ : ℝ)
    (g : Euc d → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (Cin : ℝ)
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
    (hvar : ∀ f : Euc d → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
        ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ))
    (Sf : Ω → K →L[ℝ] K →L[ℝ] ℝ) (S : Ω → K →L[ℝ] K) (Sb0 : K →L[ℝ] K) (Df : K →L[ℝ] K →L[ℝ] ℝ)
    (hSf : ∀ ω x y, Sf ω x y = κ * ∑ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫
      ∂((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)))
    (hDf : ∀ x y, Df x y = κ * ∑ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫ ∂μ)
    (hS : ∀ ω, IsSqrtOfForm (S ω) (Sf ω)) (hSb : IsSqrtOfForm Sb0 Df) :
    ∫⁻ ω, ∑' k, ENNReal.ofReal (‖(S ω - Sb0) (e k)‖ ^ 2) ∂P ≤
      2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) *
          (ENNReal.ofReal ((∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2) *
            ENNReal.ofReal (2 * max (hi p.1) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)))) := by
  classical
  set ν : Ω → Measure (Euc d) := fun ω => (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω) with hν
  have hνfin : ∀ ω, IsFiniteMeasure (ν ω) := fun ω => isFiniteMeasure_empirical N hN (fun k => xs k ω)
  have hpt : ∀ ω, ∑' k, ENNReal.ofReal (‖(S ω - Sb0) (e k)‖ ^ 2) ≤
      2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r) (((ν ω).restrict (U p.1)).map (ψ p.1)) -
            outerCov (chartFeature (d := d) r) ((μ.restrict (U p.1)).map (ψ p.1)))) := by
    intro ω
    haveI := hνfin ω
    exact s86_pointwise r hr e U hU ψ hψ χ hχm hχ1 κ hκ μ (ν ω) (s86_emp_mass N hN _) Γ hΓm B hΓb R hR
      hRs lo hlo0 hlo (S ω) Sb0 (Sf ω) Df (hSf ω) hDf (hS ω) hSb
  have hmeasp : ∀ p : J × Fin d, Measurable fun ω => ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
      (ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r) (((ν ω).restrict (U p.1)).map (ψ p.1)) -
          outerCov (chartFeature (d := d) r) ((μ.restrict (U p.1)).map (ψ p.1)))) := fun p =>
    measurable_const.mul (measurable_const.mul
      (s86_relQuad_meas r hr μ (U p.1) (hU p.1) (ψ p.1) (hψ p.1) N hN xs hxs))
  have hchart : ∀ j, ∫⁻ ω, relQuad (hb d) (chartWeight r)
      (outerCov (chartFeature (d := d) r) (((ν ω).restrict (U j)).map (ψ j)) -
        outerCov (chartFeature (d := d) r) ((μ.restrict (U j)).map (ψ j))) ∂P ≤
      ENNReal.ofReal ((∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2) *
        ENNReal.ofReal (2 * max (hi j) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)) := fun j =>
    s86_chart_relQuad r hr μ (U j) (hU j) (ψ j) (hψ j) (hi j) (hle j) P N hN xs hxs δ g hg hmarg Cin
      hgL2 hvar
  calc ∫⁻ ω, ∑' k, ENNReal.ofReal (‖(S ω - Sb0) (e k)‖ ^ 2) ∂P
      ≤ ∫⁻ ω, 2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r) (((ν ω).restrict (U p.1)).map (ψ p.1)) -
            outerCov (chartFeature (d := d) r) ((μ.restrict (U p.1)).map (ψ p.1)))) ∂P :=
        lintegral_mono hpt
    _ = 2 * ∑' p : J × Fin d, ∫⁻ ω, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) * relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r) (((ν ω).restrict (U p.1)).map (ψ p.1)) -
            outerCov (chartFeature (d := d) r) ((μ.restrict (U p.1)).map (ψ p.1)))) ∂P := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_tsum fun p => (hmeasp p).aemeasurable]
    _ ≤ 2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) *
          (ENNReal.ofReal ((∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2) *
            ENNReal.ofReal (2 * max (hi p.1) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)))) := by
        gcongr with p
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact hchart p.1

end HRS.MS.FinNoise
