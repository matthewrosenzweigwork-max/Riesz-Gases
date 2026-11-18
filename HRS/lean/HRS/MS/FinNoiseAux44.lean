import HRS.MS.FinNoiseAux43

/-!
# S8.6 `finite_noise`: proof of the covariance-root cost `S86Cost` (S86b)

`s86_cost`: for `d ≥ 2`, `a, β > 0`, `m ≥ 24d + 240`, `H > 0` and every `Cin` there is `C ≥ 0` such that for every thermal
equilibrium `ρ` (necessarily `ρ₀`), `N ≥ 2`, canonical realization with the linear input, `r ∈ [0,H]` and symmetric
roots `S_ω` of the empirical covariance form and `Sb` of the reference form,
`E ∑_j ‖(S - Sb) e_j‖² ≤ C (N⁻¹ + δ_N²)`.

Route.  The chart system of `s86_charts_system` (atlas of S8.4, reconstruction operators from the Fourier synthesis with the
weighted bounds of S8.5) turns the empirical and the reference forms into sums over charts (`s86_form_chart`); the symmetric
roots are compared blockwise through Araki-Yamagami and the Hilbert-Schmidt composition bound (`s86_det_root`); each chart
contributes its relative quadratic form, whose expectation is bounded by `s86_chart_relQuad` with the moment hypotheses
supplied by the canonical realization (`s86_particle_data`); the constants `4κ/lo_j · hi_j ≤ 4κ Kr` and `∑‖R_{ji}‖² ≤ ΣR`
are independent of the realization.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.Uniform HRS.Uniform.ChartAux

variable {d : ℕ}

theorem s86_int_emp (F : Euc d → ℝ) (hF : Measurable F) {N : ℕ} (hN : 1 ≤ N) (pts : Fin N → Euc d) :
    ∫ z, F z ∂((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)) = (N : ℝ)⁻¹ * ∑ i, F (pts i) := by
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac' _ _ hF.stronglyMeasurable, smul_eq_mul]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact integrable_dirac enorm_lt_top

theorem s86_hsCov_emp {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [MeasurableSpace K] [BorelSpace K] {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (hβ : 0 < β)
    (Γ : Fin d → Euc d → K) (hΓm : ∀ a, Measurable (Γ a)) (pts : Fin N → Euc d) (x y : K) :
    hsCovForm (fun ia : Fin N × Fin d => Real.sqrt (2 / (N * β)) • Γ ia.2 (pts ia.1)) x y =
      (2 / β) * ∑ a, ∫ z, ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫ ∂((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (pts i)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : Summable fun ia : Fin N × Fin d =>
      ‖Real.sqrt (2 / (N * β)) • Γ ia.2 (pts ia.1)‖ ^ 2 := Summable.of_finite
  rw [hsCovForm_apply hsum, tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  have hinm : ∀ (w : K) (a : Fin d), Measurable fun z => ⟪Γ a z, w⟫ := fun w a => by
    have : (fun z => ⟪Γ a z, w⟫) = (innerSL ℝ w) ∘ Γ a := by
      funext z; simp [real_inner_comm]
    rw [this]
    exact (innerSL ℝ w).continuous.measurable.comp (hΓm a)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s86_int_emp (fun z => ⟪Γ a z, x⟫ * ⟪Γ a z, y⟫) ((hinm x a).mul (hinm y a)) hN pts, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [inner_smul_left, conj_trivial]
  have hsq : Real.sqrt (2 / (N * β)) * Real.sqrt (2 / (N * β)) = 2 / (N * β) :=
    Real.mul_self_sqrt (by positivity)
  calc (Real.sqrt (2 / (N * β)) * ⟪Γ a (pts i), x⟫) * (Real.sqrt (2 / (N * β)) * ⟪Γ a (pts i), y⟫)
      = (Real.sqrt (2 / (N * β)) * Real.sqrt (2 / (N * β))) * (⟪Γ a (pts i), x⟫ * ⟪Γ a (pts i), y⟫) := by
        ring
    _ = 2 / (N * β) * (⟪Γ a (pts i), x⟫ * ⟪Γ a (pts i), y⟫) := by rw [hsq]
    _ = 2 / β * ((N : ℝ)⁻¹ * (⟪Γ a (pts i), x⟫ * ⟪Γ a (pts i), y⟫)) := by
        field_simp

set_option maxHeartbeats 3200000 in
theorem s86_cost (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (Hz : ℝ) (hHz : 0 < Hz) (Cin : ℝ) :
    S86Cost d a β m Hz Cin := by
  classical
  obtain ⟨J, hJ, U, ψ, χ, lo, hi, Kr, SR, hUm, hψm, hχm, hχ1, hlo0, hKr, hhi, hlo, hle, hSR, hsys⟩ :=
    s86_charts_system hd a β ha hβ m hm Hz hHz
  obtain ⟨B, hB0, hdata⟩ := s86_feat_data hd a β ha hβ m hm Hz hHz
  set κ : ℝ := 2 / β with hκdef
  have hκ : 0 < κ := by positivity
  set S1 : ℝ := ∑' k : Lattice d, Real.sqrt (chartWeight (d + 2) k) with hS1
  set Mc : ℝ := max |Cin| (Cin ^ 2) with hMc
  have hMc0 : 0 ≤ Mc := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨16 * κ * Kr * S1 ^ 2 * Mc * SR, by positivity, ?_⟩
  intro ρ hρ N hN Ω mΩ P hP X₀ W X hreal ℱ hprog hlin r hr D hD ι hι e S Sb hS hSb
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hρeq, hρ₀⟩ := HRS.MS.S85.s85_thermal_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  set ρ : Euc d → ℝ := thermalDensity d ((d : ℝ) / 2) a β with hρdef
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q09A.measure_isProb hρ.1.1
  obtain ⟨R, hR, hRs, hRsum⟩ := hsys r hr
  obtain ⟨hFeat, hbnd⟩ := hdata ρ hρ
  have hmaxr : max r 0 = r := max_eq_left hr.1
  have hΓm : ∀ i : Fin d, Measurable (gradFeature (critCoeff d a β ρ) m Hz i r) := by
    intro i
    have := (s86_feat_cont _ hFeat hHz.le i r).measurable
    simpa [hmaxr] using this
  have hΓb : ∀ (i : Fin d) x, ‖gradFeature (critCoeff d a β ρ) m Hz i r x‖ ≤ B := by
    intro i x
    simpa [hmaxr] using hbnd i r x
  obtain ⟨hxs, g, hg, hmarg, hgL2, hvar⟩ := s86_particle_data hd ha hβ hN P X₀ W X hreal ℱ hprog ρ Cin r hr.1
    (hlin r hr)
  have hδ := s86_deltaN_nonneg d N hN1
  set δ : ℝ := deltaN d ((d : ℝ) / 2) N with hδdef
  have hcore := s86_expected_core (d + 2) (by omega) e U hUm ψ hψm χ hχm hχ1 κ hκ
    (HRS.Whole.withDensityReal ρ) (fun i => gradFeature (critCoeff d a β ρ) m Hz i r) hΓm B hΓb R hR
    hRs lo hi hlo0 hlo hle P N hN1 (fun i z => X (Real.toNNReal r) z i) hxs δ g hg hmarg Cin hgL2 hvar
    (fun z => hsCovForm (fun ia : Fin N × Fin d => Real.sqrt (2 / (N * β)) •
      gradFeature (critCoeff d a β ρ) m Hz ia.2 r (X (Real.toNNReal r) z ia.1))) S Sb D
    (fun z x y => s86_hsCov_emp hN1 β hβ (fun i => gradFeature (critCoeff d a β ρ) m Hz i r) hΓm _ x y)
    (fun x y => by rw [hD x y]; unfold featureForm; rw [hκdef]; ring) hS hSb
  -- the final arithmetic
  have hBN : |Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2 ≤ Mc * ((N : ℝ)⁻¹ + δ ^ 2) := by
    have h1 : |Cin| ≤ Mc := le_max_left _ _
    have h2 : Cin ^ 2 ≤ Mc := le_max_right _ _
    have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
    calc |Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2 = |Cin| * (N : ℝ)⁻¹ + Cin ^ 2 * δ ^ 2 := by ring
      _ ≤ Mc * (N : ℝ)⁻¹ + Mc * δ ^ 2 := add_le_add (mul_le_mul_of_nonneg_right h1 hN0)
          (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
      _ = Mc * ((N : ℝ)⁻¹ + δ ^ 2) := by ring
  have hBN0 : 0 ≤ (N : ℝ)⁻¹ + δ ^ 2 := by positivity
  have hterm : ∀ p : J × Fin d,
      ENNReal.ofReal (4 * κ / lo p.1) *
        (ENNReal.ofReal (S1 ^ 2) * ENNReal.ofReal (2 * max (hi p.1) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2))) ≤
      ENNReal.ofReal (8 * κ * Kr * S1 ^ 2 * Mc * ((N : ℝ)⁻¹ + δ ^ 2)) := by
    intro p
    have hlp := hlo0 p.1
    have hhm : max (hi p.1) 0 ≤ Kr * lo p.1 := max_le (hhi p.1) (by positivity)
    have hB1 : 0 ≤ |Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2 := by positivity
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc 4 * κ / lo p.1 * (S1 ^ 2 * (2 * max (hi p.1) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)))
        ≤ 4 * κ / lo p.1 * (S1 ^ 2 * (2 * (Kr * lo p.1) * (Mc * ((N : ℝ)⁻¹ + δ ^ 2)))) := by
          gcongr
      _ = 8 * κ * Kr * S1 ^ 2 * Mc * ((N : ℝ)⁻¹ + δ ^ 2) := by
          field_simp
          ring
  have hsumR : ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) ≤ ENNReal.ofReal SR := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hRs]
    exact ENNReal.ofReal_le_ofReal hRsum
  calc ∫⁻ z, ∑' j, ‖(S z - Sb) (e j)‖ₑ ^ 2 ∂P
      = ∫⁻ z, ∑' j, ENNReal.ofReal (‖(S z - Sb) (e j)‖ ^ 2) ∂P := by
        refine lintegral_congr fun z => tsum_congr fun j => ?_
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ 2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        (ENNReal.ofReal (4 * κ / lo p.1) *
          (ENNReal.ofReal (S1 ^ 2) *
            ENNReal.ofReal (2 * max (hi p.1) 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)))) := hcore
    _ ≤ 2 * ∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2) *
        ENNReal.ofReal (8 * κ * Kr * S1 ^ 2 * Mc * ((N : ℝ)⁻¹ + δ ^ 2)) := by
        gcongr with p
        exact hterm p
    _ = 2 * ((∑' p : J × Fin d, ENNReal.ofReal (‖R p.1 p.2‖ ^ 2)) *
        ENNReal.ofReal (8 * κ * Kr * S1 ^ 2 * Mc * ((N : ℝ)⁻¹ + δ ^ 2))) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ 2 * (ENNReal.ofReal SR * ENNReal.ofReal (8 * κ * Kr * S1 ^ 2 * Mc * ((N : ℝ)⁻¹ + δ ^ 2))) := by
        gcongr
    _ = ENNReal.ofReal (16 * κ * Kr * S1 ^ 2 * Mc * SR * ((N : ℝ)⁻¹ + δ ^ 2)) := by
        rw [← ENNReal.ofReal_mul hSR, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end HRS.MS.FinNoise
