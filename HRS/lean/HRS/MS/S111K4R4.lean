import HRS.MS.S111K4R3

/-!
# S11.1 / V02 (S11K4), Pro `R26-T6C.V07` (part): the cross-covariance density on `[0,u]` and the shift-split of `r`-integrals
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

/-- For `0 ≤ r ≤ t` and a response `h` of `U^{r,t}φ`: the density `ρh` represents the covariance functional. -/
theorem k4_cross_core (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) {h : Euc d → ℝ}
    (hresp : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ) h)
    (hhm : MemLp h 2 (HRS.Whole.withDensityReal ρ)) {ψ : Euc d → ℝ} (hψ : IsOscTest (wholeSpaceIndex d) ψ) :
    Integrable (fun x => ψ x * (ρ x * h x)) ∧
      ∫ x, ψ x * (ρ x * h x) = linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) r t ψ φ := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hex := HRS.MS.S111X1.exist_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨g, hg⟩ := hex t (hr.trans hrt) φ hφ
  have hmean : ∫ x, h x ∂μ = 0 := hresp.1.2
  have hpsiL : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → MemLp ψ 2 μ := fun ψ hψ =>
    HRS.MS.S111X1.x1_osc_memLp T.en.K.meas T.en.K.nonneg T.en.K.bdd hψ
  have hhi : ∀ ψ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * h x) μ := fun ψ hψ =>
    (hpsiL ψ hψ).integrable_mul hhm
  have hρh : Integrable (fun x => ψ x * (ρ x * h x)) := by
    have := (tc2_integrable_nu T.prob _).1 (hhi ψ hψ)
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only; ring)
  refine ⟨hρh, ?_⟩
  rw [k4_lgc_eq hd s a β hs0 hs ha hβ ρ hρ hr hrt hψ hφ]
  have hri : HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ) =ᵐ[μ] h := by
    have hex' : ∃ u, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ) u := ⟨h, hresp⟩
    have hr' : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ)
        (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ)) := by
      unfold HRS.Whole.responseInverse
      rw [dif_pos hex']
      exact hex'.choose_spec
    exact T.uniq _ _ _ hr' hresp
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  have e1 : ∫ x, HRS.Whole.projMean μ ψ x *
        HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (propagatorW C r t φ) x ∂μ =
      ∫ x, HRS.Whole.projMean μ ψ x * h x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hri] with x hx
    rw [hx]
  rw [e1]
  have e2 : ∀ x, HRS.Whole.projMean μ ψ x * h x = ψ x * h x - HRS.Whole.pair μ ψ * h x := fun x => by
    simp only [HRS.Whole.projMean]; ring
  simp_rw [e2]
  rw [integral_sub (hhi ψ hψ) ((hhm.integrable (by norm_num)).const_mul _), integral_const_mul, hmean, mul_zero,
    sub_zero, tc2_integral_nu T.prob]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- Identification of the cross-covariance density on `0 ≤ r ≤ t` (extends `k4_cross_density_ident` to `r = 0`). -/
theorem k4_cross_ident0 (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d) φ) {h : Euc d → ℝ}
    (hresp : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
      (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ) h)
    (hhm : MemLp h 2 (HRS.Whole.withDensityReal ρ)) {χ : Euc d → ℝ}
    (hχi : ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) ψ → Integrable (fun x => ψ x * χ x))
    (hχ : ∀ ψ : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) ψ →
      ∫ x, ψ x * χ x = linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) r t ψ φ) :
    χ =ᵐ[volume] fun x => ρ x * h x :=
  HRS.MS.S21E.s21e_chi_ae_eq (wholeSpaceIndex d) hχi
    (fun ψ hψ => (k4_cross_core hd s a β hs0 hs ha hβ ρ hρ hr hrt hφ hresp hhm hψ).1)
    (fun ψ hψ => by
      rw [hχ ψ hψ, (k4_cross_core hd s a β hs0 hs ha hβ ρ hρ hr hrt hφ hresp hhm hψ).2])

/-- Splitting an `r`-integral over `[0,u+τ]` at `u`, the second part being a shift of a window-`0` integrand. -/
theorem k4_split_shift {G G' : ℝ → ℝ} {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (hG : IntegrableOn G (Icc 0 u)) (hG' : IntegrableOn G' (Icc 0 τ))
    (heq : ∀ r ∈ Ioc u (u + τ), G r = G' (r - u)) :
    IntegrableOn G (Icc 0 (u + τ)) ∧
      ∫ r in Icc 0 (u + τ), G r = (∫ r in Icc 0 u, G r) + ∫ a in Icc 0 τ, G' a := by
  have hII : IntervalIntegrable G' volume 0 τ := (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).2 hG'
  have h2 : IntervalIntegrable (fun x => G' (x - u)) volume (0 + u) (τ + u) := hII.comp_sub_right u
  rw [zero_add, add_comm τ u] at h2
  have h3 : IntegrableOn (fun x => G' (x - u)) (Ioc u (u + τ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 h2
  have h4 : IntegrableOn G (Ioc u (u + τ)) := h3.congr_fun (fun r hr => (heq r hr).symm) measurableSet_Ioc
  have hU : Icc (0 : ℝ) (u + τ) = Icc 0 u ∪ Ioc u (u + τ) := (Icc_union_Ioc_eq_Icc hu (by linarith)).symm
  have hdisj : Disjoint (Icc (0 : ℝ) u) (Ioc u (u + τ)) :=
    disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  rw [hU]
  refine ⟨hG.union h4, ?_⟩
  rw [setIntegral_union hdisj measurableSet_Ioc hG h4]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioc heq, ← intervalIntegral.integral_of_le (show u ≤ u + τ by linarith),
    intervalIntegral.integral_comp_sub_right G' u, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hτ]
  simp

end HRS.MS.S111K4
