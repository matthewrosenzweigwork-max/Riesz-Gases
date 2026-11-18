import HRS.MS.ShiftFldAux19

/-!
# S79P: the Lyapunov identity in `L²(μ)` (part 2): `U(L u) = -β⁻¹ (I + βK) a_u`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

theorem s79g_U_L (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    [IsProbabilityMeasure (thermalMeasure d s a β)]
    {K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β)}
    (hK : S45.IsKData (thermalMeasure d s a β) (rieszKernel d s) K)
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) (hLc : Continuous (generatorW (Cst d s a β) 0 u))
    (hAm : MemLp (Aop d s a β (thermalDensity d s a β) u) 2 (thermalMeasure d s a β))
    (hLm : MemLp (generatorW (Cst d s a β) 0 u) 2 (thermalMeasure d s a β)) :
    S45.s45_U (generatorW (Cst d s a β) 0 u) hLm =
      (-β⁻¹) • (hAm.toLp _ + β • K (hAm.toLp _)) := by
  set A := Aop d s a β (thermalDensity d s a β) u with hA
  set a' : Lp ℝ 2 (thermalMeasure d s a β) := hAm.toLp A with ha'
  have hac : HRS.Whole.Q34.Pc (thermalMeasure d s a β) a' = a' := by
    refine (S45.s45_centered_iff a').2 ?_
    rw [integral_congr_ae (MemLp.coeFn_toLp hAm)]
    exact s79g_centered hd hs.le hsd ha hβ hρ hu
  have hKa := hK.kop a' hac
  set Kt : Euc d → ℝ := fun x => ∫ y, rieszKernel d s (x - y) * A y ∂(thermalMeasure d s a β) with hKt
  have hKt_eq : ∀ x, Kt x = ∫ y, rieszKernel d s (x - y) * (thermalDensity d s a β y * A y) := by
    intro x
    obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs.le hsd ha hβ
    show ∫ y, rieszKernel d s (x - y) * A y ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) = _
    rw [HRS.Whole.S79.s79_integral_withDensityReal hT.prob]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hKopeq : ∀ x, ∫ y, rieszKernel d s (x - y) * (a' : Euc d → ℝ) y ∂(thermalMeasure d s a β) = Kt x := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hAm] with y hy
    rw [hy]
  have hKop : HRS.Whole.Kop (rieszKernel d s) (thermalMeasure d s a β) (a' : Euc d → ℝ) = fun x => Kt x - ∫ x', Kt x' ∂(thermalMeasure d s a β) := by
    funext x
    unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
    simp only [hKopeq]
  have hL : ∀ᵐ x ∂(thermalMeasure d s a β), generatorW (Cst d s a β) 0 u x = -(β⁻¹ * A x) - Kt x := by
    have hvol := s79g_L_eq hd hs hsd ha hβ hρ hu hLc
    have hac2 : (thermalMeasure d s a β) ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
    filter_upwards [hac2.ae_le hvol] with x hx
    rw [hx, hKt_eq]
  have hAint : Integrable A (thermalMeasure d s a β) := hAm.integrable (by norm_num)
  have hLint : Integrable (generatorW (Cst d s a β) 0 u) (thermalMeasure d s a β) := hLm.integrable (by norm_num)
  have hKtint : Integrable Kt (thermalMeasure d s a β) := by
    have : Integrable (fun x => -(β⁻¹ * A x) - generatorW (Cst d s a β) 0 u x) (thermalMeasure d s a β) :=
      (hAint.const_mul β⁻¹).neg.sub hLint
    refine this.congr ?_
    filter_upwards [hL] with x hx
    rw [hx]; ring
  have hpair : ∫ x, generatorW (Cst d s a β) 0 u x ∂(thermalMeasure d s a β) = -∫ x, Kt x ∂(thermalMeasure d s a β) := by
    have : ∫ x, generatorW (Cst d s a β) 0 u x ∂(thermalMeasure d s a β) = ∫ x, (-(β⁻¹ * A x) - Kt x) ∂(thermalMeasure d s a β) :=
      integral_congr_ae hL
    have hneg : Integrable (fun x => -(β⁻¹ * A x)) (thermalMeasure d s a β) :=
      (hAint.const_mul β⁻¹).neg
    rw [this, integral_sub hneg hKtint, integral_neg, integral_const_mul,
      s79g_centered hd hs.le hsd ha hβ hρ hu]
    ring
  refine Lp.ext ?_
  filter_upwards [S45.s45_U_ae hLm, Lp.coeFn_smul (-β⁻¹) (a' + β • K a'),
    Lp.coeFn_add a' (β • K a'), Lp.coeFn_smul β (K a'), hKa, MemLp.coeFn_toLp hAm, hL]
    with x h1 h2 h3 h4 h5 h6 h7
  rw [h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3]
  simp only [Pi.add_apply]
  rw [h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h1]
  unfold HRS.Whole.projMean HRS.Whole.pair
  rw [h7, hpair]
  have h5' : (K a' : Euc d → ℝ) x = Kt x - ∫ x', Kt x' ∂(thermalMeasure d s a β) := by
    rw [← h5, hKop]
  rw [h5', ← h6]
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have : (a' : Euc d → ℝ) x = A x := h6
  rw [this]
  linear_combination (Kt x - ∫ x', Kt x' ∂(thermalMeasure d s a β)) * hb

end HRS.MS.S79G
