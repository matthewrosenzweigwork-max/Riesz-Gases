import HRS.MS.ShiftFldAux20

/-!
# S79P: the Lyapunov identity `C(Lu,g) + C(u,Lg) = -2β⁻¹ ∫ ρ ⟨∇u,∇g⟩`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

/-- `Γ(u,g) = ∑_i ∫ ρ ∂_i u ∂_i g`. -/
def Gam (d : ℕ) (s a β : ℝ) (u g : Euc d → ℝ) : ℝ :=
  ∑ i : Fin d, ∫ x, thermalDensity d s a β x * (D1 i u x * D1 i g x)

theorem s79g_inner_resolv {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
    {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β)
    (a w : Lp ℝ 2 ν) : ⟪a + β • K a, S45.s45_Rr hK hβ w⟫ = ⟪a, w⟫ := by
  rw [inner_add_left, real_inner_smul_left, hK.symm, ← real_inner_smul_right, ← inner_add_right]
  congr 1
  exact S45.s45_Rr_eq hK hβ w

theorem s79g_Rr_resolv {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
    {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β)
    (a : Lp ℝ 2 ν) : S45.s45_Rr hK hβ (a + β • K a) = a := by
  have := S45.s45_Rr_symm_apply hK hβ a
  rw [← this]
  exact (S45.s45_Rr hK hβ).apply_symm_apply a

theorem s79g_pair (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    [IsProbabilityMeasure (thermalMeasure d s a β)]
    {u f : Euc d → ℝ} (hu : HRS.MemCb 2 u) (hf : HRS.MemCb 2 f)
    (hAm : MemLp (Aop d s a β (thermalDensity d s a β) u) 2 (thermalMeasure d s a β))
    (hfm : MemLp f 2 (thermalMeasure d s a β)) :
    ⟪hAm.toLp _, S45.s45_U f hfm⟫ =
      ∑ i : Fin d, ∫ x, D1 i f x * (thermalDensity d s a β x * D1 i u x) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs.le hsd ha hβ
  rw [HRS.Whole.Q34.lp_inner]
  have h1 : ∫ x, (hAm.toLp _ : Euc d → ℝ) x * (S45.s45_U f hfm : Euc d → ℝ) x ∂(thermalMeasure d s a β) =
      ∫ x, Aop d s a β (thermalDensity d s a β) u x * (f x - ∫ y, f y ∂(thermalMeasure d s a β))
        ∂(thermalMeasure d s a β) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hAm, S45.s45_U_ae hfm] with x hx1 hx2
    rw [hx1, hx2]
    rfl
  rw [h1]
  have hAint : Integrable (Aop d s a β (thermalDensity d s a β) u) (thermalMeasure d s a β) :=
    hAm.integrable (by norm_num)
  have hprod : Integrable (fun x => Aop d s a β (thermalDensity d s a β) u x * f x)
      (thermalMeasure d s a β) := hAm.integrable_mul hfm
  have h2 : ∫ x, Aop d s a β (thermalDensity d s a β) u x * (f x - ∫ y, f y ∂(thermalMeasure d s a β))
        ∂(thermalMeasure d s a β) =
      ∫ x, Aop d s a β (thermalDensity d s a β) u x * f x ∂(thermalMeasure d s a β) := by
    have : ∀ x, Aop d s a β (thermalDensity d s a β) u x * (f x - ∫ y, f y ∂(thermalMeasure d s a β)) =
        Aop d s a β (thermalDensity d s a β) u x * f x -
          (∫ y, f y ∂(thermalMeasure d s a β)) * Aop d s a β (thermalDensity d s a β) u x := fun x => by ring
    simp only [this]
    rw [integral_sub hprod (hAint.const_mul _), integral_const_mul,
      s79g_centered hd hs.le hsd ha hβ hρ hu]
    ring
  rw [h2]
  show ∫ x, _ ∂(HRS.Whole.withDensityReal (thermalDensity d s a β)) = _
  rw [HRS.Whole.S79.s79_integral_withDensityReal hT.prob, ← s79g_green hd hs.le hsd ha hβ hρ hu hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

theorem s79g_lyap (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u g : Euc d → ℝ} (hu : HRS.MemCb 2 u) (hg : HRS.MemCb 2 g)
    (hLcu : Continuous (generatorW (Cst d s a β) 0 u))
    (hLbu : ∃ B : ℝ, ∀ x, |generatorW (Cst d s a β) 0 u x| ≤ B * (1 + ‖x‖))
    (hLcg : Continuous (generatorW (Cst d s a β) 0 g))
    (hLbg : ∃ B : ℝ, ∀ x, |generatorW (Cst d s a β) 0 g x| ≤ B * (1 + ‖x‖)) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β
        (generatorW (Cst d s a β) 0 u) g +
      HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β u
        (generatorW (Cst d s a β) 0 g) = -2 * β⁻¹ * Gam d s a β u g := by
  haveI := s79g_prob hd hs.le hsd ha hβ
  obtain ⟨K, hK⟩ := s79g_kdata hd hs.le hsd ha hβ
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs.le hsd ha hβ
  have hmem : ∀ {f : Euc d → ℝ}, HRS.MemCb 2 f → MemLp f 2 (thermalMeasure d s a β) := by
    intro f hf
    obtain ⟨f0, f1, f2, hf0, -, -, hb0, -, -⟩ := s79g_memcb_bounds hf
    exact s79g_memLp_lin hd hs.le hsd ha hβ hf.1.continuous (K := f0) (fun x => s79g_lin_of_le (hb0 x) x)
  have hAmem : ∀ {f : Euc d → ℝ}, HRS.MemCb 2 f →
      MemLp (Aop d s a β (thermalDensity d s a β) f) 2 (thermalMeasure d s a β) := by
    intro f hf
    obtain ⟨hc, K, hK⟩ := s79g_Aop_cont_bound hd hs.le hsd ha hβ hρ hf
    exact s79g_memLp_lin hd hs.le hsd ha hβ hc hK
  have hLu := s79g_memLp_lin hd hs.le hsd ha hβ hLcu hLbu.choose_spec
  have hLg := s79g_memLp_lin hd hs.le hsd ha hβ hLcg hLbg.choose_spec
  rw [S45.s45_susceptibilityCov_eq hK hβ hLu (hmem hg), S45.s45_susceptibilityCov_eq hK hβ (hmem hu) hLg,
    s79g_U_L hd hs hsd ha hβ hρ hK hu hLcu (hAmem hu) hLu,
    s79g_U_L hd hs hsd ha hβ hρ hK hg hLcg (hAmem hg) hLg]
  rw [map_smul, s79g_Rr_resolv hK hβ.le, real_inner_smul_left, real_inner_smul_right,
    s79g_inner_resolv hK hβ.le]
  have hpair1 := s79g_pair hd hs hsd ha hβ hρ hu hg (hAmem hu) (hmem hg)
  have hpair2 := s79g_pair hd hs hsd ha hβ hρ hg hu (hAmem hg) (hmem hu)
  rw [real_inner_comm] at hpair2
  rw [hpair1, hpair2]
  unfold Gam
  have e1 : ∀ i : Fin d, ∫ x, D1 i g x * (thermalDensity d s a β x * D1 i u x) =
      ∫ x, thermalDensity d s a β x * (D1 i u x * D1 i g x) := fun i =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  have e2 : ∀ i : Fin d, ∫ x, D1 i u x * (thermalDensity d s a β x * D1 i g x) =
      ∫ x, thermalDensity d s a β x * (D1 i u x * D1 i g x) := fun i =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  simp only [e1, e2]
  ring

end HRS.MS.S79G
