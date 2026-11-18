import HRS.MS.S111K4Q3

/-!
# S11.1 / T03 (S11K4), Pro `R26-T6C.P07`: the `L²(μ)` derivative of the response along a classical orbit
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X2
open HRS.Whole.Q34 (Pc)

variable {d : ℕ}

/-- The common facts: the resolvent identification of the response class along the orbit. -/
theorem k4_orbit_class (hd : 2 ≤ d) (s a β H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    {t : ℝ} (htH : H ≤ t) {φ : Euc d → ℝ} {F : ℝ → Euc d → ℝ}
    (hF : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t φ F)
    (h : ℝ → Euc d → ℝ) (hhm : ∀ q, MemLp (h q) 2 (HRS.Whole.withDensityReal ρ))
    (hresp : ∀ q ∈ Icc (0 : ℝ) H,
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (F q) (h q)) :
    ∃ R : Lp ℝ 2 (HRS.Whole.withDensityReal ρ) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal ρ),
      (∀ q ∈ Icc (0 : ℝ) H, k4_toL (HRS.Whole.withDensityReal ρ) (h q) =
        R (k4_toL (HRS.Whole.withDensityReal ρ) (F q))) ∧
      (∀ ψ r : Euc d → ℝ, MemLp ψ 2 (HRS.Whole.withDensityReal ρ) →
        HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ψ r →
        MemLp r 2 (HRS.Whole.withDensityReal ρ) →
        k4_toL (HRS.Whole.withDensityReal ρ) r = R (k4_toL (HRS.Whole.withDensityReal ρ) ψ)) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hθ : (0 : ℝ) ≤ β := hβ.le
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have key : ∀ ψ r : Euc d → ℝ, MemLp ψ 2 μ → HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) μ β ψ r →
      MemLp r 2 μ → k4_toL μ r = (s111x2_Rm hK.posOp hθ).comp (Pc μ) (k4_toL μ ψ) := by
    intro ψ r hψ hr hrm
    have hu := s111x2_resp_unique hK hθ hψ hr
    have e : (s111x2_Rm hK.posOp hθ).comp (Pc μ) (k4_toL μ ψ) = s111x2_Res hK.posOp hθ (s111x2_cl hψ) := by
      rw [ContinuousLinearMap.comp_apply, s111x2_Rm_apply, s111x2_cl_eq_Pc hψ]
      rfl
    rw [e]
    apply Lp.ext
    filter_upwards [k4_toL_ae hrm, hu] with x h1 h2
    rw [h1, h2]
  refine ⟨(s111x2_Rm hK.posOp hθ).comp (Pc μ), fun q hq => ?_, key⟩
  have hψ : MemLp (F q) 2 μ := by
    obtain ⟨B0, h0⟩ := hF.bdd 0 (by norm_num)
    refine MemLp.of_bound (hF.c2 q ⟨hq.1, hq.2.trans htH⟩).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => ?_)
    have := h0 q ⟨hq.1, hq.2.trans htH⟩ x
    simpa [norm_iteratedFDeriv_zero] using this
  exact key (F q) (h q) hψ (hresp q hq) (hhm q)

/-- Pro `R26-T6C.P07`: `d/dv [h_v] = [β⁻¹ L f_v]` in `L²(μ)`. -/
theorem k4_orbit_deriv (hd : 2 ≤ d) (s a β H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    {t : ℝ} (htH : H ≤ t) {φ : Euc d → ℝ} {F : ℝ → Euc d → ℝ}
    (hF : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t φ F)
    (h : ℝ → Euc d → ℝ) (hhm : ∀ q, MemLp (h q) 2 (HRS.Whole.withDensityReal ρ))
    (hresp : ∀ q ∈ Icc (0 : ℝ) H,
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (F q) (h q))
    {v : ℝ} (hv : v ∈ Ioo 0 H) :
    HasDerivAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (h q))
      (k4_toL (HRS.Whole.withDensityReal ρ) (fun x => β⁻¹ * s111x2_L ρ (F v) x)) v := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  obtain ⟨R, hE, hkey⟩ := k4_orbit_class hd s a β H hs0 hs ha hβ ρ hρ htH hF h hhm hresp
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hF
  have hfC : ∀ r ∈ Icc (0 : ℝ) t, CbD (F r) Bf1 Bf2 := fun r hr =>
    ⟨hF.c2 r hr, fun x => (hfB r hr x).2.1, fun x => (hfB r hr x).2.2⟩
  have hfL : ∀ r ∈ Icc (0 : ℝ) t, MemLp (F r) 2 μ := fun r hr =>
    MemLp.of_bound (hF.c2 r hr).continuous.aestronglyMeasurable Bf0
      (Filter.Eventually.of_forall fun x => (hfB r hr x).1) |>.mono_exponent le_top
  obtain ⟨Af, hAf⟩ := hF.bdd_time_deriv
  have hvt : v ∈ Ioo (0 : ℝ) t := ⟨hv.1, hv.2.trans_le htH⟩
  have hvI : v ∈ Icc (0 : ℝ) t := ⟨hv.1.le, hvt.2.le⟩
  have hdf : ∀ x, ∀ r' ∈ Ioo (0 : ℝ) t, HasDerivAt (fun q => F q x)
      ((fun x => -generatorW C 0 (F r') x) x) r' := by
    intro x r' hr'
    have := hF.time_deriv x r' hr'
    rwa [s111x2_gen_auto T (hfC r' ⟨hr'.1.le, hr'.2.le⟩) r'] at this
  have hGf := s111x2_gen_memLp T (hfC v hvI)
  have hFl := s111x2_lp_hasDerivAt (μ := μ) (w := F) (w' := fun r' x => -generatorW C 0 (F r') x)
    (a := 0) (b := t) (A := Af) hvt (fun r' hr' => hfL r' ⟨hr'.1.le, hr'.2.le⟩) hGf.neg hdf
    (fun r' hr' x => by
      have := hAf r' ⟨hr'.1.le, hr'.2.le⟩ x
      rwa [s111x2_gen_auto T (hfC r' ⟨hr'.1.le, hr'.2.le⟩) r', abs_neg] at *)
    (s111x2_lin_memLp T Af)
  have hR : HasDerivAt (fun q => R (k4_toL μ (F q))) (R (k4_toL μ (fun x => -generatorW C 0 (F v) x))) v :=
    R.hasFDerivAt.comp_hasDerivAt v hFl
  have hev : (fun q => k4_toL μ (h q)) =ᶠ[nhds v] fun q => R (k4_toL μ (F q)) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with q hq
    exact hE q ⟨hq.1.le, hq.2.le⟩
  refine (hR.congr_of_eventuallyEq hev).congr_deriv ?_
  -- the value of the derivative
  obtain ⟨B1, B2, Hv⟩ : ∃ B1 B2, CbD (F v) B1 B2 := ⟨Bf1, Bf2, hfC v hvI⟩
  have hresG := s111x2_isResponse_gen T Hv
  have hLm : MemLp (fun x => β⁻¹ * s111x2_L ρ (F v) x) 2 μ := (s111x2_L_memLp T Hv).const_mul _
  have hLm' : MemLp (fun x => -β⁻¹ * s111x2_L ρ (F v) x) 2 μ := (s111x2_L_memLp T Hv).const_mul _
  have h1 := hkey (generatorW C 0 (F v)) (fun x => -β⁻¹ * s111x2_L ρ (F v) x) hGf hresG hLm'
  have h2 : k4_toL μ (fun x => -generatorW C 0 (F v) x) = -k4_toL μ (generatorW C 0 (F v)) :=
    s111x2_toLp_neg hGf
  have h3 : k4_toL μ (fun x => -(β⁻¹ * s111x2_L ρ (F v) x)) = -k4_toL μ (fun x => β⁻¹ * s111x2_L ρ (F v) x) :=
    s111x2_toLp_neg hLm
  have h4 : (fun x => -β⁻¹ * s111x2_L ρ (F v) x) = fun x => -(β⁻¹ * s111x2_L ρ (F v) x) := by
    funext x; ring
  rw [h2, map_neg, ← h1, h4, h3, neg_neg]

/-- Continuity of the response class along the orbit on the closed interval. -/
theorem k4_orbit_cont (hd : 2 ≤ d) (s a β H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    {t : ℝ} (htH : H ≤ t) {φ : Euc d → ℝ} {F : ℝ → Euc d → ℝ}
    (hF : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t φ F)
    (h : ℝ → Euc d → ℝ) (hhm : ∀ q, MemLp (h q) 2 (HRS.Whole.withDensityReal ρ))
    (hresp : ∀ q ∈ Icc (0 : ℝ) H,
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (F q) (h q))
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) H) :
    ContinuousWithinAt (fun q => k4_toL (HRS.Whole.withDensityReal ρ) (h q)) (Icc 0 H) v := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨R, hE, hkey⟩ := k4_orbit_class hd s a β H hs0 hs ha hβ ρ hρ htH hF h hhm hresp
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hF
  have hHt : Icc (0 : ℝ) H ⊆ Icc 0 t := Icc_subset_Icc le_rfl htH
  have hfL : ∀ r ∈ Icc (0 : ℝ) H, MemLp (F r) 2 μ := fun r hr =>
    MemLp.of_bound (hF.c2 r (hHt hr)).continuous.aestronglyMeasurable Bf0
      (Filter.Eventually.of_forall fun x => (hfB r (hHt hr) x).1) |>.mono_exponent le_top
  have hcont0 : ∀ x, ContinuousOn (fun q => F q x) (Icc 0 H) := by
    intro x
    have h0 := hF.cont_c2 0 (by norm_num)
    have h1 : Continuous fun r : Icc (0 : ℝ) t => iteratedFDeriv ℝ 0 (F r) x :=
      h0.comp (continuous_id.prodMk continuous_const)
    have h2 : Continuous fun r : Icc (0 : ℝ) t => F r x := by
      have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp h1
      refine this.congr fun r => ?_
      simp [iteratedFDeriv_zero_eq_comp]
    have h3 : ContinuousOn (fun q => F q x) (Icc 0 t) := continuousOn_iff_continuous_restrict.2 h2
    exact h3.mono hHt
  have hFc : ContinuousWithinAt (fun q => k4_toL μ (F q)) (Icc 0 H) v :=
    s111x2_lp_continuousWithinAt (μ := μ) (G := fun _ => Bf0) hv hfL hcont0
      (fun r' hr' x => by simpa using (hfB r' (hHt hr') x).1) (memLp_const _)
  have := (R.continuous.continuousAt.comp_continuousWithinAt hFc)
  exact this.congr (fun y hy => hE y hy) (hE v hv)

end HRS.MS.S111K4
