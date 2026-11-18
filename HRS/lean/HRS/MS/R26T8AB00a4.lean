import HRS.MS.R26T8AD01
import HRS.MS.R26T8AB00a
import HRS.MS.R26T8AB00a3

/-!
# S8.2 observed-time layer, packet T8A.B00a: an ordinary rectangle parameter integral has the anchored maximal bound

Packet statement `r26t8a_rectangle_drift` (`[0,T] × [l,h]`).  Route: the time-zero slice is measurable (`b00a1`); for a.e. sample the
FTC holds for a.e. parameter, so `sup_t ‖Y t w‖ₑ ≤ Z₁ + Z₂` with `Z₁ = ∫⁻‖V 0‖ₑ`, `Z₂ = ∫⁻∫⁻‖Vd‖ₑ` (`b00a2`); the two
`L²` norms are bounded by Minkowski (`b00a3`) and added by `ENNReal.lintegral_Lp_add_le`; measurability of the supremum
comes from the Fubini transfer and `b00n3`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_b00a4_fin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ≥0∞)
    (hZ : AEMeasurable Z P) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : (∫⁻ w, Z w ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ B) : ∀ᵐ w ∂P, Z w < ⊤ := by
  have hfin : ∫⁻ w, Z w ^ (2 : ℝ) ∂P ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at h
    exact hB (top_le_iff.mp h)
  have := ae_lt_top' (hZ.pow_const (2 : ℝ)) hfin
  filter_upwards [this] with w hw
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_rpow_of_pos (by norm_num)] at hw
  exact lt_irrefl _ hw

theorem r26t8a_rectangle_drift {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (l h T A : ℝ) (hlh : l≤h) (hT : 0<T) (hA : 0≤A)
    (V Vd : ℝ → ℝ → Omega → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => V p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))).prod P))
    (hdm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => Vd p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc l h))).prod P))
    (hzero : ∀ r∈Set.Icc l h, MemLp (V 0 r) 2 P ∧ eLpNorm (V 0 r) 2 P≤ENNReal.ofReal A)
    (hder : ∀ t∈Set.Icc 0 T, ∀ r∈Set.Icc l h, MemLp (Vd t r) 2 P ∧ eLpNorm (Vd t r) 2 P≤ENNReal.ofReal A)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc l h)).prod P),
      IntegrableOn (fun v => Vd v p.1 p.2) (Set.Icc 0 T) ∧
      ∀ t∈Set.Icc 0 T, V t p.1 p.2=V 0 p.1 p.2+∫ v in Set.Icc 0 t, Vd v p.1 p.2) :
    let Y := fun t w => ∫ r in Set.Icc l h, V t r w
    AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
      (r26t8a_scalarSupSq P T Y)^(1/2:ℝ) ≤ ENNReal.ofReal ((h-l)*(1+T)*A) := by
  intro Y
  set μT : Measure ℝ := volume.restrict (Set.Icc 0 T) with hμT
  set ν : Measure ℝ := volume.restrict (Set.Icc l h) with hν
  have hV0m := r26t8a_b00a1_V0_meas P l h T hT V Vd hm hdm hFTC
  have hae := r26t8a_b00a_ae_ftc P l h T V Vd hFTC
  -- the two dominating functions
  set Z1 : Omega → ℝ≥0∞ := fun w => ∫⁻ r, ‖V 0 r w‖ₑ ∂ν with hZ1
  set Z2 : Omega → ℝ≥0∞ := fun w => ∫⁻ q, ‖Vd q.1 q.2 w‖ₑ ∂(μT.prod ν) with hZ2
  have hF1 : AEMeasurable (Function.uncurry fun (w : Omega) (r : ℝ) => ‖V 0 r w‖ₑ) (P.prod ν) :=
    hV0m.prod_swap.aemeasurable.enorm
  have hF2 : AEMeasurable (Function.uncurry fun (w : Omega) (q : ℝ × ℝ) => ‖Vd q.1 q.2 w‖ₑ)
      (P.prod (μT.prod ν)) := hdm.prod_swap.aemeasurable.enorm
  have hb1 : ∀ᵐ r ∂ν, ∫⁻ w, ‖V 0 r w‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal A ^ (2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact r26t8a_b00a3_sq_le P _ A (hzero r hr).1.aestronglyMeasurable (hzero r hr).2
  have hb2 : ∀ᵐ q ∂(μT.prod ν), ∫⁻ w, ‖Vd q.1 q.2 w‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal A ^ (2 : ℝ) := by
    rw [hμT, hν, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    exact r26t8a_b00a3_sq_le P _ A (hder q.1 hq.1 q.2 hq.2).1.aestronglyMeasurable
      (hder q.1 hq.1 q.2 hq.2).2
  have hZ1bd := r26t8a_b00a3_L2 P ν hF1 (ENNReal.ofReal A) hb1
  have hZ2bd := r26t8a_b00a3_L2 P (μT.prod ν) hF2 (ENNReal.ofReal A) hb2
  have hνu : ν Set.univ = ENNReal.ofReal (h - l) := by
    rw [hν, Measure.restrict_apply_univ, Real.volume_Icc]
  have hμu : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hν2u : (μT.prod ν) Set.univ = ENNReal.ofReal T * ENNReal.ofReal (h - l) := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hμu, hνu]
  rw [hνu] at hZ1bd
  rw [hν2u] at hZ2bd
  have hZ1m : AEMeasurable Z1 P := hF1.lintegral_prod_right
  have hZ2m : AEMeasurable Z2 P := hF2.lintegral_prod_right
  -- slices
  have hs1 : ∀ᵐ w ∂P, AEStronglyMeasurable (fun r => V 0 r w) ν := hV0m.prodMk_right
  have hs2 : ∀ᵐ w ∂P, AEStronglyMeasurable (fun q : ℝ × ℝ => Vd q.1 q.2 w) (μT.prod ν) :=
    hdm.prodMk_right
  have hfin1 := r26t8a_b00a4_fin P Z1 hZ1m _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) hZ1bd
  have hfin2 := r26t8a_b00a4_fin P Z2 hZ2m _ (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top) hZ2bd
  -- the sample-wise bound
  have hpt : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ≤ Z1 w + Z2 w := by
    filter_upwards [hae, hs1, hs2] with w hw s1 s2
    refine iSup_le fun t => ?_
    have := r26t8a_b00a2_pt l h T (fun r => V 0 r w) (fun t r => V t r w) (fun v r => Vd v r w)
      s1.aemeasurable.enorm (hw.mono fun r hr => hr.2) t t.2
    refine this.trans (le_of_eq ?_)
    congr 1
    exact (lintegral_prod_symm (fun q : ℝ × ℝ => ‖Vd q.1 q.2 w‖ₑ) s2.aemeasurable.enorm).symm
  refine ⟨?_, ?_⟩
  · -- measurability of the supremum
    have hY0m : AEMeasurable (Y 0) P := hV0m.prod_swap.integral_prod_right'.aemeasurable
    have hGm := r26t8a_b00n2_mid_int P μT ν Vd hdm
    refine r26t8a_b00n3_sup_meas P T Y (fun v w => ∫ r in Set.Icc l h, Vd v r w) hY0m hGm ?_
    filter_upwards [hae, hs1, hs2, hfin1, hfin2] with w hw s1 s2 f1 f2
    exact r26t8a_b00a2_fubini l h T (fun r => V 0 r w) (fun t r => V t r w)
      (fun v r => Vd v r w) ⟨s1, f1⟩ ⟨s2, f2⟩ (hw.mono fun r hr => hr.2)
  · -- the bound
    have hle : r26t8a_scalarSupSq P T Y ≤ ∫⁻ w, (Z1 w + Z2 w) ^ (2 : ℝ) ∂P := by
      unfold r26t8a_scalarSupSq
      refine lintegral_mono_ae ?_
      filter_upwards [hpt] with w hw
      rw [ENNReal.rpow_two]
      gcongr
    have h1 := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2) hZ1m hZ2m (by norm_num)
    have h2 : (r26t8a_scalarSupSq P T Y) ^ (1 / 2 : ℝ) ≤
        (∫⁻ w, (Z1 w + Z2 w) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hle (by norm_num)
    refine h2.trans (h1.trans ?_)
    refine (add_le_add hZ1bd hZ2bd).trans (le_of_eq ?_)
    have hl0 : (0 : ℝ) ≤ h - l := sub_nonneg.2 hlh
    rw [← ENNReal.ofReal_mul hl0, ← ENNReal.ofReal_mul hT.le,
      ← ENNReal.ofReal_mul (mul_nonneg hT.le hl0),
      ← ENNReal.ofReal_add (mul_nonneg hl0 hA) (mul_nonneg (mul_nonneg hT.le hl0) hA)]
    congr 1
    ring

end HRS.MS.R26T8A

end
