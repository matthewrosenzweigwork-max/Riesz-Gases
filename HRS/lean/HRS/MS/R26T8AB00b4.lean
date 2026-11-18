import HRS.MS.R26T8AB00a4
import HRS.MS.R26T8AB00b3

/-!
# S8.2 observed-time layer, packet T8A.B00b: an ordinary triangular parameter integral has the recent maximal bound

Packet statement `r26t8a_triangle_drift`.  Same route as `r26t8a_rectangle_drift`: `sup_t ‖Y t w‖ₑ ≤ Z₁ + Z₂` with
`Z₁ = ∫⁻‖V r r‖ₑ` over `[0,T]` and `Z₂` the integral of the clipped derivative over the triangle; the diagonal is
measurable by `b00b1`, the triangle has area `T²/2` (`b00b3`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_triangle_drift {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (T A : ℝ) (hT : 0<T) (hA : 0≤A)
    (V Vd : ℝ → ℝ → Omega → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => if p.1.2≤p.1.1 then V p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))).prod P))
    (hdm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => if p.1.2≤p.1.1 then Vd p.1.1 p.1.2 p.2 else 0)
      (((volume.restrict (Set.Icc 0 T)).prod (volume.restrict (Set.Icc 0 T))).prod P))
    (hdiag : ∀ r∈Set.Icc 0 T, MemLp (V r r) 2 P ∧ eLpNorm (V r r) 2 P≤ENNReal.ofReal A)
    (hder : ∀ r∈Set.Icc 0 T, ∀ v∈Set.Icc r T, MemLp (Vd v r) 2 P ∧ eLpNorm (Vd v r) 2 P≤ENNReal.ofReal A)
    (hFTC : ∀ᵐ p ∂((volume.restrict (Set.Icc 0 T)).prod P),
      IntegrableOn (fun v => Vd v p.1 p.2) (Set.Icc p.1 T) ∧
      ∀ t∈Set.Icc p.1 T, V t p.1 p.2=V p.1 p.1 p.2+∫ v in Set.Icc p.1 t, Vd v p.1 p.2) :
    let Y := fun t w => ∫ r in Set.Icc 0 t, V t r w
    AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
      (r26t8a_scalarSupSq P T Y)^(1/2:ℝ) ≤ ENNReal.ofReal ((T+T^2/2)*A) := by
  intro Y
  set μT : Measure ℝ := volume.restrict (Set.Icc 0 T) with hμT
  have hDm := r26t8a_b00b1_diag_meas P T hT V Vd hm hdm hFTC
  have hae : ∀ᵐ w ∂P, ∀ᵐ r ∂μT, ∀ t ∈ Set.Icc r T,
      V t r w = V r r w + ∫ v in Set.Icc r t, Vd v r w := by
    have hsw := (Measure.measurePreserving_swap (μ := P) (ν := μT)).quasiMeasurePreserving.ae hFTC
    have := Measure.ae_ae_of_ae_prod hsw
    filter_upwards [this] with w hw
    filter_upwards [hw] with r hr using hr.2
  set Z1 : Omega → ℝ≥0∞ := fun w => ∫⁻ r, ‖V r r w‖ₑ ∂μT with hZ1
  set ν3 : Measure (ℝ × ℝ) := (μT.prod μT).restrict {q : ℝ × ℝ | q.2 ≤ q.1} with hν3
  set Z2 : Omega → ℝ≥0∞ := fun w => ∫⁻ q, ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ ∂(μT.prod μT)
    with hZ2
  have hF1 : AEMeasurable (Function.uncurry fun (w : Omega) (r : ℝ) => ‖V r r w‖ₑ) (P.prod μT) :=
    hDm.prod_swap.aemeasurable.enorm
  have hF2' : AEMeasurable (Function.uncurry fun (w : Omega) (q : ℝ × ℝ) =>
      ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ) (P.prod (μT.prod μT)) :=
    hdm.prod_swap.aemeasurable.enorm
  have hF2 : AEMeasurable (Function.uncurry fun (w : Omega) (q : ℝ × ℝ) =>
      ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ) (P.prod ν3) :=
    hF2'.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hb1 : ∀ᵐ r ∂μT, ∫⁻ w, ‖V r r w‖ₑ ^ (2 : ℝ) ∂P ≤ ENNReal.ofReal A ^ (2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact r26t8a_b00a3_sq_le P _ A (hdiag r hr).1.aestronglyMeasurable (hdiag r hr).2
  have hb2 : ∀ᵐ q ∂ν3, ∫⁻ w, ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal A ^ (2 : ℝ) := by
    have hq : ∀ᵐ q ∂ν3, q ∈ {q : ℝ × ℝ | q.2 ≤ q.1} := ae_restrict_mem
      (measurableSet_le measurable_snd measurable_fst)
    have hq2 : ∀ᵐ q ∂ν3, q.1 ∈ Set.Icc (0 : ℝ) T ∧ q.2 ∈ Set.Icc (0 : ℝ) T := by
      rw [hν3]
      refine ae_restrict_of_ae ?_
      rw [hμT, Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
      exact ⟨hq.1, hq.2⟩
    filter_upwards [hq, hq2] with q hq hq2
    have hq' : q.2 ≤ q.1 := hq
    have hd := hder q.2 hq2.2 q.1 ⟨hq', hq2.1.2⟩
    simp only [if_pos hq']
    exact r26t8a_b00a3_sq_le P _ A hd.1.aestronglyMeasurable hd.2
  have hZ1bd := r26t8a_b00a3_L2 P μT hF1 (ENNReal.ofReal A) hb1
  have hZ2bd := r26t8a_b00a3_L2 P ν3 hF2 (ENNReal.ofReal A) hb2
  have hμu : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hν3u : ν3 Set.univ = ENNReal.ofReal (T ^ 2 / 2) := by
    rw [hν3, Measure.restrict_apply_univ]
    exact r26t8a_b00b3_tri_mass T hT.le
  rw [hμu] at hZ1bd
  rw [hν3u] at hZ2bd
  have hZ2eq : ∀ w, Z2 w = ∫⁻ q, ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ ∂ν3 := by
    intro w
    rw [hν3]
    refine (setLIntegral_eq_of_support_subset ?_).symm
    intro q hq
    by_contra hc
    exact hq (by simp [show ¬ q.2 ≤ q.1 from hc])
  have hZ1m : AEMeasurable Z1 P := hF1.lintegral_prod_right
  have hZ2m : AEMeasurable Z2 P := hF2'.lintegral_prod_right
  have hZ2bd' : (∫⁻ w, Z2 w ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (T ^ 2 / 2) * ENNReal.ofReal A := by
    have : ∀ w, Z2 w = ∫⁻ b, (Function.uncurry fun (w : Omega) (q : ℝ × ℝ) =>
        ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ) (w, b) ∂ν3 := hZ2eq
    simp only [this]
    exact hZ2bd
  have hs1 : ∀ᵐ w ∂P, AEStronglyMeasurable (fun r => V r r w) μT := hDm.prodMk_right
  have hs2 : ∀ᵐ w ∂P, AEStronglyMeasurable
      (fun q : ℝ × ℝ => if q.2 ≤ q.1 then Vd q.1 q.2 w else 0) (μT.prod μT) := hdm.prodMk_right
  have hfin1 := r26t8a_b00a4_fin P Z1 hZ1m _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) hZ1bd
  have hfin2 := r26t8a_b00a4_fin P Z2 hZ2m _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) hZ2bd'
  have hpt : ∀ᵐ w ∂P, (⨆ t : Set.Icc (0 : ℝ) T, ‖Y t w‖ₑ) ≤ Z1 w + Z2 w := by
    filter_upwards [hae, hs1, hs2] with w hw s1 s2
    refine iSup_le fun t => ?_
    have := r26t8a_b00b2_pt T (fun r => V r r w) (fun t r => V t r w) (fun v r => Vd v r w)
      s1.aemeasurable.enorm hw t t.2
    refine this.trans (le_of_eq ?_)
    congr 1
    exact (lintegral_prod_symm (fun q : ℝ × ℝ => ‖if q.2 ≤ q.1 then Vd q.1 q.2 w else 0‖ₑ)
      s2.aemeasurable.enorm).symm
  refine ⟨?_, ?_⟩
  · have hY0 : Y 0 = fun _ => 0 := by
      funext w
      show ∫ r in Set.Icc (0 : ℝ) 0, V 0 r w = 0
      rw [Set.Icc_self, Measure.restrict_eq_zero.2 Real.volume_singleton, integral_zero_measure]
    have hY0m : AEMeasurable (Y 0) P := by rw [hY0]; exact aemeasurable_const
    have hGm : AEStronglyMeasurable
        (fun p : ℝ × Omega => V p.1 p.1 p.2 + ∫ r in Set.Icc 0 T, (if r ≤ p.1 then Vd p.1 r p.2 else 0))
        (μT.prod P) :=
      hDm.add (r26t8a_b00n2_mid_int P μT μT (fun v r w => if r ≤ v then Vd v r w else 0) hdm)
    refine r26t8a_b00n3_sup_meas P T Y
      (fun s w => V s s w + ∫ r in Set.Icc 0 T, (if r ≤ s then Vd s r w else 0)) hY0m hGm ?_
    filter_upwards [hae, hs1, hs2, hfin1, hfin2] with w hw s1 s2 f1 f2
    obtain ⟨h1, h2⟩ := r26t8a_b00b2_fubini T (fun r => V r r w) (fun t r => V t r w)
      (fun v r => Vd v r w) ⟨s1, f1⟩ ⟨s2, f2⟩ hw
    refine ⟨h1, fun t ht => ?_⟩
    have := h2 t ht
    simp only [hY0, zero_add]
    exact this
  · have hle : r26t8a_scalarSupSq P T Y ≤ ∫⁻ w, (Z1 w + Z2 w) ^ (2 : ℝ) ∂P := by
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
    refine (add_le_add hZ1bd hZ2bd').trans (le_of_eq ?_)
    have hT2 : (0 : ℝ) ≤ T ^ 2 / 2 := by positivity
    rw [← ENNReal.ofReal_mul hT.le, ← ENNReal.ofReal_mul hT2,
      ← ENNReal.ofReal_add (mul_nonneg hT.le hA) (mul_nonneg hT2 hA)]
    congr 1
    ring

end HRS.MS.R26T8A

end
