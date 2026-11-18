import HRS.MS.R2GenInitAux12
import HRS.Main.GFB4Aux12
import HRS.Prob.HilbertBDG

/-!
# S10.5 window comparison, packet A2: the `W_1` comparison of the window martingales, uniformly in the window start

`s105_w1_abstract`: for the coupled martingales `M`, `G` of the master (difference martingale with covariation `Sd`, `‖Sd‖₁ ≤ cost`):
`W₁(Law(A(k₀) + 𝒯M_b + R), Law(A(k₀) + 𝒯G_b)) ≤ C (E∫_0^{b+T} cost)^{1/2} + E‖R‖`, `C = (3+√T) √C_BDG` independent of `b`
(Burkholder-Davis-Gundy for the difference martingale on `[0,b+T]`; no evolution is involved because the evolution is the identity).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ}

theorem s105_w1_abstract (m T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), 0 ≤ b → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (k0 : Ω → KSpace d m T),
      ∀ (M G : ℝ → Ω → KSpace d m T), (∀ t, Measurable (M t)) → (∀ t, Measurable (G t)) →
      ∀ (Sd : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)) (cost : ℝ → Ω → ℝ),
      IsHilbertMartingaleWithCovariation P ℱ (b + T) (fun τ ζ => M (min τ (b + T)) ζ - G (min τ (b + T)) ζ)
        (fun r ζ => if r ≤ b + T then Sd r ζ else 0) →
      (∀ᵐ ζ ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ b + T → traceNormForm (Sd r ζ) ≤ cost r ζ) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ) (Set.Icc 0 (b + T))) → (∀ᵐ ζ ∂P, M 0 ζ = 0) →
      (∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ) (Set.Icc 0 (b + T))) → (∀ᵐ ζ ∂P, G 0 ζ = 0) →
      ∀ (R : ℝ → Ω → OscDual d m), (∀ᵐ ζ ∂P, ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) →
      (∀ t, Measurable (R t)) → ∀ (Ξ Yh : Ω → OscPath d m T),
      (∀ᵐ ζ ∂P, Ξ ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ t + R t ζ)) →
      (∀ᵐ ζ ∂P, Yh ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t)) →
      Measurable k0 →
      wassersteinE 1 (law P Ξ) (law P Yh) ≤
        ENNReal.ofReal C * (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) +
        ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P := by
  have hT0 : 0 ≤ T := hT.le
  obtain ⟨Cb, hCb0, hCb⟩ := HilbertBDG.hilbert_bdg 2 le_rfl
  refine ⟨(3 + Real.sqrt T) * Real.sqrt Cb, by positivity, ?_⟩
  intro b hb Ω mΩ P hP ℱ k0 M G hMm hGm Sd cost hdiff hcost hMc hM0 hGc hG0 R hRc hRm Ξ Yh hΞ hYh hk0
  have hk0m : Measurable k0 := hk0
  have hbT : 0 < b + T := by linarith
  have hτ : 0 ≤ b + T := hbT.le
  set X : ℝ → Ω → KSpace d m T := fun t ζ => k0 ζ + (M t ζ - M 0 ζ) with hXdef
  set Xb : ℝ → Ω → KSpace d m T := fun t ζ => k0 ζ + (G t ζ - G 0 ζ) with hXbdef
  set D : ℝ → Ω → KSpace d m T := fun t ζ => M t ζ - G t ζ with hDdef
  have hXc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => X t ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hMc] with ζ h
    exact continuousOn_const.add (h.sub continuousOn_const)
  have hXbc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Xb t ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hGc] with ζ h
    exact continuousOn_const.add (h.sub continuousOn_const)
  have hDc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => D t ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hMc, hGc] with ζ h1 h2
    exact h1.sub h2
  have hXm : ∀ t, Measurable (X t) := fun t => hk0m.add ((hMm t).sub (hMm 0))
  have hXbm : ∀ t, Measurable (Xb t) := fun t => hk0m.add ((hGm t).sub (hGm 0))
  have hwX : AEMeasurable (windowPath b T X) P :=
    HRS.Uniform.Comp28.aemeasurable_windowPath_a P hb hT0 hbT X (fun t _ => hXm t) hXc
  have hwXb : AEMeasurable (windowPath b T Xb) P :=
    HRS.Uniform.Comp28.aemeasurable_windowPath_a P hb hT0 hbT Xb (fun t _ => hXbm t) hXbc
  have hRp0 : AEMeasurable (windowPath 0 T R) P :=
    HRS.GF.gfb4_aemeasurable_windowPath P hT0 R (fun t _ => hRm t) hRc
  set L := s56_reconCLM (d := d) (m := m) hT0 with hL
  set A : Ω → OscPath d m T := fun ζ => L (windowPath b T X ζ) with hAdef
  set Ab : Ω → OscPath d m T := fun ζ => L (windowPath b T Xb ζ) with hAbdef
  set Rp : Ω → OscPath d m T := fun ζ => windowPathOf m T 0 (fun t => R t ζ) with hRpdef
  have hA : AEMeasurable A P := L.continuous.measurable.comp_aemeasurable hwX
  have hAb : AEMeasurable Ab P := L.continuous.measurable.comp_aemeasurable hwXb
  have hRp : AEMeasurable Rp P := by
    refine hRp0.congr (Filter.Eventually.of_forall fun ζ => ?_)
    exact congrFun (s56_wpo_eq_windowPath (m := m) (T := T) R) ζ
  have hΞ' : ∀ᵐ ζ ∂P, Ξ ζ = A ζ + Rp ζ := by
    filter_upwards [hΞ, hMc, hM0, hRc] with ζ h1 h2 h3 h4
    rw [h1]
    exact s105_key_eq hT0 hb k0 M R ζ h2 h3 h4
  have hYh' : ∀ᵐ ζ ∂P, Yh ζ = Ab ζ := by
    filter_upwards [hYh, hGc, hG0] with ζ h1 h2 h3
    rw [h1]
    have := s105_key_eq hT0 hb k0 G (fun _ _ => (0 : OscDual d m)) ζ h2 h3 continuousOn_const
    simp only [add_zero] at this
    rw [this, s56_wpo_zero, add_zero]
  have hlaw1 : law P Ξ = P.map (fun ζ => A ζ + Rp ζ) := Measure.map_congr hΞ'
  have hlaw2 : law P Yh = P.map Ab := Measure.map_congr hYh'
  rw [hlaw1, hlaw2]
  -- the sup of the difference martingale
  set c : Ω → ℝ≥0∞ := fun ζ => ‖windowPath 0 (b + T) D ζ‖ₑ with hcdef
  have hwD : AEMeasurable (windowPath 0 (b + T) D) P :=
    HRS.GF.gfb4_aemeasurable_windowPath P hτ D (fun t _ => (hMm t).sub (hGm t)) hDc
  have hc_m : AEMeasurable c P := hwD.enorm
  have hAAb : ∀ᵐ ζ ∂P, ‖A ζ - Ab ζ‖ₑ ≤ ENNReal.ofReal (3 + Real.sqrt T) * c ζ := by
    filter_upwards [hXc, hXbc, hDc, hMc, hGc, hM0, hG0] with ζ h1 h2 h3 h4 h5 h6 h7
    have hfull : windowPath 0 (b + T) X ζ - windowPath 0 (b + T) Xb ζ = windowPath 0 (b + T) D ζ := by
      rw [← HRS.GF.gfb4_windowPath_sub X Xb h1 h2]
      refine pcm_ext fun t => ?_
      rw [pcm_windowPath (fun t ζ => X t ζ - Xb t ζ) (h1.sub h2), pcm_windowPath D h3]
      simp only [hXdef, hXbdef, hDdef, h6, h7, sub_zero]
      abel
    have e1 := HRS.Uniform.Comp28.windowPath_eq_resWin hb hT0 X h1
    have e2 := HRS.Uniform.Comp28.windowPath_eq_resWin hb hT0 Xb h2
    have hdiff' : A ζ - Ab ζ = L (HRS.Uniform.Comp28.resWin b T hb hT0 (windowPath 0 (b + T) D ζ)) := by
      rw [← hfull, hAdef, hAbdef]
      simp only []
      rw [e1, e2, ← map_sub, ← map_sub]
    have hn : ‖A ζ - Ab ζ‖ ≤ (3 + Real.sqrt T) * ‖windowPath 0 (b + T) D ζ‖ := by
      rw [hdiff']
      calc ‖L (HRS.Uniform.Comp28.resWin b T hb hT0 (windowPath 0 (b + T) D ζ))‖
          ≤ ‖L‖ * ‖HRS.Uniform.Comp28.resWin b T hb hT0 (windowPath 0 (b + T) D ζ)‖ := L.le_opNorm _
        _ ≤ (3 + Real.sqrt T) * (1 * ‖windowPath 0 (b + T) D ζ‖) := by
            refine mul_le_mul (s56_reconCLM_norm_le hT0) ?_ (norm_nonneg _) (by positivity)
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (HRS.Uniform.Comp28.norm_resWin_le hb hT0) (norm_nonneg _))
        _ = _ := by ring
    show ‖A ζ - Ab ζ‖ₑ ≤ ENNReal.ofReal (3 + Real.sqrt T) * ‖windowPath 0 (b + T) D ζ‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hn
  -- BDG
  have hint2 : ∫⁻ ζ, c ζ ^ (2 : ℝ) ∂P ≤
      ENNReal.ofReal Cb * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (cost r ζ)) ∂P := by
    have hbdg := hCb Ω P ℱ (KSpace d m T) (b + T) _ _ hdiff
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one] at hbdg
    calc ∫⁻ ζ, c ζ ^ (2 : ℝ) ∂P
        ≤ ∫⁻ ζ, (⨆ t ∈ Set.Icc (0 : ℝ) (b + T), ‖(M (min t (b + T)) ζ - G (min t (b + T)) ζ)‖ₑ) ^ (2 : ℝ) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hDc] with ζ hζ
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          refine (enorm_windowPath_le D hζ).trans (iSup₂_le fun t ht => ?_)
          refine le_iSup₂_of_le t ht ?_
          simp only [hDdef, min_eq_left ht.2]
          exact le_rfl
      _ ≤ _ := by
          simp only [ENNReal.rpow_two] at hbdg ⊢
          refine hbdg.trans (mul_le_mul' le_rfl (lintegral_mono_ae ?_))
          filter_upwards [hcost] with ζ hζ
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          simp only [if_pos hr.2]
          exact ENNReal.ofReal_le_ofReal (hζ r hr.1 hr.2)
  -- the coupling bounds
  have hp1 : (1 : ℝ) ≤ 1 := le_rfl
  have hw1 : wassersteinE 1 (P.map (fun ζ => A ζ + Rp ζ)) (P.map A) ≤ ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P := by
    refine (wassersteinE_le_of_coupling P 1 hp1 (fun ζ => A ζ + Rp ζ) A (hA.add hRp) hA).trans (le_of_eq ?_)
    simp only [div_one, ENNReal.rpow_one, Real.rpow_one]
    refine lintegral_congr fun ζ => ?_
    rw [add_sub_cancel_left, ← ofReal_norm]
  have hw2 : wassersteinE 1 (P.map A) (P.map Ab) ≤
      ENNReal.ofReal ((3 + Real.sqrt T) * Real.sqrt Cb) *
        (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) := by
    refine (wassersteinE_le_of_coupling P 1 hp1 A Ab hA hAb).trans ?_
    simp only [div_one, ENNReal.rpow_one, Real.rpow_one]
    have e : ∀ ζ, ENNReal.ofReal ‖A ζ - Ab ζ‖ = ‖A ζ - Ab ζ‖ₑ := fun ζ => ofReal_norm _
    simp_rw [e]
    calc ∫⁻ ζ, ‖A ζ - Ab ζ‖ₑ ∂P ≤ ∫⁻ ζ, ENNReal.ofReal (3 + Real.sqrt T) * c ζ ∂P := lintegral_mono_ae hAAb
      _ = ENNReal.ofReal (3 + Real.sqrt T) * (∫⁻ ζ, c ζ ^ (1 : ℝ) ∂P) ^ (1 / (1 : ℝ)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal (3 + Real.sqrt T) * (∫⁻ ζ, c ζ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) :=
          mul_le_mul' le_rfl (HRS.GF.gfb4_lp_le_two P hc_m (Or.inl rfl))
      _ ≤ ENNReal.ofReal (3 + Real.sqrt T) * (ENNReal.ofReal Cb *
            ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / (2 : ℝ)) :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hint2 (by norm_num))
      _ = ENNReal.ofReal ((3 + Real.sqrt T) * Real.sqrt Cb) *
            (∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T), ENNReal.ofReal (cost r ζ)) ∂P) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg hCb0 (by norm_num),
            ← Real.sqrt_eq_rpow]
  calc wassersteinE 1 (P.map (fun ζ => A ζ + Rp ζ)) (P.map Ab)
      ≤ wassersteinE 1 (P.map (fun ζ => A ζ + Rp ζ)) (P.map A) + wassersteinE 1 (P.map A) (P.map Ab) :=
        wassersteinE_triangle 1 hp1 _ (P.map A) _
    _ ≤ _ := by
        rw [add_comm]
        exact add_le_add hw2 hw1

end HRS.MS.R2GenInit
