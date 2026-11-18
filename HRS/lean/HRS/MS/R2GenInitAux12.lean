import HRS.MS.R2GenInitAux11
import HRS.Uniform.Comp28Final

/-!
# S10.5 window comparison, packet A1: the smooth comparison of the window martingales, uniformly in the window start

`s105_smooth_abstract`: Proposition 3.28 (`comparison_smooth_proof`, `K = 1`, `c = 0`, identity evolution on `𝒦_T`) applied to the
`𝒦_T`-valued martingales `k₀ + M` and `k₀ + G` on `[0,b+T]`, followed by the reconstruction `𝒯` of the window path (`s56_reconCLM`, norm
`≤ 3 + √T`, independent of `b`) and the remainder `R`.  The constant `max 1 ((3+√T)²) / 2` does not depend on the window start `b ≥ 0`.
The window of the reconstructed process is `reconstructPath m T (τ ↦ M(b+τ))`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9

variable {d : ℕ}

theorem s105_plainEvol_id (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] (T : ℝ) :
    IsPlainEvolution (fun _ _ => ContinuousLinearMap.id ℝ K) T :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun x => continuousOn_const⟩

/-- On the window the reconstructed process is the image under `𝒯` of the window path of `k₀ + (M - M₀)`, plus the remainder path. -/
lemma s105_key_eq {m T : ℝ} (hT : 0 ≤ T) {b : ℝ} (hb : 0 ≤ b) {Ω : Type*} (k0 : Ω → KSpace d m T)
    (M : ℝ → Ω → KSpace d m T) (R : ℝ → Ω → OscDual d m) (ζ : Ω)
    (hMc : ContinuousOn (fun t => M t ζ) (Set.Icc 0 (b + T))) (hM0 : M 0 ζ = 0)
    (hRc : ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) :
    windowPathOf m T 0 (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ t + R t ζ) =
      s56_reconCLM hT (windowPath b T (fun t ζ => k0 ζ + (M t ζ - M 0 ζ)) ζ) +
        windowPathOf m T 0 (fun t => R t ζ) := by
  have hXc : ContinuousOn (fun t => k0 ζ + (M t ζ - M 0 ζ)) (Set.Icc 0 (b + T)) :=
    continuousOn_const.add (hMc.sub continuousOn_const)
  have hshift : ContinuousOn (fun τ => M (b + τ) ζ) (Set.Icc 0 T) :=
    hMc.comp (by fun_prop) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hreconc : ContinuousOn (fun t => reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ t) (Set.Icc 0 T) :=
    continuousOn_iff_continuous_restrict.2 (u9_continuous_recon hT (fun τ ζ => M (b + τ) ζ) ζ hshift)
  have hfc : ContinuousOn (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ t + R t ζ)
      (Set.Icc 0 T) :=
    ((u9_continuousOn_evalA hT (k0 ζ)).add hreconc).add hRc
  refine ContinuousMap.ext fun t => ?_
  have hL := s56_wpo_apply (m := m) hfc t
  have hR := s56_wpo_apply (m := m) hRc t
  show (show C(Set.Icc (0 : ℝ) T, OscDual d m) from windowPathOf m T 0 _) t =
    (show C(Set.Icc (0 : ℝ) T, OscDual d m) from s56_reconCLM hT _) t +
      (show C(Set.Icc (0 : ℝ) T, OscDual d m) from windowPathOf m T 0 _) t
  rw [hL, hR, s56_reconCLM_apply]
  have hp : ∀ s : Set.Icc (0 : ℝ) T, pcm (windowPath b T (fun t ζ => k0 ζ + (M t ζ - M 0 ζ)) ζ) s =
      k0 ζ + M (b + s) ζ := fun s => by
    rw [HRS.Uniform.Comp28.pcm_windowPath_a hb hT (fun t ζ => k0 ζ + (M t ζ - M 0 ζ)) hXc s, hM0, sub_zero]
  rw [hp, hp]
  unfold reconstructPath
  simp only [s56_evalA_add, s56_B_add]
  abel

theorem s105_smooth_abstract (m T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ), 0 ≤ b → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (k0 : Ω → KSpace d m T), Measurable[ℱ 0] k0 →
      ∀ (M : ℝ → Ω → KSpace d m T) (Sg : ℝ → Ω → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ (b + T) M Sg → (∀ t, Measurable (M t)) →
      ∀ (G : ℝ → Ω → KSpace d m T) (Cb : ℝ → (KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ)),
      IsDetCovDensity (b + T) Cb → IsHilbertMartingaleWithCovariation P ℱ (b + T) G (fun r _ => Cb r) →
      (∀ t, Measurable (G t)) →
      ∀ (R : ℝ → Ω → OscDual d m), (∀ᵐ ζ ∂P, ContinuousOn (fun t => R t ζ) (Set.Icc 0 T)) →
      (∀ t, Measurable (R t)) → ∀ (Ξ Yh : Ω → OscPath d m T),
      (∀ᵐ ζ ∂P, Ξ ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ t + R t ζ)) →
      (∀ᵐ ζ ∂P, Yh ζ = windowPathOf m T 0
        (fun t => (k0 ζ).evalA t + reconstructPath m T (fun τ ζ => G (b + τ) ζ) ζ t)) →
      ENNReal.ofReal (smoothDist 2 (law P Ξ) (law P Yh)) ≤
        ENNReal.ofReal C * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T),
          ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P +
        ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P := by
  have hT0 : 0 ≤ T := hT.le
  refine ⟨max 1 ((3 + Real.sqrt T) ^ 2) * (1 / 2), by positivity, ?_⟩
  intro b hb Ω mΩ P hP ℱ k0 hk0 M Sg hM hMm G Cb hCb hG hGm R hRc hRm Ξ Yh hΞ hYh
  have hbT : 0 < b + T := by linarith
  have hk0m : Measurable k0 := hk0.mono (ℱ.le 0) le_rfl
  set X : ℝ → Ω → KSpace d m T := fun t ζ => k0 ζ + (M t ζ - M 0 ζ) with hXdef
  set Xb : ℝ → Ω → KSpace d m T := fun t ζ => k0 ζ + (G t ζ - G 0 ζ) with hXbdef
  have hZc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => M t ζ - M 0 ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hM.cont] with ζ hζ
    exact hζ.sub continuousOn_const
  have hZbc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => G t ζ - G 0 ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hG.cont] with ζ hζ
    exact hζ.sub continuousOn_const
  have hsp := HRS.Uniform.comparison_smooth_proof 1 0 zero_le_one le_rfl b T hb hT0 Ω P ℱ (KSpace d m T)
    (fun _ _ => ContinuousLinearMap.id ℝ _) (s105_plainEvol_id _ _)
    (fun r t _ _ _ => by simpa using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := KSpace d m T))
    k0 k0 hk0 hk0 M Sg hM G Cb hCb hG (fun t ζ => M t ζ - M 0 ζ) (fun t ζ => G t ζ - G 0 ζ) (fun _ _ => 0)
    (fun t _ => s56_isStochConv_id P M 0 t) (fun t _ => s56_isStochConv_id P G 0 t) hZc hZbc
    (Filter.Eventually.of_forall fun _ => continuousOn_const)
    (fun t => (hMm t).sub (hMm 0)) (fun t => (hGm t).sub (hGm 0)) (fun _ => measurable_const) X Xb
    (fun t _ ζ => by simp [hXdef]) (fun t _ ζ => by simp [hXbdef])
  have hRz : ∀ ζ, ‖windowPath b T (fun (_ : ℝ) (_ : Ω) => (0 : KSpace d m T)) ζ‖ₑ = 0 := fun ζ => by
    have h0 : ‖windowPath 0 (b + T) (fun (_ : ℝ) (_ : Ω) => (0 : KSpace d m T)) ζ‖ₑ = 0 :=
      le_antisymm (HRS.GF.gfb4_windowPath_enorm_le (b + T) _ ζ 0 (fun t _ => by simp)) bot_le
    have hz := enorm_eq_zero.1 h0
    have hr := HRS.Uniform.Comp28.windowPath_eq_resWin hb hT0 (fun (_ : ℝ) (_ : Ω) => (0 : KSpace d m T))
      (ω := ζ) (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : KSpace d m T)) (Set.Icc 0 (b + T)))
    rw [hr, hz, map_zero]
    simp
  have hsp' : ENNReal.ofReal (smoothDist 2 (law P (windowPath b T X)) (law P (windowPath b T Xb))) ≤
      ENNReal.ofReal (1 / 2) * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T),
        ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P := by
    simpa [hRz] using hsp
  have hXm : ∀ t, Measurable (X t) := fun t => hk0m.add ((hMm t).sub (hMm 0))
  have hXbm : ∀ t, Measurable (Xb t) := fun t => hk0m.add ((hGm t).sub (hGm 0))
  have hXc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => X t ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hZc] with ζ h
    exact continuousOn_const.add h
  have hXbc : ∀ᵐ ζ ∂P, ContinuousOn (fun t => Xb t ζ) (Set.Icc 0 (b + T)) := by
    filter_upwards [hZbc] with ζ h
    exact continuousOn_const.add h
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
    filter_upwards [hΞ, hM.cont, hM.zero, hRc] with ζ h1 h2 h3 h4
    rw [h1]
    exact s105_key_eq hT0 hb k0 M R ζ h2 h3 h4
  have hYh' : ∀ᵐ ζ ∂P, Yh ζ = Ab ζ := by
    filter_upwards [hYh, hG.cont, hG.zero] with ζ h1 h2 h3
    rw [h1]
    have := s105_key_eq hT0 hb k0 G (fun _ _ => (0 : OscDual d m)) ζ h2 h3 continuousOn_const
    simp only [add_zero] at this
    rw [this, s56_wpo_zero, add_zero]
  have hlaw1 : law P Ξ = P.map (fun ζ => A ζ + Rp ζ) := Measure.map_congr hΞ'
  have hlaw2 : law P Yh = P.map Ab := Measure.map_congr hYh'
  rw [hlaw1, hlaw2]
  have hmap1 : P.map A = (P.map (windowPath b T X)).map L :=
    (AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hwX).symm
  have hmap2 : P.map Ab = (P.map (windowPath b T Xb)).map L :=
    (AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hwXb).symm
  have hs1 : ENNReal.ofReal (smoothDist 2 (P.map (fun ζ => A ζ + Rp ζ)) (P.map A)) ≤
      ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P := by
    refine (s56_smoothDist_coupling_ae P _ _ (hA.add hRp) hA).trans (le_of_eq ?_)
    refine lintegral_congr fun ζ => ?_
    simp [hRpdef]
  have hs2 : smoothDist 2 (P.map A) (P.map Ab) ≤
      max 1 (((3 + Real.sqrt T) ^ 2)) * smoothDist 2 (law P (windowPath b T X)) (law P (windowPath b T Xb)) := by
    rw [hmap1, hmap2]
    refine (HRS.Main.smoothDist_map_clm_le L 2 _ _).trans ?_
    have hLn : ‖L‖ ≤ 3 + Real.sqrt T := s56_reconCLM_norm_le hT0
    have : max 1 (‖L‖ ^ 2) ≤ max 1 ((3 + Real.sqrt T) ^ 2) :=
      max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hLn 2)
    exact mul_le_mul_of_nonneg_right this (smoothDist_nonneg _ _ _)
  have hmax : 0 ≤ max 1 (((3 + Real.sqrt T) ^ 2)) := le_trans zero_le_one (le_max_left _ _)
  calc ENNReal.ofReal (smoothDist 2 (P.map (fun ζ => A ζ + Rp ζ)) (P.map Ab))
      ≤ ENNReal.ofReal (smoothDist 2 (P.map (fun ζ => A ζ + Rp ζ)) (P.map A) + smoothDist 2 (P.map A) (P.map Ab)) :=
        ENNReal.ofReal_le_ofReal (smoothDist_triangle 2 _ (P.map A) _)
    _ ≤ ENNReal.ofReal (smoothDist 2 (P.map (fun ζ => A ζ + Rp ζ)) (P.map A)) +
          ENNReal.ofReal (smoothDist 2 (P.map A) (P.map Ab)) := ENNReal.ofReal_add_le
    _ ≤ (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P) +
          ENNReal.ofReal (max 1 (((3 + Real.sqrt T) ^ 2))) *
            ENNReal.ofReal (smoothDist 2 (law P (windowPath b T X)) (law P (windowPath b T Xb))) := by
        gcongr
        calc ENNReal.ofReal (smoothDist 2 (P.map A) (P.map Ab))
            ≤ ENNReal.ofReal (max 1 (((3 + Real.sqrt T) ^ 2)) *
                smoothDist 2 (law P (windowPath b T X)) (law P (windowPath b T Xb))) :=
              ENNReal.ofReal_le_ofReal hs2
          _ = _ := ENNReal.ofReal_mul hmax
    _ ≤ (∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P) +
          ENNReal.ofReal (max 1 (((3 + Real.sqrt T) ^ 2))) *
            (ENNReal.ofReal (1 / 2) * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T),
              ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P) := by
        gcongr
    _ = ENNReal.ofReal (max 1 ((3 + Real.sqrt T) ^ 2) * (1 / 2)) * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (b + T),
              ENNReal.ofReal (traceNormForm (Sg r ζ - Cb r))) ∂P +
          ∫⁻ ζ, ‖windowPathOf m T 0 (fun t => R t ζ)‖ₑ ∂P := by
        rw [ENNReal.ofReal_mul hmax, mul_assoc, add_comm]

end HRS.MS.R2GenInit
