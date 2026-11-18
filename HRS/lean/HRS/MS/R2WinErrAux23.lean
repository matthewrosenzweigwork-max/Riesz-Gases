import HRS.MS.R2WinErrAux22
import HRS.MS.GenPathAux11

/-!
# S10.4 input `hdyn` for the stationary trajectory (part 3): joint measurability of the forcing families

`s104_M0_stat`, `s104_M1_stat`, `s104_M2_stat`: the families `ofReal|Fm(b,r)|`, `ofReal|Fm(r,r)|`, `ofReal|F2(s',r)|` are `P ⊗ dr`-a.e.-measurable (resp.
`P ⊗ ds'dr`) along a progressive process: they are `D(G(·))(X_r)` with `G` jointly continuous in `(τ,x)` after clamping (`s53_grad_continuous`),
`s53_Dk_measurable`, and the joint measurability of the clamped progressive process (`mrr_prog_meas`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53 HRS.MP.RdRem

variable {d N : ℕ}

lemma s104_aem_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {f : Ω × ℝ → ℝ≥0∞}
    {A B : Set ℝ} (hAB : B ⊆ A) (h : AEMeasurable f (P.prod (volume.restrict A))) :
    AEMeasurable f (P.prod (volume.restrict B)) :=
  h.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono hAB le_rfl))

section Stat

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
  {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) (α : MultiIndex d) {T0 : ℝ} (hT0 : 0 ≤ T0)
  {G0 G1 G2 : ℝ → Euc d → ℝ}

include hd hs0 hsd ha hβ hρ hT0 in
theorem s104_M0_stat {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X))
    (hG : S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2) (hprob : HRS.Whole.IsProbDensity ρβ)
    {b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T0) :
    AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α b p.2 p.1|)
      (P.prod (volume.restrict (Icc (0 : ℝ) b))) := by
  have hc0 : S53Cont T0 G0 := s53_cont_of_diff hG.cb0 hG.cb1 hG.diff01
  have hjc := s53_grad_continuous hT0 hG.cb0 hc0
  have hF : Measurable fun p : ℝ × Euc d => gradient ((fun τ => G0 (s53_clamp T0 (b - τ))) p.1) p.2 :=
    (hjc.comp (Continuous.prodMk (by fun_prop) continuous_snd)).measurable
  have hDm := s53_Dk_measurable (N := N) (s := s) (F := fun τ => G0 (s53_clamp T0 (b - τ))) hprob hF
  have hFm : Measurable fun q : ℝ × EucConfig d N =>
      |s53_Dk s ρβ ((fun τ => G0 (s53_clamp T0 (b - τ))) q.1) q.2| :=
    continuous_abs.measurable.comp hDm
  have h := HRS.MS.GenPath.s56_aemeas_of_clamp P ℱ X hprog hb _ hFm
  refine (h.ennreal_ofReal).congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) b))), p.2 ∈ Icc (0 : ℝ) b :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  have hbm : b ∈ Icc (0 : ℝ) T0 := ⟨hb, hbT⟩
  rw [s104_Fm_eq hd hs0 hsd ha hβ hρ α hG X p.1 hbm hp]
  have : s53_clamp T0 (b - p.2) = b - p.2 := s53_clamp_of_mem ⟨by linarith [hp.2], by linarith [hp.1]⟩
  simp only [this]

include hd hs0 hsd ha hβ hρ hT0 in
theorem s104_M1_stat {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X))
    (hG : S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2) (hprob : HRS.Whole.IsProbDensity ρβ)
    {b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T0) :
    AEMeasurable (fun p : Ω × ℝ => ENNReal.ofReal |r2CommForcingMov
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α p.2 p.2 p.1|)
      (P.prod (volume.restrict (Icc b T0))) := by
  have hjc0 : Measurable fun p : ℝ × Euc d => gradient ((fun _ : ℝ => G0 0) p.1) p.2 := by
    have h1 := (hG.cb0 0 ⟨le_rfl, hT0⟩).1
    have h2 : Continuous (fderiv ℝ (G0 0)) := h1.continuous_fderiv (by norm_num)
    have h3 : Continuous fun x => gradient (G0 0) x :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h2
    exact (h3.comp continuous_snd).measurable
  have hDm := s53_Dk_measurable (N := N) (s := s) (F := fun _ : ℝ => G0 0) hprob hjc0
  have hFm : Measurable fun q : ℝ × EucConfig d N => |s53_Dk s ρβ ((fun _ : ℝ => G0 0) q.1) q.2| :=
    continuous_abs.measurable.comp hDm
  have h := HRS.MS.GenPath.s56_aemeas_of_clamp P ℱ X hprog hT0 _ hFm
  refine s104_aem_mono (A := Icc (0 : ℝ) T0) (Icc_subset_Icc_left hb) ?_
  refine (h.ennreal_ofReal).congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict (Icc (0 : ℝ) T0))), p.2 ∈ Icc (0 : ℝ) T0 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hq] with p hp
  rw [s104_Fm_eq hd hs0 hsd ha hβ hρ α hG X p.1 hp ⟨hp.1, le_rfl⟩]
  simp only [sub_self]

set_option maxHeartbeats 800000 in
include hd hs0 hsd ha hβ hρ hT0 in
theorem s104_M2_stat {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N) (hprog : IsProgressive ℱ (ofNNRealTime X))
    (hG : S104StatOrbit ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
      (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) T0 G0 G1 G2) (hprob : HRS.Whole.IsProbDensity ρβ)
    {b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T0) :
    AEMeasurable (fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |s104_F2
      ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ)) s ((24 * d + 240 : ℕ) : ℝ) (fun _ => ρβ) X α p.2 p.1|)
      (P.prod (volume.restrict ((Icc b T0) ×ˢ (Icc (0 : ℝ) T0)))) := by
  have hc1 : S53Cont T0 G1 := s53_cont_of_diff hG.cb1 hG.cb2 hG.diff12
  have hjc := s53_grad_continuous hT0 hG.cb1 hc1
  have hDm := s53_Dk_measurable (N := N) (s := s) (F := fun τ => G1 (s53_clamp T0 τ)) hprob
    hjc.measurable
  have hE : Measurable fun p : Ω × (ℝ × ℝ) => X (Real.toNNReal (mrrClamp T0 p.2.2)) p.1 :=
    (mrr_prog_meas ℱ X hprog hT0).comp (measurable_snd.comp measurable_snd |>.prodMk measurable_fst)
  have hΨ : Measurable fun p : Ω × (ℝ × ℝ) => ENNReal.ofReal |if p.2.2 ≤ p.2.1 then
      s53_Dk s ρβ (G1 (s53_clamp T0 (p.2.1 - p.2.2))) (X (Real.toNNReal (mrrClamp T0 p.2.2)) p.1) else 0| := by
    refine ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp ?_)
    refine Measurable.ite (measurableSet_le (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd)) ?_ measurable_const
    have hg : Measurable fun p : Ω × (ℝ × ℝ) => (p.2.1 - p.2.2, X (Real.toNNReal (mrrClamp T0 p.2.2)) p.1) :=
      ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd)).prodMk hE
    have hc := hDm.comp hg
    simpa only [Function.comp_def] using hc
  refine hΨ.aemeasurable.congr ?_
  have hq : ∀ᵐ p ∂(P.prod (volume.restrict ((Icc b T0) ×ˢ (Icc (0 : ℝ) T0)))),
      p.2 ∈ (Icc b T0) ×ˢ (Icc (0 : ℝ) T0) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc))
  filter_upwards [hq] with p hp
  obtain ⟨⟨hs1, hs2⟩, hr1, hr2⟩ := hp
  by_cases hle : p.2.2 ≤ p.2.1
  · have hs' : p.2.1 ∈ Icc (0 : ℝ) T0 := ⟨hb.trans hs1, hs2⟩
    rw [s104_F2_eq hd hs0 hsd ha hβ hρ α hG X p.1 hs' ⟨hr1, hle⟩]
    have hc : s53_clamp T0 (p.2.1 - p.2.2) = p.2.1 - p.2.2 :=
      s53_clamp_of_mem ⟨by linarith, by linarith⟩
    have hm : mrrClamp T0 p.2.2 = p.2.2 := mrrClamp_of_mem ⟨hr1, hr2⟩
    simp only [hle, if_true, hc, hm]
  · simp only [hle, if_false]
    unfold s104_F2
    simp [hle]

end Stat

end HRS.MS.R2WinErr
