import HRS.MC.S7FCH2D

/-!
# H2, part E: assembly in `t` (Minkowski/Jensen in time, Tonelli) and the Carathéodory modification of `fcPartAt`

* `S7FCH2_toL2_sub_le`: `‖toL2 Y - toL2 Z‖ₑ² ≤ ∫⁻_{[0,T]} ‖Y - Z‖ₑ²` for every pair of paths with measurable difference
  (the junk value `0` of `toL2` is harmless: if the right side is finite, `Y` and `Z` are in `L²` together);
* `S7FCH2_joint_modif_fc`: a jointly measurable modification of `t ↦ fcPartAt (0+t) ω`;
* `S7FCH2_asm`: `E ‖toL2 Fa - toL2 Fb‖^Q ≤ T^{Q/2-1} ∫_0^T E ‖Fa_t - Fb_t‖^Q dt` for jointly measurable `Fa, Fb`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F HRS.MC.Sec7.S7FCF5J

variable {d : ℕ}

theorem S7FCH2_toL2_sub_le (r T : ℝ) (Y Z : ℝ → NegSobolev d r)
    (hYZ : AEStronglyMeasurable (fun t => Y t - Z t) (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ‖HRS.Sec7.toL2 r T Y - HRS.Sec7.toL2 r T Z‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t in Set.Icc (0 : ℝ) T, ‖Y t - Z t‖ₑ ^ (2 : ℝ) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  by_cases hf : ∫⁻ t in Set.Icc (0 : ℝ) T, ‖Y t - Z t‖ₑ ^ (2 : ℝ) < ⊤
  swap
  · rw [not_lt, top_le_iff] at hf
    rw [hf]
    exact le_top
  have hD : MemLp (fun t => Y t - Z t) 2 μT := by
    have hlt : eLpNorm (fun t => Y t - Z t) 2 μT < ⊤ :=
      (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (μ := μT)
        (f := fun t => Y t - Z t) (by norm_num) (by simp) hYZ).2 (by simpa using hf)
    exact hlt
  by_cases hY : MemLp Y 2 μT
  · have hZ : MemLp Z 2 μT := by
      have := hY.sub hD
      convert this using 1
      funext t
      simp
    have key : HRS.Sec7.toL2 r T Y - HRS.Sec7.toL2 r T Z = HRS.Sec7.toL2 r T (fun t => Y t - Z t) := by
      unfold HRS.Sec7.toL2
      rw [dif_pos hY, dif_pos hZ, dif_pos hD]
      exact (MemLp.toLp_sub hY hZ).symm
    rw [key]
    exact S7FCF5J_toL2_enorm_rpow_le r T _
  · have hZ : ¬ MemLp Z 2 μT := fun hZ => hY (by
      have := hD.add hZ
      convert this using 1
      funext t
      simp)
    have e1 : HRS.Sec7.toL2 r T Y = 0 := by
      unfold HRS.Sec7.toL2
      rw [dif_neg hY]
    have e2 : HRS.Sec7.toL2 r T Z = 0 := by
      unfold HRS.Sec7.toL2
      rw [dif_neg hZ]
    rw [e1, e2, sub_zero, enorm_zero]
    simp

/-- A jointly measurable modification of `t ↦ fcPartAt (0+t) ω`. -/
theorem S7FCH2_joint_modif_fc (R : Regime d) (r T : ℝ) (hT : 0 < T)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    ∃ Fp : ℝ → Ω → NegSobolev d r, Measurable (Function.uncurry Fp) ∧
      ∃ N0 : Set Ω, MeasurableSet N0 ∧ P N0 = 0 ∧
        ∀ ω ∉ N0, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Fp t ω = fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (0 + t) ω := by
  have hc0 : ∀ᵐ ω ∂P, ContinuousOn (fun t => X (0 + t).toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω => (continuous_pi fun i =>
      (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))).continuousOn
  obtain ⟨V, hVm, N0, hN0m, hN0, hVN⟩ := HRS.MC.Sec7.S7FCW12.s7fcw12_caratheodory P hT.le
    (fun t ω => X (0 + t).toNNReal ω) (fun t => hadapt _) hc0 0
  set G : ℝ × Ω → NegSobolev d r := fun q =>
    fcPartTilde r S K (withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (0 + q.1, y)) (V q.1 q.2)
    with hG_def
  have hGm : Measurable G :=
    HRS.MC.Sec7.S7FCW12.s7fcw12_fcPartTilde_measurable R r S K (fun q : ℝ × Ω => 0 + q.1) (by fun_prop)
      (fun q => V q.1 q.2) hVm
  set M : ℝ → NegSobolev d r := fun t => ∫ ω', G (t, ω') ∂P with hM_def
  have hM : Measurable M := (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  refine ⟨fun t ω => G (t, ω) - M t, hGm.sub (hM.comp measurable_fst), N0, hN0m, hN0, ?_⟩
  intro ω hω t ht
  have hat : 0 ≤ 0 + t := by simpa using ht.1
  have hμ : withDensityReal (R.ρ (0 + t)) =
      withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (0 + t, y) := by
    congr 1
    funext y
    rw [HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos_eq R hat y]
  have hV1 : X (0 + t).toNNReal ω = V t ω := (hVN ω hω t ht).symm
  have hV2 : ∀ᵐ ω' ∂P, X (0 + t).toNNReal ω' = V t ω' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
    exact (hVN ω' hω' t ht).symm
  show G (t, ω) - ∫ ω', G (t, ω') ∂P = _
  show _ = fcPartTilde r S K (withDensityReal (R.ρ (0 + t))) (X (0 + t).toNNReal ω) -
      ∫ ω', fcPartTilde r S K (withDensityReal (R.ρ (0 + t))) (X (0 + t).toNNReal ω') ∂P
  rw [hμ, hV1, integral_congr_ae (hV2.mono fun ω' h' => congrArg _ h')]

/-- Minkowski/Jensen in `t` and Tonelli for the difference of two jointly measurable fields. -/
theorem S7FCH2_asm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r T Q : ℝ)
    (hT : 0 < T) (hQ : 2 < Q) (Fa Fb : ℝ → Ω → NegSobolev d r)
    (hFa : Measurable (Function.uncurry Fa)) (hFb : Measurable (Function.uncurry Fb))
    (ψ : ℝ → ℝ≥0∞) (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂P ≤ ψ t) :
    ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ Q ∂P ≤
      ENNReal.ofReal (T ^ (Q / 2 - 1)) * ∫⁻ t in Set.Icc (0 : ℝ) T, ψ t := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  have hp : 1 < Q / 2 := by linarith
  have hmu : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hexp_nonneg : (0 : ℝ) ≤ Q / 2 - 1 := by linarith
  have hFd : Measurable (Function.uncurry fun t ω => Fa t ω - Fb t ω) := hFa.sub hFb
  have hF2 : ∀ ω, ‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ Q ≤
      μT Set.univ ^ (Q / 2 - 1) * ∫⁻ t, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂μT := by
    intro ω
    have hDm : Measurable fun t => Fa t ω - Fb t ω := Measurable.of_uncurry_right hFd
    have hK : Measurable fun t => ‖Fa t ω - Fb t ω‖ₑ ^ (2 : ℝ) := hDm.enorm.pow_const _
    calc ‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ Q
        = (‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ (2 : ℝ)) ^ (Q / 2) :=
          (S7FCF5J_pow_two _ Q).symm
      _ ≤ (∫⁻ t in Set.Icc (0 : ℝ) T, ‖Fa t ω - Fb t ω‖ₑ ^ (2 : ℝ)) ^ (Q / 2) :=
          ENNReal.rpow_le_rpow (S7FCH2_toL2_sub_le r T _ _ hDm.aestronglyMeasurable) (by linarith)
      _ ≤ μT Set.univ ^ (Q / 2 - 1) * ∫⁻ t, (‖Fa t ω - Fb t ω‖ₑ ^ (2 : ℝ)) ^ (Q / 2) ∂μT :=
          S7FCF5J_jensen_gen μT hK hp
      _ = μT Set.univ ^ (Q / 2 - 1) * ∫⁻ t, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂μT := by
          simp only [S7FCF5J_pow_two]
  have hTon : ∫⁻ ω, ∫⁻ t, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂μT ∂P = ∫⁻ t, ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂P ∂μT := by
    apply lintegral_lintegral_swap
    exact ((hFd.comp measurable_swap).enorm.pow_const Q).aemeasurable
  have hfin : μT Set.univ ^ (Q / 2 - 1) ≠ ⊤ := by
    rw [hmu]
    exact ENNReal.rpow_ne_top_of_nonneg hexp_nonneg ENNReal.ofReal_ne_top
  have hslice : ∫⁻ t, ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂P ∂μT ≤ ∫⁻ t, ψ t ∂μT := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbd t ht
  calc ∫⁻ ω, ‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ Q ∂P
      ≤ ∫⁻ ω, μT Set.univ ^ (Q / 2 - 1) * ∫⁻ t, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂μT ∂P := lintegral_mono hF2
    _ = μT Set.univ ^ (Q / 2 - 1) * ∫⁻ ω, ∫⁻ t, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂μT ∂P :=
        lintegral_const_mul' _ _ hfin
    _ = μT Set.univ ^ (Q / 2 - 1) * ∫⁻ t, ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂P ∂μT := by rw [hTon]
    _ ≤ μT Set.univ ^ (Q / 2 - 1) * ∫⁻ t, ψ t ∂μT := mul_le_mul_of_nonneg_left hslice zero_le
    _ = ENNReal.ofReal (T ^ (Q / 2 - 1)) * ∫⁻ t in Set.Icc (0 : ℝ) T, ψ t := by
        rw [hmu, ENNReal.ofReal_rpow_of_nonneg hT.le hexp_nonneg]

end HRS.MC.Sec7.S7FCH2

end
