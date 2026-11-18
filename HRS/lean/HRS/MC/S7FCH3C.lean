import HRS.MC.S7FCH3B
import HRS.MC.S7FCH1B3
import HRS.MC.S7FCW5A
import HRS.MC.S7FCW9Lem
import HRS.PDE.MeanFieldLinearLoss

/-!
# S7FCH3C: `IsHalfWick` differences, measurability of the finite-rank quadratic form, `toL2` calculus (H3, part C)

Sorry-free helpers, no regime:

* `S7FCH3_isHalfWick_sub`: if `Q` and `Q'` are the Wick limits for the kernels `h` and `h'`, and the Wick coefficients
  of `h''` are the difference, then `Q - Q'` is the Wick limit for `h''`;
* `S7FCH3_quad_meas`: `FRKernel.quad` is continuous (hence measurable) on `E_r`;
* `S7FCH3_toL2_congr`, `S7FCH3_toL2_sub`, `S7FCH3_toL2_norm_sq`: calculus for `toL2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH3

open HRS HRS.Sec7 HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW9 HRS.MC.Sec7.S7FCW5

variable {d : ℕ}

theorem S7FCH3_isHalfWick_sub {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {r : ℝ}
    {η : Ω → NegSobolev d r} (hηm : Measurable η) {μ : Measure (Torus d)}
    {h h' h'' : Torus d → Torus d → ℝ} {Q Q' : Ω → ℝ} (hQm : Measurable Q) (hQ'm : Measurable Q')
    (H : IsHalfWick P η μ h Q) (H' : IsHalfWick P η μ h' Q')
    (hc : ∀ k l, wickCoeff μ h'' k l = wickCoeff μ h k l - wickCoeff μ h' k l) :
    IsHalfWick P η μ h'' (fun ω => Q ω - Q' ω) := by
  unfold IsHalfWick at H H' ⊢
  set sec : (Torus d → Torus d → ℝ) → Finset (NonzeroLattice d) → Ω → ℝ := fun g S ω =>
    (1 / 2) * ∑ k ∈ S, ∑ l ∈ S, wickCoeff μ g k l * (NegSobolev.fourierCoeff (η ω) k *
      NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
        NegSobolev.fourierCoeff (η ω') l ∂P) with hsec
  have hsm : ∀ g S, Measurable (sec g S) := by
    intro g S
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_)
    exact measurable_const.mul
      ((((HRS.FieldSingAux.measurable_fourierCoeff k).comp hηm).mul
        ((HRS.FieldSingAux.measurable_fourierCoeff l).comp hηm)).sub measurable_const)
  have hsub : ∀ S ω, sec h'' S ω = sec h S ω - sec h' S ω := by
    intro S ω
    simp only [hsec, hc, sub_mul, Finset.sum_sub_distrib]
    ring
  have hbound : ∀ S : Finset (NonzeroLattice d),
      ∫⁻ ω, ‖(Q ω - Q' ω) - sec h'' S ω‖ₑ ^ 2 ∂P ≤
        2 * (∫⁻ ω, ‖Q ω - sec h S ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Q' ω - sec h' S ω‖ₑ ^ 2 ∂P) := by
    intro S
    have hm1 : Measurable (fun ω => ‖Q ω - sec h S ω‖ₑ ^ 2) :=
      (measurable_enorm.comp (hQm.sub (hsm h S))).pow_const 2
    have hpt : ∀ ω, ‖(Q ω - Q' ω) - sec h'' S ω‖ₑ ^ 2 ≤
        2 * (‖Q ω - sec h S ω‖ₑ ^ 2 + ‖Q' ω - sec h' S ω‖ₑ ^ 2) := by
      intro ω
      rw [S7FCW5_enorm_sq, S7FCW5_enorm_sq, S7FCW5_enorm_sq]
      have e : (Q ω - Q' ω) - sec h'' S ω = (Q ω - sec h S ω) - (Q' ω - sec h' S ω) := by
        rw [hsub]; ring
      rw [e, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [sq_nonneg (Q ω - sec h S ω + (Q' ω - sec h' S ω))]
    calc ∫⁻ ω, ‖(Q ω - Q' ω) - sec h'' S ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * (‖Q ω - sec h S ω‖ₑ ^ 2 + ‖Q' ω - sec h' S ω‖ₑ ^ 2) ∂P := lintegral_mono hpt
      _ = 2 * (∫⁻ ω, ‖Q ω - sec h S ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Q' ω - sec h' S ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left hm1]
  have hlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
      2 * (∫⁻ ω, ‖Q ω - sec h S ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Q' ω - sec h' S ω‖ₑ ^ 2 ∂P)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (H.add H') (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)) (a := 2)
    have h0 : (2 : ℝ≥0∞) * (0 + 0) = 0 := by simp
    rw [h0] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hbound

theorem S7FCH3_quad_cont {r : ℝ} (K : FRKernel d) : Continuous (fun F : NegSobolev d r => K.quad F) := by
  unfold FRKernel.quad
  refine continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  have hc : ∀ i, Continuous (fun F : NegSobolev d r => NegSobolev.eval F (K.f i)) := fun i =>
    HRS.PDE.MFLinear.continuous_eval_const (K.f i) (HRS.MC.Sec7.S7FCH1.S7FCH1_wsum (K.smooth i) r)
  exact continuous_const.mul ((hc i).mul (hc j))

theorem S7FCH3_toL2_congr (r T : ℝ) {f g : ℝ → NegSobolev d r}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = g t) : toL2 r T f = toL2 r T g := by
  have hae : f =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] g :=
    (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall h)
  unfold toL2
  by_cases hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))
  · have hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := hf.ae_eq hae
    rw [dif_pos hf, dif_pos hg]
    exact MemLp.toLp_congr hf hg hae
  · have hg : ¬ MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := fun hg => hf (hg.ae_eq hae.symm)
    rw [dif_neg hf, dif_neg hg]

theorem S7FCH3_toL2_sub (r T : ℝ) {f g : ℝ → NegSobolev d r}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hg : MemLp g 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    toL2 r T f - toL2 r T g = toL2 r T (fun t => f t - g t) := by
  have hfg : MemLp (fun t => f t - g t) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := hf.sub hg
  unfold toL2
  rw [dif_pos hf, dif_pos hg, dif_pos hfg, ← MemLp.toLp_sub hf hg]
  rfl

theorem S7FCH3_toL2_norm_sq (r T : ℝ) {f : ℝ → NegSobolev d r}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T))) :
    ‖toL2 r T f‖ ^ 2 = ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  unfold toL2
  rw [dif_pos hf, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

end HRS.MC.Sec7.S7FCH3

end
