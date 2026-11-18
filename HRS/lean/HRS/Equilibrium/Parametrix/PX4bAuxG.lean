import HRS.Equilibrium.Parametrix.PX4bAuxF

/-!
# Packet PX4b auxiliaries G: row integrals of conormal kernels and their `x`-derivatives
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ} {ρ : Torus d → ℝ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Rows of a conormal kernel of order `< d` are continuous functions of the first variable. -/
theorem px4b_row_cont (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ < d) {b : ℕ → ℕ}
    {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : ConormalL σ b m B F) :
    Continuous (fun x => ∫ y, F x y ∂(withDensityReal ρ)) := by
  have hB := conormalL_B_nonneg hd hF
  obtain ⟨C, -, hC⟩ := conormal_row_smooth_aux hd hρ hσ (b 0) 0
  have := (hC B F hB (px4b_conormal_zero_const (conormalL_mono_m (Nat.zero_le m) hF))).1
  exact KernelGrad.continuous_of_lift (show ContDiff ℝ 0 _ from this).continuous

/-- Uniform `L¹` bound of the rows of a conormal kernel of order `< d`. -/
theorem px4b_row_bound (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ < d) {b : ℕ → ℕ}
    {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hF : ConormalL σ b m B F) :
    ∃ K : ℝ, ∀ x, Integrable (fun y => F x y) (withDensityReal ρ) ∧
      ∫ y, |F x y| ∂(withDensityReal ρ) ≤ K := by
  have hB := conormalL_B_nonneg hd hF
  have hc := px4b_conormal_zero_const (conormalL_mono_m (Nat.zero_le m) hF)
  have hH : Conormal σ (b 0) 0 B (offZero F) :=
    conormalL_congr_offDiag (fun x y hxy => by simp [offZero, hxy]) hc
  have hdiag : ∀ x, offZero F x x = 0 := fun x => by simp [offZero]
  obtain ⟨K, hK0, hK⟩ := conormal_row_int hd hρ hσ (b 0)
  refine ⟨K * B, fun x => ?_⟩
  obtain ⟨hint, hbd⟩ := hK B (offZero F) hB hH hdiag x
  have hae : ∀ᵐ y ∂(withDensityReal ρ), offZero F x y = F x y := by
    have := px4b_ae_ne_mu (by omega : 1 ≤ d) ρ x
    filter_upwards [this] with y hy
    simp [offZero, Ne.symm hy]
  refine ⟨hint.congr hae, ?_⟩
  calc ∫ y, |F x y| ∂(withDensityReal ρ) = ∫ y, |offZero F x y| ∂(withDensityReal ρ) :=
        integral_congr_ae (hae.mono fun y hy => by simp only [hy])
    _ ≤ K * B := hbd


lemma px4b_cont_zero_of_integral {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ∫ s in (0 : ℝ)..t, f s = 0) : f 0 = 0 := by
  have hd : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, f s) (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt
  have hw : HasDerivWithinAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, f s) (f 0) (Ici 0) 0 :=
    hd.hasDerivWithinAt
  have hev : (fun u : ℝ => ∫ s in (0 : ℝ)..u, f s) =ᶠ[𝓝[Ici 0] 0] fun _ => (0 : ℝ) := by
    have : Icc (0 : ℝ) 1 ∈ 𝓝[Ici 0] (0 : ℝ) := Icc_mem_nhdsGE zero_lt_one
    filter_upwards [this] with u hu
    rcases eq_or_lt_of_le hu.1 with h0 | h0
    · rw [← h0]; simp
    · exact h u h0 hu.2
  have hw2 : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (f 0) (Ici 0) 0 :=
    hw.congr_of_eventuallyEq hev.symm (by simp)
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hw2 (hasDerivWithinAt_const _ _ _)

lemma px4b_T_neg_self (i : Fin d) (s : ℝ) (x : Torus d) : px4b_T i (-s) (px4b_T i s x) = x := by
  rw [px4b_T_add, neg_add_cancel, px4b_T_zero]

lemma px4b_null_orbit (hd : 2 ≤ d) (i : Fin d) (x0 : Torus d) :
    (volume : Measure (Torus d)) {y : Torus d | ∃ s : ℝ, y = px4b_T i s x0} = 0 :=
  measure_mono_null (fun y hy => by
    obtain ⟨s, hs⟩ := hy
    exact ⟨-s, by rw [hs, px4b_T_neg_self]⟩) (px4b_null_line hd i x0)

lemma px4b_slice_cd {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} {n : ℕ}
    (hn : n ≤ m) (hF : ConormalL σ b m B F) (y : Torus d) :
    ∀ v : Euc d, Torus.mk v ≠ y → ContDiffAt ℝ n (Torus.lift (fun x => F x y)) v := by
  intro v hv
  have hp : (v, Torus.rep y) ∈ offDiag d := by
    show Torus.mk v ≠ Torus.mk (Torus.rep y)
    rwa [Torus.mk_rep]
  have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (lift2 F) (v, Torus.rep y) :=
    hF.smooth.contDiffAt (isOpen_offDiag.mem_nhds hp)
  have h2 : ContDiffAt ℝ n (lift2 F) (v, Torus.rep y) := h1.of_le (by exact_mod_cast hn)
  have h3 : ContDiffAt ℝ n (fun w : Euc d => lift2 F (w, Torus.rep y)) v :=
    h2.comp v (contDiffAt_id.prodMk contDiffAt_const)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [Torus.lift, Function.comp, lift2]
  rw [Torus.mk_rep]


/-- Differentiating the rows: if the rows of a conormal kernel `F` (order `σ`, `σ + 1 < d`,
`m ≥ 1` derivatives) have `μ`-mean zero, so do the rows of `∂_{x_i} F`.  (Fundamental theorem of
calculus along lines + Fubini; the continuity of the rows of `∂_{x_i}F` closes the argument.) -/
theorem px4b_row_deriv_zero (hd : 2 ≤ d) (hρ : SmoothPosDensity ρ) {σ : ℝ} (hσ : σ + 1 < d)
    {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ} (hm : 1 ≤ m)
    (hF : ConormalL σ b m B F) (i : Fin d)
    (hrow : ∀ x, ∫ y, F x y ∂(withDensityReal ρ) = 0) (x0 : Torus d) :
    ∫ y, Torus.partialDeriv i (fun z => F z y) x0 ∂(withDensityReal ρ) = 0 := by
  set μ := withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ.density
  have hσ0 : σ < d := by linarith
  obtain ⟨K1, hK1def⟩ : ∃ K1 : Torus d → Torus d → ℝ,
      ∀ x y, K1 x y = Torus.partialDeriv i (fun z => F z y) x := ⟨_, fun _ _ => rfl⟩
  have hK1 : ConormalL (σ + 1) (fun c => max (b c) (b (c + 1))) (m - 1) (2 * B) K1 := by
    have h := conormal_partial_fst_aux hF hm i
    have e : K1 = fun x y => Torus.partialDeriv i (fun z => F z y) x := funext fun x => funext (hK1def x)
    rw [e]; exact h
  have hcont := px4b_row_cont hd hρ hσ hK1
  obtain ⟨KK, hKK⟩ := px4b_row_bound hd hρ hσ hK1
  obtain ⟨KF, hKF⟩ := px4b_row_bound hd hρ hσ0 hF
  obtain ⟨G, hG⟩ : ∃ G : Torus d → Torus d → ℝ, ∀ x y, G x y = if x = y then 0 else K1 x y :=
    ⟨offZero K1, fun _ _ => rfl⟩
  have hGe : G = offZero K1 := funext fun x => funext fun y => hG x y
  have hGmeas : Measurable (Function.uncurry G) := by
    rw [hGe]; exact measurable_offZero_of_contDiffOn hK1.smooth
  have hne : ∀ x : Torus d, ∀ᵐ y ∂μ, y ≠ x := fun x => px4b_ae_ne_mu (by omega) ρ x
  have hGeq : ∀ x, (fun y => G x y) =ᵐ[μ] fun y => K1 x y := fun x => by
    filter_upwards [hne x] with y hy
    rw [hG, if_neg (Ne.symm hy)]
  have hGrow : ∀ x, Integrable (fun y => G x y) μ := fun x => (hKK x).1.congr (hGeq x).symm
  have hTc : Continuous (fun s : ℝ => px4b_T i s x0) :=
    (px4b_continuous_T i).comp (continuous_id.prodMk continuous_const)
  have hAmeas : Measurable (fun p : ℝ × Torus d => G (px4b_T i p.1 x0) p.2) :=
    hGmeas.comp (hTc.measurable.comp measurable_fst |>.prodMk measurable_snd)
  have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∫ s in (0 : ℝ)..t, (∫ y, K1 (px4b_T i s x0) y ∂μ) = 0 := by
    intro t ht0 ht1
    obtain ⟨μs, hμs⟩ : ∃ μs : Measure ℝ, μs = volume.restrict (Ioc (0 : ℝ) t) := ⟨_, rfl⟩
    haveI : IsFiniteMeasure μs := ⟨by simp [hμs]⟩
    -- joint integrability
    have hint : Integrable (fun p : ℝ × Torus d => G (px4b_T i p.1 x0) p.2) (μs.prod μ) := by
      rw [integrable_prod_iff hAmeas.aestronglyMeasurable]
      refine ⟨Eventually.of_forall fun s => ?_, ?_⟩
      · exact hGrow (px4b_T i s x0)
      refine Integrable.mono' (integrable_const KK)
        (hAmeas.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun s => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖G (px4b_T i s x0) y‖ ∂μ = ∫ y, ‖K1 (px4b_T i s x0) y‖ ∂μ :=
            integral_congr_ae ((hGeq _).mono fun y (hy : G _ y = K1 _ y) => by show ‖G _ y‖ = ‖K1 _ y‖; rw [hy])
        _ ≤ KK := by
          have := (hKK (px4b_T i s x0)).2
          simpa [Real.norm_eq_abs] using this
    -- pointwise FTC for `y` off the orbit
    have hline : ∀ y : Torus d, (∀ s : ℝ, y ≠ px4b_T i s x0) →
        F (px4b_T i t x0) y - F x0 y = ∫ s in (0 : ℝ)..t, G (px4b_T i s x0) y := by
      intro y hy
      have hu : ∀ r : ℝ, ContDiffAt ℝ 1 (Torus.lift (fun z => F z y)) (Torus.rep x0 + r • px4b_e i) := by
        intro r
        refine px4b_slice_cd (n := 1) hm hF y _ ?_
        rw [px4b_mk_rep_add]; exact (hy r).symm
      have hf := px4b_line_ftc i (fun z => F z y) x0 hu 0 t
      rw [px4b_T_zero] at hf
      rw [hf]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      show Torus.partialDeriv i (fun z => F z y) (px4b_T i s x0) = G (px4b_T i s x0) y
      rw [hG, if_neg (hy s).symm, hK1def]
    have hae : ∀ᵐ y ∂μ, ∀ s : ℝ, y ≠ px4b_T i s x0 := by
      have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), ∀ s : ℝ, y ≠ px4b_T i s x0 := by
        rw [ae_iff]
        refine measure_mono_null (fun y hy => ?_) (px4b_null_orbit hd i x0)
        simpa using hy
      exact (withDensity_absolutelyContinuous _ _).ae_le h0
    -- the row integrals of `F`
    have h1 : ∫ y, (F (px4b_T i t x0) y - F x0 y) ∂μ = 0 := by
      rw [integral_sub (hKF _).1 (hKF _).1, hrow, hrow, sub_zero]
    have h2 : ∫ y, (F (px4b_T i t x0) y - F x0 y) ∂μ =
        ∫ y, (∫ s in (0 : ℝ)..t, G (px4b_T i s x0) y) ∂μ :=
      integral_congr_ae (hae.mono fun y hy => hline y hy)
    have h3 : ∫ y, (∫ s in (0 : ℝ)..t, G (px4b_T i s x0) y) ∂μ =
        ∫ s in Ioc (0 : ℝ) t, ∫ y, G (px4b_T i s x0) y ∂μ := by
      simp only [intervalIntegral.integral_of_le ht0.le]
      have := integral_integral_swap
        (f := fun (s : ℝ) (y : Torus d) => G (px4b_T i s x0) y) hint
      rw [hμs] at this
      exact this.symm
    have h4 : ∫ s in Ioc (0 : ℝ) t, ∫ y, G (px4b_T i s x0) y ∂μ =
        ∫ s in Ioc (0 : ℝ) t, ∫ y, K1 (px4b_T i s x0) y ∂μ :=
      integral_congr_ae (Eventually.of_forall fun s => integral_congr_ae (hGeq _))
    rw [intervalIntegral.integral_of_le ht0.le, ← h4, ← h3, ← h2, h1]
  have hfc : Continuous (fun s : ℝ => ∫ y, K1 (px4b_T i s x0) y ∂μ) := hcont.comp hTc
  have := px4b_cont_zero_of_integral hfc hstep
  simpa [px4b_T_zero, hK1def] using this

end HRS.Parx
end
