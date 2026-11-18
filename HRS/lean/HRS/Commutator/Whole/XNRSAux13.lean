import HRS.Commutator.Whole.XNRSAux12

/-!
# Packet X-NRS, part 13: the limit `δ → 0` (super-Coulombic estimate, `α' ∈ (0,1)`)

`‖∫ (2π|ξ|)^{2σ} 𝓕h 𝓕ψ(-ξ)‖ ≤ (d + (d+2σ+2)/2) L ‖Λ^σ h‖²`, `ψ = v·∇h`, `0 < σ < 1`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xmK_le_xm0 (hd : 1 ≤ d) {σ δ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hδ : 0 < δ) (ξ : Euc d) :
    xmK (xK d σ δ) ξ ≤ xm0 d σ ξ := by
  unfold xmK xm0
  refine integral_mono (integrable_xmK_integrand (xKer_xK hσ0 hδ) ξ)
    (integrable_xm0_integrand hd hσ0 hσ1 ξ) fun z => ?_
  by_cases hz : z = 0
  · subst hz; simp [xph]
  · exact mul_le_mul_of_nonneg_right ((xK_le_xN hδ z).trans (xN_le_pow hσ0 hδ hz)) (xph_nonneg ξ z)

lemma xmK_nonneg {σ δ : ℝ} (hσ0 : 0 < σ) (hδ : 0 < δ) (ξ : Euc d) : 0 ≤ xmK (xK d σ δ) ξ :=
  integral_nonneg fun z => mul_nonneg (xK_pos hδ z).le (xph_nonneg ξ z)

lemma tendsto_xmK (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ξ : Euc d) :
    Tendsto (fun δ : ℝ => xmK (xK d σ δ) ξ) (𝓝[>] 0) (𝓝 (xm0 d σ ξ)) := by
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  unfold xmK xm0
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z) ?_ ?_
    (integrable_xm0_integrand hd hσ0 hσ1 ξ) ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (integrable_xmK_integrand (xKer_xK hσ0 hδ) ξ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (xK_pos hδ z).le (xph_nonneg ξ z))]
    by_cases hz : z = 0
    · subst hz; simp [xph]
    · exact mul_le_mul_of_nonneg_right ((xK_le_xN hδ z).trans (xN_le_pow hσ0 hδ hz)) (xph_nonneg ξ z)
  · have hz : ∀ᵐ z : Euc d, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hz] with z hz
    refine Tendsto.mul ?_ tendsto_const_nhds
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hN : Tendsto (fun δ : ℝ => xN d σ δ z) (𝓝[>] 0) (𝓝 (‖z‖ ^ (-((d : ℝ) + 2 * σ)))) := by
      have hc : ContinuousAt (fun δ : ℝ => (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)) 0 := by
        apply ContinuousAt.rpow_const (by fun_prop) (Or.inl (by positivity))
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      have hlim : (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) = ‖z‖ ^ (-((d : ℝ) + 2 * σ)) := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; congr 1; push_cast; ring
      rw [hlim] at this
      exact this
    have hΦ : Tendsto (fun δ : ℝ => xPhi δ z) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun δ : ℝ => (1 + δ * ‖z‖ ^ 2)⁻¹) 0 := by
        apply ContinuousAt.inv₀ (by fun_prop); simp
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [xPhi] using this
    have := hN.mul hΦ
    simpa [xK] using this


lemma xint_w_schwartz {s : ℝ} (hs : 0 ≤ s) (G : 𝓢(Euc d, ℂ)) :
    Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ s * ‖G ξ‖) := by
  have h := (HRS.Commutator.Whole.cmxHLS_integrable_rpow_schwartz hs G).const_mul ((2 * Real.pi) ^ s)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
  ring

lemma continuous_xw {s : ℝ} (hs : 0 ≤ s) : Continuous (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ s) :=
  (Real.continuous_rpow_const hs).comp (by fun_prop)

lemma aesm_xmK {K : Euc d → ℝ} (hK : XKer K) :
    AEStronglyMeasurable (fun ξ : Euc d => ((xmK K ξ : ℝ) : ℂ)) volume := by
  have h1 : StronglyMeasurable (fun ξ : Euc d => xmK K ξ) := by
    unfold xmK
    have hc : Continuous (fun p : Euc d × Euc d => K p.2 * xph p.1 p.2) := by
      refine (hK.cont.comp continuous_snd).mul ?_
      unfold xph; fun_prop
    exact hc.stronglyMeasurable.integral_prod_right'
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable h1).aestronglyMeasurable

theorem xsc (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {v : Euc d → Euc d} (hv : XTVF v)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) (h : 𝓢(Euc d, ℂ)) :
    ‖xpair (2 * σ) h (xadv v h)‖ ≤ ((d : ℝ) + ((d : ℝ) + 2 * σ + 2) / 2) * L * xhom σ h := by
  set ψ := xadv v h with hψ
  set C : ℝ := (d : ℝ) + ((d : ℝ) + 2 * σ + 2) / 2 with hC
  have hC0 : 0 ≤ C := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; rw [hC]; positivity
  set c₀ := xm0 d σ (xe (⟨0, hd⟩ : Fin d)) with hc₀def
  have hc₀ : 0 < c₀ := xm0_pos hd hσ0 hσ1
  set c' : ℝ := c₀ * (2 * Real.pi) ^ (-(2 * σ)) with hc'def
  have hc' : 0 < c' := by rw [hc'def]; positivity
  have hxm0 : ∀ ξ : Euc d, xm0 d σ ξ = c' * (2 * Real.pi * ‖ξ‖) ^ (2 * σ) := by
    intro ξ
    rw [xm0_eq hd hσ0 ξ, hc'def, Real.mul_rpow (by positivity) (norm_nonneg _), ← mul_assoc]
    have : (2 * Real.pi) ^ (-(2 * σ)) * (2 * Real.pi) ^ (2 * σ) = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    rw [mul_assoc c₀, this, mul_one]
  obtain ⟨M₂, hM₂0, hM₂⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ : Euc d, ‖𝓕 ψ (-ξ)‖ ≤ M := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(Euc d, ℂ)), by positivity, fun ξ => ?_⟩
    simpa using SchwartzMap.le_seminorm ℝ 0 0 (𝓕 ψ : 𝓢(Euc d, ℂ)) (-ξ)
  -- the dominating function
  have hwint : Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖) :=
    xint_w_schwartz (by positivity) (𝓕 h : 𝓢(Euc d, ℂ))
  have hB : Integrable (fun ξ : Euc d => c' * ((2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖) * M₂) :=
    (hwint.const_mul c').mul_const M₂
  have hxm0c : Continuous (fun ξ : Euc d => xm0 d σ ξ) := by
    have : (fun ξ : Euc d => xm0 d σ ξ) = fun ξ => c' * (2 * Real.pi * ‖ξ‖) ^ (2 * σ) := funext hxm0
    rw [this]; exact continuous_const.mul (continuous_xw (by positivity))
  have hpair_bound : ∀ ξ : Euc d, ‖((xm0 d σ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)‖ ≤
      c' * ((2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖) * M₂ := by
    intro ξ
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hxm0 ξ,
      abs_of_nonneg (by positivity)]
    calc c' * (2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖ * ‖𝓕 ψ (-ξ)‖
        ≤ c' * (2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖ * M₂ :=
          mul_le_mul_of_nonneg_left (hM₂ ξ) (by positivity)
      _ = _ := by ring
  have hpair_int : Integrable (fun ξ : Euc d => ((xm0 d σ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)) := by
    refine hB.mono' ?_ (Eventually.of_forall hpair_bound)
    exact (((Complex.continuous_ofReal.comp hxm0c).mul (𝓕 h : 𝓢(Euc d, ℂ)).continuous).mul
      ((𝓕 ψ : 𝓢(Euc d, ℂ)).continuous.comp continuous_neg)).aestronglyMeasurable
  -- the limit
  have hlim : Tendsto (fun δ : ℝ => ∫ ξ, ((xmK (xK d σ δ) ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)) (𝓝[>] 0)
      (𝓝 (∫ ξ, ((xm0 d σ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ : Euc d => c' * ((2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖) * M₂) ?_ ?_ hB ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact ((aesm_xmK (xKer_xK hσ0 hδ)).mul
        (𝓕 h : 𝓢(Euc d, ℂ)).continuous.aestronglyMeasurable).mul
        ((𝓕 ψ : 𝓢(Euc d, ℂ)).continuous.comp continuous_neg).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      refine Eventually.of_forall fun ξ => ?_
      refine le_trans ?_ (hpair_bound ξ)
      have e1 : ‖((xmK (xK d σ δ) ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)‖ =
          xmK (xK d σ δ) ξ * ‖𝓕 h ξ‖ * ‖𝓕 ψ (-ξ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (xmK_nonneg hσ0 hδ ξ)]
      have e2 : ‖((xm0 d σ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)‖ =
          xm0 d σ ξ * ‖𝓕 h ξ‖ * ‖𝓕 ψ (-ξ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by rw [hxm0 ξ]; positivity)]
      rw [e1, e2]
      have := xmK_le_xm0 hd hσ0 hσ1 hδ ξ
      gcongr
    · refine Eventually.of_forall fun ξ => ?_
      refine Tendsto.mul_const _ (Tendsto.mul_const _ ?_)
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_xmK hd hσ0 hσ1 ξ)
  -- the bound at every δ > 0
  have hbound : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ‖∫ ξ, ((xmK (xK d σ δ) ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)‖ ≤ C * L * (c' * xhom σ h) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine (xsc_core hv hL0 hL hσ0 hδ h).trans ?_
    rw [← hC]
    have hI : ∫ ξ, xmK (xK d σ δ) ξ * ‖𝓕 h ξ‖ ^ 2 ≤ c' * xhom σ h := by
      unfold xhom
      rw [← integral_const_mul]
      have hint : Integrable (fun ξ : Euc d => c' * ((2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖ ^ 2)) :=
        (integrable_xhom hσ0.le h).const_mul c'
      refine integral_mono_of_nonneg (Eventually.of_forall fun ξ =>
        mul_nonneg (xmK_nonneg hσ0 hδ ξ) (sq_nonneg _)) hint (Eventually.of_forall fun ξ => ?_)
      have := xmK_le_xm0 hd hσ0 hσ1 hδ ξ
      rw [hxm0 ξ] at this
      show xmK (xK d σ δ) ξ * ‖𝓕 h ξ‖ ^ 2 ≤ c' * ((2 * Real.pi * ‖ξ‖) ^ (2 * σ) * ‖𝓕 h ξ‖ ^ 2)
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg hC0 hL0)
  have hnorm : ‖∫ ξ, ((xm0 d σ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ)‖ ≤ C * L * (c' * xhom σ h) :=
    le_of_tendsto (hlim.norm) hbound
  have hid : ∫ ξ, ((xm0 d σ ξ : ℝ) : ℂ) * 𝓕 h ξ * 𝓕 ψ (-ξ) = (c' : ℂ) * xpair (2 * σ) h ψ := by
    unfold xpair
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [hxm0 ξ]
    push_cast
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc'] at hnorm
  have : c' * ‖xpair (2 * σ) h ψ‖ ≤ c' * (C * L * xhom σ h) := by nlinarith [hnorm]
  exact le_of_mul_le_mul_left this hc'

end HRS.Commutator.Whole.XNRS
