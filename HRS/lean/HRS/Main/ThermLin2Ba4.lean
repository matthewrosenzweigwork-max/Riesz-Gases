import HRS.Main.ThermLin2Ba1

/-!
# THERMLIN2, packet Ba, part 4: A4 (`tl2_init_shift`)

Direct coupling on `P'.prod κ`: the window of `Uev · 0 w.2 + Z · w.1` equals `L w.2 + window Z (w.1)` a.e. (`t25p_win_add`),
with `‖L x‖ ≤ K e^{-ca} ‖x‖`, and `wassersteinE_le_of_coupling`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- A4 proof. -/
theorem tl2_init_shift_proof {m T a K c : ℝ} (hT : 0 < T) (ha : 0 ≤ a) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (Uev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hplain : IsPlainEvolution Uev (a + T))
    (hdec : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Uev t 0‖ ≤ K * Real.exp (-c * t))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZm : ∀ t, Measurable (Z t))
    (hZc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (κ : Measure (NegSobolev d m)) [IsProbabilityMeasure κ] (p : ℝ) (hp : p = 1 ∨ p = 2) :
    wassersteinE p
      (law (P'.prod κ) (Uniform.windowPath a T (fun t (w : Ω' × NegSobolev d m) => Uev t 0 w.2 + Z t w.1)))
      (law P' (Uniform.windowPath a T Z)) ≤
    ENNReal.ofReal (K * Real.exp (-c * a)) * (∫⁻ x, ‖x‖ₑ ^ p ∂κ) ^ (1 / p) := by
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hp0 : 0 < p := by linarith
  have hcont := hplain.2.2
  have hb : ∀ t : ℝ, 0 ≤ t → t ≤ a + T → ‖Uev t 0‖ ≤ K := by
    intro t ht htT
    refine (hdec t ht htT).trans ?_
    have : Real.exp (-c * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    nlinarith
  set L := t25p_L (T := T) ha Uev hcont hK hb with hL
  have hLn : ∀ x : NegSobolev d m, ‖L x‖ ≤ K * Real.exp (-c * a) * ‖x‖ := by
    intro x
    refine HRS.Uniform.Q45.norm_pcm_le _ (by positivity) fun s => ?_
    rw [hL, t25p_pcm_L]
    have hs := s.2
    refine ((Uev _ 0).le_opNorm x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (hdec _ (by linarith [hs.1]) (by linarith [hs.2])).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
    nlinarith [hs.1]
  have hwin : AEMeasurable (Uniform.windowPath a T Z) P' :=
    HRS.Uniform.Comp28.aem_wp_a P' ha hT.le Z (fun t _ => hZm t) hZc
  have hwin' : AEMeasurable (fun w : Ω' × NegSobolev d m => Uniform.windowPath a T Z w.1) (P'.prod κ) :=
    hwin.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have key : (Uniform.windowPath a T
      (fun t (w : Ω' × NegSobolev d m) => Uev t 0 w.2 + Z t w.1)) =ᵐ[P'.prod κ]
      fun w => L w.2 + Uniform.windowPath a T Z w.1 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hZc] with w h1
    have h3 := t25p_win_add ha Uev hcont hK hb hT.le w.2
      (fun t (w' : Ω' × NegSobolev d m) => Z t w'.1) (ω := w) h1
    exact h3
  have hX : AEMeasurable (Uniform.windowPath a T
      (fun t (w : Ω' × NegSobolev d m) => Uev t 0 w.2 + Z t w.1)) (P'.prod κ) :=
    AEMeasurable.congr (((L.continuous.measurable.comp measurable_snd).aemeasurable).add hwin') key.symm
  have hlaw : law P' (Uniform.windowPath a T Z) =
      law (P'.prod κ) (fun w : Ω' × NegSobolev d m => Uniform.windowPath a T Z w.1) := by
    unfold law
    have : (P'.prod κ).map Prod.fst = P' := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    conv_lhs => rw [← this]
    exact AEMeasurable.map_map_of_aemeasurable (by rwa [this]) measurable_fst.aemeasurable
  rw [hlaw]
  refine (wassersteinE_le_of_coupling (P'.prod κ) p hp1 _ _ hX hwin').trans ?_
  set M : ℝ := K * Real.exp (-c * a) with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ᵐ w ∂(P'.prod κ), ENNReal.ofReal (‖Uniform.windowPath a T
      (fun t (w : Ω' × NegSobolev d m) => Uev t 0 w.2 + Z t w.1) w - Uniform.windowPath a T Z w.1‖ ^ p) ≤
      ENNReal.ofReal M ^ p * ‖w.2‖ₑ ^ p := by
    filter_upwards [key] with w hw
    rw [hw, add_sub_cancel_right]
    calc ENNReal.ofReal (‖L w.2‖ ^ p) ≤ ENNReal.ofReal ((M * ‖w.2‖) ^ p) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hLn _) hp0.le)
      _ = ENNReal.ofReal M ^ p * ‖w.2‖ₑ ^ p := by
          rw [Real.mul_rpow hM0 (norm_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg hM0 _),
            ENNReal.ofReal_rpow_of_nonneg hM0 hp0.le, ← ofReal_norm,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  have hint : ∫⁻ w, ENNReal.ofReal M ^ p * ‖w.2‖ₑ ^ p ∂(P'.prod κ) = ENNReal.ofReal M ^ p * ∫⁻ x, ‖x‖ₑ ^ p ∂κ := by
    have hf : Measurable (fun x : NegSobolev d m => ENNReal.ofReal M ^ p * ‖x‖ₑ ^ p) :=
      (measurable_enorm.pow_const p).const_mul _
    have h1 := lintegral_map (μ := P'.prod κ) hf measurable_snd
    rw [Measure.map_snd_prod, measure_univ, one_smul] at h1
    rw [← h1, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
  calc _ ≤ (∫⁻ w, ENNReal.ofReal M ^ p * ‖w.2‖ₑ ^ p ∂(P'.prod κ)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (by positivity)
    _ = ENNReal.ofReal M * (∫⁻ x, ‖x‖ₑ ^ p ∂κ) ^ (1 / p) := by
        rw [hint, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

example := (@tl2_init_shift_proof : type_of% @tl2_init_shift)

end HRS.ThermLin.Plan2
