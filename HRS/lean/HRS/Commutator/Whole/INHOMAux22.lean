import HRS.Commutator.Whole.INHOMAux21

/-!
# CMX-INHOM auxiliary 22: the bound for a component of the cross term
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_cross_comp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ (φ φ₀ φ₁ : SchwartzMap (Euc d) ℂ) (a a₀ a₁ : Euc d → ℝ),
        (∀ x, φ x = ((a x : ℝ) : ℂ)) → (∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ)) →
        (∀ x, φ₁ x = ((a₁ x : ℝ) : ℂ)) → (∀ x, a₀ x = Pleq (1 / 16) a x) →
        (∀ ξ, 𝓕 (⇑φ₀) ξ = cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ) →
        (∀ ξ, 𝓕 (⇑φ₁) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) → ∀ i : Fin d,
        ENNReal.ofReal |∫ x, a₀ x * v x i * inhom_conv (ghiForce s) a₁ x i| ≤
          ENNReal.ofReal (C * K) * inhom_Sob (-alphaE d s) φ := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < alphaE d s := by linarith [inhom_alpha_one hd hs0 hsd]
  obtain ⟨Cb, hCb, hbern⟩ := inhom_a0_Lp2 hd hs0 hsd
  obtain ⟨Cv, hCv, hvhi⟩ := vhi_Lp hd hs0 hsd
  obtain ⟨M1, hM1, hP1⟩ := inhom_Pleq_close (d := d) (L' := 1) one_pos
  obtain ⟨M16, hM16, hP16⟩ := inhom_Pleq_close (d := d) (L' := 1 / 16) (by norm_num)
  obtain ⟨Ch, hCh, hh2⟩ := inhom_h_L2 hd hs0 hsd
  set k0 : ℝ := ((1 + Real.pi ^ 2 / 16) ^ alphaE d s) ^ ((1 : ℝ) / 2) with hk0
  have hk00 : 0 < k0 := by positivity
  have hexp := PROD.prod_exponent_identity hd hsd hs0
  refine ⟨(Cb * Cv + (M1 + M16)) * k0 * Ch + 1, by positivity, ?_⟩
  intro v K hv φ φ₀ φ₁ a a₀ a₁ hφ hφ₀ hφ₁ ha₀ hF₀ hF₁ i
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨L, F, hF0, hL, ⟨w, hrep, hw⟩, hK⟩ := id hv
  have hfd : HasFracData d s v L w F := ⟨hL, hrep, hw⟩
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  -- the scalar component `f` of `v`
  set f : Euc d → ℝ := fun x => v x i with hf
  have hproj : Continuous fun z : Euc d => z i := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous
  have hfc : Continuous f := hproj.comp hL.continuous
  have hfl : ∀ x y, |f x - f y| ≤ L * ‖x - y‖ := by
    intro x y
    have h1 : |(v x - v y) i| ≤ ‖v x - v y‖ := by simpa using PiLp.norm_apply_le (v x - v y) i
    have h2 : ‖v x - v y‖ ≤ L * ‖x - y‖ := by simpa [dist_eq_norm] using hL.dist_le_mul x y
    simpa [hf] using h1.trans h2
  have hfg : ∀ x, |f x| ≤ (‖v 0‖ + L) * (1 + ‖x‖) := by
    intro x
    have h1 : |f x| ≤ |f 0| + L * ‖x‖ := by
      have := hfl x 0
      rw [sub_zero] at this
      calc |f x| = |f 0 + (f x - f 0)| := by ring_nf
        _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
        _ ≤ |f 0| + L * ‖x‖ := by gcongr
    have h0 : |f 0| ≤ ‖v 0‖ := by simpa [hf] using PiLp.norm_apply_le (v 0) i
    nlinarith [norm_nonneg x, norm_nonneg (v 0), mul_nonneg hL0 (norm_nonneg x)]
  -- properties of `a`, `a₀`, `h`
  obtain ⟨hac, hai, ⟨M, hM⟩, ha1, ha2⟩ := inhom_schw_props hφ
  obtain ⟨ha₀c, ha₀i, ⟨M₀, hM₀⟩, ha₀1, ha₀2⟩ := inhom_schw_props hφ₀
  obtain ⟨hhc, Mh, hMh⟩ := inhom_h_props hd hs0 hsd hφ₁ i
  set h : Euc d → ℝ := fun x => inhom_conv (ghiForce s) a₁ x i with hh
  -- the Pleq pieces
  have hu1c : Continuous (Pleq 1 f) := lowv_Pleq_continuous one_pos hfc _ hfg
  have hu16c : Continuous (Pleq (1 / 16) f) := lowv_Pleq_continuous (by norm_num) hfc _ hfg
  have hd1 : ∀ x, |f x - Pleq 1 f x| ≤ M1 * L := fun x => hP1 f L hL0 hfl x
  have hd16 : ∀ x, |f x - Pleq (1 / 16) f x| ≤ M16 * L := fun x => hP16 f L hL0 hfl x
  have hu16g : ∀ x, |Pleq (1 / 16) f x| ≤ (‖v 0‖ + L + M16 * L) * (1 + ‖x‖) := by
    intro x
    have h1 : |Pleq (1 / 16) f x| ≤ |f x| + M16 * L := by
      calc |Pleq (1 / 16) f x| = |f x - (f x - Pleq (1 / 16) f x)| := by ring_nf
        _ ≤ |f x| + |f x - Pleq (1 / 16) f x| := abs_sub _ _
        _ ≤ |f x| + M16 * L := by gcongr; exact hd16 x
    have := hfg x
    have h2 : 0 ≤ M16 * L := mul_nonneg hM16 hL0
    nlinarith [norm_nonneg x]
  -- vanishing of the low part
  have hz := inhom_cross_low hd hs0 hsd hφ₀ hφ₁ hφ ha₀ f hfc hfg i
  have hint1 : Integrable (fun x => a₀ x * Pleq (1 / 16) f x * h x) volume :=
    inhom_int_aqh ha₀i ha₀c hu16c hu16g hhc hMh
  have hint2 : Integrable (fun x => a₀ x * f x * h x) volume :=
    inhom_int_aqh ha₀i ha₀c hfc hfg hhc hMh
  have hsplit : ∫ x, a₀ x * v x i * h x = ∫ x, a₀ x * (f x - Pleq (1 / 16) f x) * h x := by
    have e := integral_sub hint2 hint1
    rw [hz, sub_zero] at e
    rw [← e]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf]; ring
  -- decomposition of `f - P_{≤1/16} f = q₁ + q₂`
  set q₁ : Euc d → ℝ := fun x => f x - Pleq 1 f x with hq₁
  set q₂ : Euc d → ℝ := fun x => Pleq 1 f x - Pleq (1 / 16) f x with hq₂
  have hq1c : Continuous q₁ := hfc.sub hu1c
  have hq2c : Continuous q₂ := hu1c.sub hu16c
  have hhm : AEStronglyMeasurable h volume := hhc.aestronglyMeasurable
  have ha0m : AEStronglyMeasurable a₀ volume := ha₀c.aestronglyMeasurable
  have hq : ∀ x, a₀ x * (f x - Pleq (1 / 16) f x) * h x =
      (a₀ x * q₁ x) * h x + (a₀ x * q₂ x) * h x := by
    intro x; simp only [hq₁, hq₂]; ring
  set S := inhom_Sob (-alphaE d s) φ with hS
  set X := S ^ ((1 : ℝ) / 2) with hX
  have hA0 : eLpNorm a₀ 2 volume ≤ ENNReal.ofReal k0 * X := inhom_a0_L2 hα hφ₀ hF₀
  have hHh : eLpNorm h 2 volume ≤ ENNReal.ofReal Ch * X := hh2 φ φ₁ a₁ hφ₁ hF₁ i
  have hAp : eLpNorm a₀ (ENNReal.ofReal (p2E d s)) volume ≤ ENNReal.ofReal Cb * eLpNorm a₀ 2 volume :=
    hbern a a₀ φ₀ hac ⟨M, hM⟩ ha₀ hφ₀
  -- the `P_{>1}` component
  have hvg : ∀ x, ‖v x‖ ≤ (‖v 0‖ + L) * (1 + ‖x‖) := by
    intro x
    have h1 : ‖v x‖ ≤ ‖v 0‖ + L * ‖x‖ := by
      have := hL.dist_le_mul x 0
      simp only [dist_eq_norm, sub_zero] at this
      calc ‖v x‖ = ‖(v x - v 0) + v 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖v x - v 0‖ + ‖v 0‖ := norm_add_le _ _
        _ ≤ L * ‖x‖ + ‖v 0‖ := by gcongr
        _ = ‖v 0‖ + L * ‖x‖ := by ring
    nlinarith [norm_nonneg x, norm_nonneg (v 0), mul_nonneg hL0 (norm_nonneg x)]
  have hq1eq : ∀ x, q₁ x = Pgt 1 v x i := by
    intro x
    show f x - Pleq 1 f x = (v x - Pleq 1 v x) i
    rw [PiLp.sub_apply, lowv_Pleq_comp one_pos hL.continuous hvg x i]
  obtain ⟨W, hWrep, hWnorm⟩ := hvhi v L w F hfd
  have hQ1 : eLpNorm q₁ (ENNReal.ofReal (p1E d s)) volume ≤ ENNReal.ofReal (Cv * F) := by
    refine le_trans ?_ (le_trans le_add_self hWnorm)
    refine eLpNorm_mono_ae hq1c.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_norm, hq1eq x]
    simpa using PiLp.norm_apply_le (Pgt 1 v x) i
  have hQ2 : ∀ x, |q₂ x| ≤ (M1 + M16) * L := by
    intro x
    have : q₂ x = (f x - Pleq (1 / 16) f x) - (f x - Pleq 1 f x) := by simp only [hq₂]; ring
    rw [this]
    calc |(f x - Pleq (1 / 16) f x) - (f x - Pleq 1 f x)| ≤
          |f x - Pleq (1 / 16) f x| + |f x - Pleq 1 f x| := abs_sub _ _
      _ ≤ M16 * L + M1 * L := add_le_add (hd16 x) (hd1 x)
      _ = _ := by ring
  haveI hT : ENNReal.HolderTriple (ENNReal.ofReal (p2E d s)) (ENNReal.ofReal (p1E d s)) 2 :=
    ⟨by rw [add_comm]; exact hexp⟩
  have hN1 : eLpNorm (fun x => a₀ x * q₁ x) 2 volume ≤
      (ENNReal.ofReal Cb * (ENNReal.ofReal k0 * X)) * ENNReal.ofReal (Cv * F) := by
    refine (inhom_holder_triple (P := ENNReal.ofReal (p2E d s)) (Q := ENNReal.ofReal (p1E d s))
      ha0m hq1c.aestronglyMeasurable).trans ?_
    calc eLpNorm a₀ (ENNReal.ofReal (p2E d s)) volume *
          eLpNorm q₁ (ENNReal.ofReal (p1E d s)) volume
        ≤ (ENNReal.ofReal Cb * eLpNorm a₀ 2 volume) * ENNReal.ofReal (Cv * F) := by gcongr
      _ ≤ _ := by gcongr
  have hN2 : eLpNorm (fun x => a₀ x * q₂ x) 2 volume ≤
      ENNReal.ofReal ((M1 + M16) * L) * (ENNReal.ofReal k0 * X) :=
    (inhom_bdd_mul ha0m hq2c.aestronglyMeasurable hQ2).trans (by gcongr)
  -- the lintegral estimate
  have hmeas1 : Measurable fun x => ‖(a₀ x * q₁ x) * h x‖ₑ :=
    (((ha₀c.mul hq1c).mul hhc).measurable).enorm
  have hmain : ENNReal.ofReal |∫ x, a₀ x * v x i * h x| ≤
      eLpNorm (fun x => a₀ x * q₁ x) 2 volume * eLpNorm h 2 volume +
        eLpNorm (fun x => a₀ x * q₂ x) 2 volume * eLpNorm h 2 volume := by
    rw [hsplit]
    have h1 : ENNReal.ofReal |∫ x, a₀ x * (f x - Pleq (1 / 16) f x) * h x| ≤
        ∫⁻ x, ‖a₀ x * (f x - Pleq (1 / 16) f x) * h x‖ₑ := by
      rw [← Real.enorm_eq_ofReal_abs]
      exact enorm_integral_le_lintegral_enorm _
    refine h1.trans ?_
    calc ∫⁻ x, ‖a₀ x * (f x - Pleq (1 / 16) f x) * h x‖ₑ
        ≤ ∫⁻ x, (‖(a₀ x * q₁ x) * h x‖ₑ + ‖(a₀ x * q₂ x) * h x‖ₑ) := by
          refine lintegral_mono fun x => ?_
          rw [hq x]
          exact enorm_add_le _ _
      _ = (∫⁻ x, ‖(a₀ x * q₁ x) * h x‖ₑ) + ∫⁻ x, ‖(a₀ x * q₂ x) * h x‖ₑ :=
          lintegral_add_left hmeas1 _
      _ ≤ _ := by
          gcongr
          · exact inhom_holder12_lint (ha₀c.mul hq1c).aestronglyMeasurable hhm
          · exact inhom_holder12_lint (ha₀c.mul hq2c).aestronglyMeasurable hhm
  refine hmain.trans ?_
  calc eLpNorm (fun x => a₀ x * q₁ x) 2 volume * eLpNorm h 2 volume +
        eLpNorm (fun x => a₀ x * q₂ x) 2 volume * eLpNorm h 2 volume
      ≤ ((ENNReal.ofReal Cb * (ENNReal.ofReal k0 * X)) * ENNReal.ofReal (Cv * F)) *
          (ENNReal.ofReal Ch * X) +
        (ENNReal.ofReal ((M1 + M16) * L) * (ENNReal.ofReal k0 * X)) * (ENNReal.ofReal Ch * X) := by
        gcongr
    _ = ENNReal.ofReal (Cb * Cv * F * k0 * Ch + (M1 + M16) * L * k0 * Ch) * S := by
        have hS2 : X * X = S := inhom_sqrt_mul_sqrt S
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp (disch := positivity) only [ENNReal.ofReal_mul]
        rw [← hS2]
        ring
    _ ≤ ENNReal.ofReal (((Cb * Cv + (M1 + M16)) * k0 * Ch + 1) * K) * S := by
        gcongr
        have h1 : F ≤ K := by linarith
        have h2 : (L : ℝ) ≤ K := by linarith
        have h3 : 0 ≤ k0 * Ch := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hCb.le hCv.le),
          mul_le_mul_of_nonneg_left h2 (add_nonneg hM1 hM16), mul_nonneg h3 hK0,
          mul_nonneg (mul_nonneg hCb.le hCv.le) h3, mul_nonneg (add_nonneg hM1 hM16) h3]

end HRS.Commutator.Whole
