import HRS.ME.UnifP5A

/-!
# Uniform Lemma 4.6 (cavity response), part B (packet P5)

Uniform versions of `Kt_sup_rate`, `Kt_L2`, `Kt_L2_real` (which do not involve `β`) and `sup_dev_rate`
(`HRS/Equilibrium/CavityResponse.lean`).  Constants are chosen after `d, s, βm, βp, Λ, c` and before
`β ∈ [βm, βp]` and the smooth density `ρ ≤ Λ`.  Here `1 ≤ Λ` is assumed (as in `critical_integrals_unif`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

/-- Uniform `Kt_sup_rate`. -/
theorem Kt_sup_rate_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) (M : ℝ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) →
      ∫ y, h y ∂(withDensityReal ρ) = 0 → ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      ∫ y, |h y| ∂(withDensityReal ρ) ≤ e → ∀ x : Torus d,
        |ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x| ≤ CM * Real.sqrt e := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cc, -, -, h4⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  obtain ⟨B, Cck, hB0, hKU⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  have hΛ0 : 0 < Λ := by linarith
  have hgpm := measurable_gPlus hd hs0 hsd c
  obtain ⟨CM, hCM⟩ := h4 (Λ * M)
  refine ⟨|CM|, abs_nonneg _, fun ρ hρ hΛ h hm hb hint0 e he0 he1 hl x => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hK := hKU ρ hρ hΛ
  have hρm : Measurable ρ := hρ.density.measurable
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb (Classical.arbitrary _))
  set w : Torus d → ℝ := fun y => ρ y * h y with hw
  have hwm : Measurable w := hρm.mul hm
  have hwb : ∀ y, |w y| ≤ Λ * M := by
    intro y
    have h2 : |ρ y| ≤ Λ := by rw [abs_of_pos (hρ.pos y)]; exact hΛ y
    rw [hw]; simp only [abs_mul]
    exact mul_le_mul h2 (hb y) (abs_nonneg _) hΛ0.le
  have hhi : Integrable h (withDensityReal ρ) :=
    Integrable.of_bound (C := M) hm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hl1 : ∫⁻ y, ‖w y‖ₑ ≤ ENNReal.ofReal e := by
    have e1 : ∀ y, ‖w y‖ₑ = ENNReal.ofReal (ρ y) * ‖h y‖ₑ := by
      intro y
      simp only [hw, enorm_mul, Real.enorm_of_nonneg (hρ.density.nonneg y)]
    simp_rw [e1]
    have hmρ : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρm
    have e2 : ∫⁻ y, ENNReal.ofReal (ρ y) * ‖h y‖ₑ = ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) := by
      show _ = ∫⁻ y, ‖h y‖ₑ ∂(volume.withDensity fun x => ENNReal.ofReal (ρ x))
      rw [lintegral_withDensity_eq_lintegral_mul _ hmρ hm.enorm]
      rfl
    rw [e2]
    have e3 : ∫⁻ y, ‖h y‖ₑ ∂(withDensityReal ρ) = ENNReal.ofReal (∫ y, |h y| ∂(withDensityReal ρ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hhi.abs (Eventually.of_forall fun y => abs_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs]
    rw [e3]
    exact ENNReal.ofReal_le_ofReal hl
  have h1 := hCM w e hwm hwb he1 hl1 x
  -- `Kt g μ h = Kt g_+ μ h` since `∫ h dμ = 0`
  have hgi := hK.int x
  have hgh : Integrable (fun y => periodicRiesz d s (x - y) * h y) (withDensityReal ρ) :=
    hgi.mul_bdd hm.aestronglyMeasurable (c := M) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hKt : ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) h x =
      ∫ y, gPlus d s c (x - y) * w y := by
    have e1 : ∫ y, gPlus d s c (x - y) * w y = ResponseAux.Kt (gPlus d s c) (withDensityReal ρ) h x := by
      rw [ResponseAux.Kt_eq_cv hρ.density]; rfl
    rw [e1]
    unfold ResponseAux.Kt
    have : ∀ y, gPlus d s c (x - y) * h y = periodicRiesz d s (x - y) * h y + c * h y := fun y => by
      unfold gPlus; ring
    simp_rw [this]
    rw [integral_add hgh (hhi.const_mul c), integral_const_mul, hint0]
    simp
  rw [hKt]
  have h2 : ‖∫ y, gPlus d s c (x - y) * w y‖ₑ ≤ ENNReal.ofReal (|CM| * Real.sqrt e) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine le_trans (le_of_eq ?_) (h1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))))
    refine lintegral_congr fun y => ?_
    have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
    rw [enorm_mul, Real.enorm_of_nonneg hg0]
  rw [Real.enorm_eq_ofReal_abs] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- Uniform `Kt_L2`. -/
theorem Kt_L2_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ f : Torus d → ℝ, Measurable f →
      ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x) ^ 2)
          ∂(withDensityReal ρ) ≤
        ENNReal.ofReal CS * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cc, hCint, -, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hgpm := measurable_gPlus hd hs0 hsd c
  refine ⟨2 * |Cc| + 2 * c ^ 2, by positivity, fun ρ hρ hΛ f hfm => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have h3 := (hCint ρ hρ hΛ).2.1
  set μ := withDensityReal ρ with hμdef
  have hfe : Measurable fun y => ‖f y‖ₑ := hfm.enorm
  set A : Torus d → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ ∂μ with hA
  set I1 : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ∂μ with hI1
  set K : ℝ≥0∞ := ENNReal.ofReal |c| * I1 with hK
  have hpt : ∀ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ f x) ^ 2) ≤
      2 * (A x) ^ 2 + 2 * K ^ 2 := by
    intro x
    have h1 : ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ f x) ^ 2) =
        ‖ResponseAux.Kt (periodicRiesz d s) μ f x‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h1]
    have h2 : ‖ResponseAux.Kt (periodicRiesz d s) μ f x‖ₑ ≤ A x + K := by
      unfold ResponseAux.Kt
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      have h3' : ∀ y, ‖periodicRiesz d s (x - y) * f y‖ₑ ≤
          ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ + ENNReal.ofReal |c| * ‖f y‖ₑ := by
        intro y
        rw [enorm_mul, ← add_mul]
        refine mul_le_mul' ?_ le_rfl
        have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
        rw [← ENNReal.ofReal_add hg0 (abs_nonneg c), Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have hg0' : 0 ≤ periodicRiesz d s (x - y) + c := hc _
        unfold gPlus
        rw [abs_le]; constructor <;> cases abs_cases c <;> cases abs_cases (periodicRiesz d s (x - y)) <;> linarith
      have hmeasA : Measurable fun y => ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ :=
        (ENNReal.measurable_ofReal.comp (hgpm.comp (measurable_const.sub measurable_id))).mul hfe
      calc ∫⁻ y, ‖periodicRiesz d s (x - y) * f y‖ₑ ∂μ ≤
            ∫⁻ y, (ENNReal.ofReal (gPlus d s c (x - y)) * ‖f y‖ₑ + ENNReal.ofReal |c| * ‖f y‖ₑ) ∂μ :=
            lintegral_mono h3'
        _ = A x + K := by
            rw [lintegral_add_left hmeasA, lintegral_const_mul _ hfe]
    calc ‖ResponseAux.Kt (periodicRiesz d s) μ f x‖ₑ ^ 2 ≤ (A x + K) ^ 2 := by gcongr
      _ ≤ 2 * (A x ^ 2 + K ^ 2) := by
          have := ENNReal.rpow_add_le_mul_rpow_add_rpow (A x) K (p := 2) (by norm_num)
          rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_two, ENNReal.rpow_two,
            ENNReal.rpow_two] at this
          exact this
      _ = _ := by ring
  have hmA : Measurable A := by
    refine Measurable.lintegral_prod_right' (f := fun q : Torus d × Torus d =>
      ENNReal.ofReal (gPlus d s c (q.1 - q.2)) * ‖f q.2‖ₑ) ?_
    exact (ENNReal.measurable_ofReal.comp (hgpm.comp (measurable_fst.sub measurable_snd))).mul
      (hfe.comp measurable_snd)
  have hI1sq : I1 ^ 2 ≤ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
    have := lintegral_mul_sq_le μ (fun y => ‖f y‖ₑ) (fun _ => 1) hfe.aemeasurable aemeasurable_const
    simpa [hI1] using this
  have hK2 : K ^ 2 = ENNReal.ofReal (c ^ 2) * I1 ^ 2 := by
    rw [hK, mul_pow, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  calc ∫⁻ x, ENNReal.ofReal ((ResponseAux.Kt (periodicRiesz d s) μ f x) ^ 2) ∂μ
      ≤ ∫⁻ x, (2 * (A x) ^ 2 + 2 * K ^ 2) ∂μ := lintegral_mono hpt
    _ = 2 * ∫⁻ x, (A x) ^ 2 ∂μ + 2 * K ^ 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ (hmA.pow_const 2)]
        simp
    _ ≤ 2 * (ENNReal.ofReal |Cc| * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) +
          2 * (ENNReal.ofReal (c ^ 2) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) := by
        refine add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_)
        · exact (h3 f hfm).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_abs_self _)) le_rfl)
        · exact hK2.trans_le (mul_le_mul' le_rfl hI1sq)
    _ = ENNReal.ofReal (2 * |Cc| + 2 * c ^ 2) * ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        ring

/-- Uniform `Kt_L2_real`. -/
theorem Kt_L2_real_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ f : Torus d → ℝ, Measurable f → ∀ M : ℝ, (∀ y, |f y| ≤ M) →
      Integrable (fun x => (ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x) ^ 2)
          (withDensityReal ρ) ∧
        ∫ x, (ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x) ^ 2 ∂(withDensityReal ρ) ≤
          CS * ∫ y, f y ^ 2 ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨CS, hCS0, hCSU⟩ := Kt_L2_unif hd hcrit hc Λ hΛ1
  refine ⟨CS, hCS0, fun ρ hρ hΛ f hfm M hfM => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hCS := hCSU ρ hρ hΛ
  have hfi : Integrable (fun y => f y ^ 2) (withDensityReal ρ) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable (M ^ 2) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := hfM y
      nlinarith [abs_nonneg (f y), sq_abs (f y)])
  have hI0 : 0 ≤ ∫ y, f y ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun y => sq_nonneg _
  have h1 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(withDensityReal ρ) = ENNReal.ofReal (∫ y, f y ^ 2 ∂(withDensityReal ρ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h2 := hCS f hfm
  rw [h1, ← ENNReal.ofReal_mul hCS0] at h2
  exact integral_sq_le_of_lintegral (measurable_Kt hd hs0 hsd (β := 1) one_pos hρ hfm) (by positivity) h2

set_option maxHeartbeats 1600000 in
/-- Uniform `sup_dev_rate`. -/
theorem sup_dev_rate_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) → ∀ x : Torus d,
      |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤
        C * Real.sqrt (deltaN d s (n + 1)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Mp, hMp1, hMpU⟩ := pDens_bounds_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mq, hMq0, hMqU⟩ := qDens_bound_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Kg, hKg0, hKgU⟩ := convAbs_bound_unif hd hs0 hsd Λ
  obtain ⟨Cd, hCdU⟩ := insDefect_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨C2, hC20, hC2U⟩ := L2_all_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨CL, hCL0, hCLU⟩ := cavity_L2_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨CM, hCM0, hCMU⟩ := Kt_sup_rate_unif hd hcrit hc Λ hΛ1 (1 + Mq)
  set Ce : ℝ := C2 + CL with hCe
  have hCe0 : 0 ≤ Ce := by positivity
  set C3p : ℝ := βp * CM * Real.sqrt Ce + βp * (Kg * Mq) + |Cd| with hC3p
  have hC3p0 : 0 ≤ C3p := by
    have : 0 ≤ βp := hβm.le.trans hββ
    positivity
  refine ⟨max (2 * C3p * Real.exp (2 * C3p)) ((Mp + 1) * Real.sqrt Ce), by positivity, ?_⟩
  intro β hβI ρ hρ hΛ n hn lam hlamdef x
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hMp := hMpU β hβI ρ hρ hΛ
  have hMq := hMqU β hβI ρ hρ hΛ
  have hKg := hKgU ρ hρ hΛ
  have hCd := hCdU β hβI ρ hρ hΛ
  have hC2 := hC2U β hβI ρ hρ hΛ
  have hCL := hCLU β hβI ρ hρ hΛ
  have hCM := hCMU ρ hρ hΛ
  set C3 : ℝ := β * CM * Real.sqrt Ce + β * (Kg * Mq) + |Cd| with hC3
  have hC30 : 0 ≤ C3 := by positivity
  have hC3le : C3 ≤ C3p := by
    have h1 : β ≤ βp := hβI.2
    have h2 : 0 ≤ CM * Real.sqrt Ce := by positivity
    have h3 : 0 ≤ Kg * Mq := by positivity
    simp only [hC3, hC3p]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2, mul_le_mul_of_nonneg_right h1 h3]
  have hmax1 : 2 * C3 * Real.exp (2 * C3) ≤
      max (2 * C3p * Real.exp (2 * C3p)) ((Mp + 1) * Real.sqrt Ce) :=
    (by gcongr : 2 * C3 * Real.exp (2 * C3) ≤ 2 * C3p * Real.exp (2 * C3p)).trans (le_max_left _ _)
  obtain ⟨hlam, hln, hlam1⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hN : 2 ≤ n + 1 := by omega
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlam' : lam = β / ((n + 1 : ℕ) : ℝ) := hlamdef
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ1 : deltaN d s (n + 1) ≤ 1 := deltaN_le_one hs0 hsd (by omega) (n + 1) (by omega)
  have hδinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ deltaN d s (n + 1) := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
  have hsδ : Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) ≤ deltaN d s (n + 1) := by
    rw [Real.sqrt_le_left hδ0]
    have : deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ) ≤ deltaN d s (n + 1) ^ 2 := by
      rw [div_eq_mul_inv, sq]
      exact mul_le_mul_of_nonneg_left hδinv hδ0
    exact this
  have hacq := hMq (n + 1) hN
  have hac : firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) ≪
      withDensityReal ρ := by
    subst hlam'; exact hacq.1
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mq := by
    subst hlam'; exact hacq.2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y ≤ Mp := by
    subst hlam'; exact fun y => (hMp (n + 1) hN y).2
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hp0 : ∀ y, 0 < pDens (periodicRiesz d s) (withDensityReal ρ) n lam β y :=
    pDens_pos hd hs0 hsd hρ hlam hln
  set p := pDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hp
  set q := qDens (periodicRiesz d s) (withDensityReal ρ) n lam β with hq
  set μ := withDensityReal ρ with hμdef
  have hq0 : ∀ y, 0 ≤ q y := fun y => ENNReal.toReal_nonneg
  -- the case split
  by_cases hbig : Ce * deltaN d s (n + 1) ≤ 1
  · -- `L¹` bound on `1 - q`
    set qb : Torus d → ℝ := fun y => min (q y) Mq with hqbdef
    have hqbm : Measurable qb := hqm.min measurable_const
    have hqbq : q =ᵐ[μ] qb := hqb.mono fun y hy => by simp only [hqbdef, min_eq_left hy]
    have hqb0 : ∀ y, 0 ≤ qb y := fun y => le_min (hq0 y) hMq0.le
    have hqbM : ∀ y, qb y ≤ Mq := fun y => min_le_right _ _
    obtain ⟨hqi, hq1⟩ := integral_qDens hd hs0 hsd hβ hρ hn hlamdef hac
    have hh0 : ∫ y, (1 - qb y) ∂μ = 0 := by
      have e : ∫ y, (1 - qb y) ∂μ = ∫ y, (1 - q y) ∂μ :=
        integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
      rw [e, integral_sub (integrable_const _) hqi, hq1]; simp
    -- `L²` bounds
    have hp2 : Real.sqrt (∫ y, (p y - 1) ^ 2 ∂μ) ≤ C2 * deltaN d s (n + 1) :=
      Real.sqrt_le_iff.2 ⟨by positivity, hC2 n hn lam hlamdef⟩
    have hpq2 : Real.sqrt (∫ y, (p y - q y) ^ 2 ∂μ) ≤ CL * deltaN d s (n + 1) := by
      have := hCL n hn lam hlamdef
      exact this.trans (mul_le_mul_of_nonneg_left hsδ hCL0)
    have hpb' : ∀ y, |p y - 1| ≤ Mp + 1 := fun y => by
      rw [abs_le]; constructor <;> linarith [hp0 y, hpb y]
    have hpqb : ∀ y, |p y - qb y| ≤ Mp + Mq := fun y => by
      rw [abs_le]; constructor <;> linarith [hp0 y, hpb y, hqb0 y, hqbM y]
    have hl1a : ∫ y, |p y - 1| ∂μ ≤ C2 * deltaN d s (n + 1) :=
      (l1_le_sqrt (h := fun y => p y - 1) (hpm.sub measurable_const) hpb').trans hp2
    have hl1b : ∫ y, |p y - qb y| ∂μ ≤ CL * deltaN d s (n + 1) := by
      have e : ∫ y, (p y - qb y) ^ 2 ∂μ = ∫ y, (p y - q y) ^ 2 ∂μ :=
        integral_congr_ae (hqbq.mono fun y hy => by simp only [← hy])
      refine (l1_le_sqrt (h := fun y => p y - qb y) (hpm.sub hqbm) hpqb).trans ?_
      rw [e]; exact hpq2
    have hpi : Integrable p μ := Integrable.of_bound (C := Mp) hpm.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_pos (hp0 y)]; exact hpb y)
    have hqbi : Integrable qb μ := Integrable.of_bound (C := Mq) hqbm.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hqb0 y)]; exact hqbM y)
    have hl1 : ∫ y, |1 - qb y| ∂μ ≤ Ce * deltaN d s (n + 1) := by
      have h1 : Integrable (fun y => |p y - 1|) μ := (hpi.sub (integrable_const _)).abs
      have h2 : Integrable (fun y => |p y - qb y|) μ := (hpi.sub hqbi).abs
      have h3 : Integrable (fun y => |1 - qb y|) μ := ((integrable_const (1 : ℝ)).sub hqbi).abs
      have hle : ∫ y, |1 - qb y| ∂μ ≤ ∫ y, (|p y - 1| + |p y - qb y|) ∂μ := by
        refine integral_mono h3 (h1.add h2) fun y => ?_
        have := abs_add_le (1 - p y) (p y - qb y)
        rw [show (1 - p y) + (p y - qb y) = 1 - qb y by ring, abs_sub_comm 1 (p y)] at this
        exact this
      rw [integral_add h1 h2] at hle
      rw [hCe]; nlinarith
    have hbb : ∀ y, |1 - qb y| ≤ 1 + Mq := fun y => by
      rw [abs_le]; constructor <;> linarith [hqb0 y, hqbM y]
    have hKt := hCM (fun y => 1 - qb y) (measurable_const.sub hqbm) hbb hh0
      (Ce * deltaN d s (n + 1)) (by positivity) hbig hl1
    have hKt' : ∀ x, |ResponseAux.Kt (periodicRiesz d s) μ (fun y => 1 - q y) x| ≤
        CM * Real.sqrt (Ce * deltaN d s (n + 1)) := by
      intro x
      have hae : (fun y => 1 - q y) =ᵐ[μ] fun y => 1 - qb y :=
        hqbq.mono fun y hy => by simp only [← hy]
      rw [ResponseAux.Kt_congr _ hae]
      exact hKt x
    have hu : ∀ y, |uIns (periodicRiesz d s) μ n lam β y| ≤
        β * |ResponseAux.Kt (periodicRiesz d s) μ (fun y => 1 - q y) y| + lam * (Kg * Mq) +
          |insDefect (periodicRiesz d s) μ n lam β y| := fun y =>
      uIns_le_aux hd hs0 hsd hβ hρ hn hlamdef hac hMq0.le hqb (fun x => hKg x) y
    have hlamδ : lam ≤ β * deltaN d s (n + 1) := by
      rw [hlam', div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hδinv hβ.le
    have hsq : Real.sqrt (Ce * deltaN d s (n + 1)) = Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)) :=
      Real.sqrt_mul hCe0 _
    have hδs : deltaN d s (n + 1) ≤ Real.sqrt (deltaN d s (n + 1)) := by
      have h0 := Real.sqrt_nonneg (deltaN d s (n + 1))
      have h1 := Real.sq_sqrt hδ0
      have h2 : Real.sqrt (deltaN d s (n + 1)) ≤ 1 := by
        rw [Real.sqrt_le_one]; exact hδ1
      nlinarith
    have hsδ1 : Real.sqrt (deltaN d s (n + 1)) ≤ 1 := by rw [Real.sqrt_le_one]; exact hδ1
    have hu_le : ∀ y, |uIns (periodicRiesz d s) μ n lam β y| ≤ C3 * Real.sqrt (deltaN d s (n + 1)) := by
      intro y
      refine (hu y).trans ?_
      have hD : 0 ≤ insDefect (periodicRiesz d s) μ n lam β y ∧
          insDefect (periodicRiesz d s) μ n lam β y ≤ Cd * deltaN d s (n + 1) := by
        have := hCd (n + 1) hN y
        rw [← hlam'] at this
        exact ⟨this.1, this.2.1⟩
      have hD1 : |insDefect (periodicRiesz d s) μ n lam β y| ≤ |Cd| * deltaN d s (n + 1) := by
        rw [abs_of_nonneg hD.1]
        exact hD.2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
      have h1 : β * |ResponseAux.Kt (periodicRiesz d s) μ (fun y => 1 - q y) y| ≤
          β * (CM * (Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)))) := by
        rw [← hsq]; exact mul_le_mul_of_nonneg_left (hKt' y) hβ.le
      have h2 : lam * (Kg * Mq) ≤ β * (Kg * Mq) * Real.sqrt (deltaN d s (n + 1)) := by
        calc lam * (Kg * Mq) ≤ (β * deltaN d s (n + 1)) * (Kg * Mq) :=
              mul_le_mul_of_nonneg_right hlamδ (by positivity)
          _ ≤ (β * Real.sqrt (deltaN d s (n + 1))) * (Kg * Mq) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδs hβ.le) (by positivity)
          _ = _ := by ring
      have h3 : |Cd| * deltaN d s (n + 1) ≤ |Cd| * Real.sqrt (deltaN d s (n + 1)) :=
        mul_le_mul_of_nonneg_left hδs (abs_nonneg _)
      have e : C3 * Real.sqrt (deltaN d s (n + 1)) = β * (CM * (Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)))) +
          β * (Kg * Mq) * Real.sqrt (deltaN d s (n + 1)) + |Cd| * Real.sqrt (deltaN d s (n + 1)) := by
        simp only [hC3]; ring
      linarith [h1, h2, h3, hD1, e]
    have hη : 0 ≤ C3 * Real.sqrt (deltaN d s (n + 1)) := mul_nonneg hC30 (Real.sqrt_nonneg _)
    have hdev := pDens_dev hd hs0 hsd hρ hlam hln hη hu_le x
    refine hdev.trans ?_
    have hexp : Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) - 1 ≤
        2 * (C3 * Real.sqrt (deltaN d s (n + 1))) *
          Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) := by
      have h := Real.add_one_le_exp (-(2 * (C3 * Real.sqrt (deltaN d s (n + 1)))))
      have h3 : Real.exp (-(2 * (C3 * Real.sqrt (deltaN d s (n + 1))))) *
          Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (2 * (C3 * Real.sqrt (deltaN d s (n + 1))))]
    refine hexp.trans ?_
    have hE : Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1)))) ≤ Real.exp (2 * C3) :=
      Real.exp_le_exp.2 (by
        have := mul_le_mul_of_nonneg_left hsδ1 hC30
        linarith)
    calc 2 * (C3 * Real.sqrt (deltaN d s (n + 1))) *
          Real.exp (2 * (C3 * Real.sqrt (deltaN d s (n + 1))))
        ≤ 2 * (C3 * Real.sqrt (deltaN d s (n + 1))) * Real.exp (2 * C3) :=
          mul_le_mul_of_nonneg_left hE (mul_nonneg (by norm_num) hη)
      _ = (2 * C3 * Real.exp (2 * C3)) * Real.sqrt (deltaN d s (n + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmax1 (Real.sqrt_nonneg _)
  · push Not at hbig
    have hpx : |p x - 1| ≤ Mp + 1 := by
      rw [abs_le]; constructor <;> linarith [hp0 x, hpb x]
    refine hpx.trans ?_
    have h1 : 1 ≤ Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1)) := by
      rw [← Real.sqrt_mul hCe0]
      exact Real.one_le_sqrt.2 hbig.le
    calc Mp + 1 ≤ (Mp + 1) * (Real.sqrt Ce * Real.sqrt (deltaN d s (n + 1))) :=
          le_mul_of_one_le_right (by linarith) h1
      _ = ((Mp + 1) * Real.sqrt Ce) * Real.sqrt (deltaN d s (n + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)

end HRS.ME.Unif

end
