import HRS.ME.UnifP5E

/-!
# Uniform Lemma 4.6 (cavity response), part F (packet P5)

Uniform versions of `field_L1'` (`HRS/Equilibrium/CavityField.lean`), `psi_bound` and `pole_prefactor`
(`HRS/Equilibrium/CavityPsi.lean`): the `L¹` bound of the cavity field, the bound on the prefactor `ψ`, and the
pole-marginal density estimate, with constants chosen after `d, s, βm, βp, Λ, c` and before `β ∈ [βm, βp]` and the
smooth density `ρ ≤ Λ`.  The auxiliary lemmas `gTrunc_bounds`, `small_facts`, `v_integral`, `Z_bounds`,
`measurable_field_*`, `critPole_formula` take their constants as parameters and are reused.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

set_option maxHeartbeats 1600000 in
/-- Uniform `field_L1'`. -/
theorem field_L1_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|)
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
      ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y|
        ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
        C * Real.sqrt (deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cv, hCv0, hCvU⟩ := var_trunc_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  obtain ⟨Cm, hCm0, hCmU⟩ := mean_trunc_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  obtain ⟨Ct, hCt0, hCtU⟩ := tail_bound_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  have hβp : 0 ≤ βp := hβm.le.trans hββ
  refine ⟨βp * Real.sqrt (2 * Cv) + 3 * Cm + 3 * βp + Ct, by positivity,
    fun β hβI ρ hρ hΛ N hN x t ht y => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hCv := hCvU β hβI ρ hρ hΛ
  have hCm := hCmU β hβI ρ hρ hΛ
  have hCt := hCtU β hβI ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : 0 < N - 1 := by omega
  have hn' : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by rw [hn']; linarith
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  have hsq0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hN0
  set H : ℝ := 2 + Real.sqrt N with hHdef
  have hH2 : 2 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hgm := measurable_gPlus hd hs0 hsd c
  set f : Torus d → ℝ := fun z => gTrunc d s c H (y - z) with hf
  have hfm : Measurable f := (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0.le (y - z)).1
  have hfH : ∀ z, f z ≤ H := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0.le (y - z)).2.1
  have hfb : ∀ z, |f z| ≤ H := fun z => by rw [abs_of_nonneg (hf0 z)]; exact hfH z
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - gTrunc d s c H (y - z) with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z => sub_nonneg.2 (gTrunc_bounds hd hcrit hβ hρ hc H hH0.le (y - z)).2.2
  have hGfr : ∀ z, gPlus d s c (y - z) = f z + r z := fun z => by simp only [hf, hr]; ring
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  set ν := firstMarginal P with hν
  set h := convMeasure (gPlus d s c) (withDensityReal ρ) y with hh
  set EA : ℝ := (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ z, f z ∂ν with hEA
  set A : Config d (N - 1) → ℝ := fun Y => (β / N) * ((N - 1 : ℕ) : ℝ) * fracF f Y with hA
  set R : Config d (N - 1) → ℝ := fun Y => (β / N) * ∑ j, (gPlus d s c (y - Y j) - gTrunc d s c H (y - Y j))
    with hR
  have hrm : Measurable r :=
    (hgm.comp (measurable_const.sub measurable_id)).sub
      ((hgm.comp (measurable_const.sub measurable_id)).min measurable_const)
  -- pointwise bound
  have hpt : ∀ Y : Config d (N - 1), |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ≤
      |A Y - EA| + |EA - β * h| + (β / N) * H + R Y := by
    intro Y
    have e1 : ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), gPlus d s c (y - Y j) =
        (∑ j, f (Y j)) - f (Y ⟨0, hn⟩) + ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) := by
      rw [Finset.sum_congr rfl (fun j _ => hGfr (Y j)), Finset.sum_add_distrib,
        Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    have e2 : A Y = (β / N) * ∑ j, f (Y j) := by
      simp only [hA]; unfold fracF
      have : ((N - 1 : ℕ) : ℝ) ≠ 0 := hn0.ne'
      field_simp
    have e3 : cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y =
        (A Y - EA) + (EA - β * h) - (β / N) * f (Y ⟨0, hn⟩) +
          (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) := by
      unfold cavityField
      rw [e1, ← hh, e2]; ring
    rw [e3]
    have hr1 : 0 ≤ ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) :=
      Finset.sum_nonneg fun j _ => hr0 _
    have hr2 : ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) ≤ ∑ j, r (Y j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => hr0 _
    have h3 : (β / N) * f (Y ⟨0, hn⟩) ≤ (β / N) * H := mul_le_mul_of_nonneg_left (hfH _) hlam
    have h3' : 0 ≤ (β / N) * f (Y ⟨0, hn⟩) := mul_nonneg hlam (hf0 _)
    have h4 : (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) ≤ R Y :=
      mul_le_mul_of_nonneg_left hr2 hlam
    have h4' : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase (⟨0, hn⟩ : Fin (N - 1)), r (Y j) :=
      mul_nonneg hlam hr1
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (A Y - EA), neg_abs_le (EA - β * h), le_abs_self (A Y - EA),
      le_abs_self (EA - β * h)]
  have hRm : Measurable R :=
    (Finset.measurable_sum _ fun j _ => hrm.comp (measurable_pi_apply j)).const_mul _
  have hRint : Integrable R P := (hCt N hN x t ht y H hH2).1
  have hRle : ∫ Y, R Y ∂P ≤ Ct / H := (hCt N hN x t ht y H hH2).2
  have hR0 : ∀ Y, 0 ≤ R Y := fun Y => mul_nonneg hlam (Finset.sum_nonneg fun j _ => hr0 _)
  have hfrm : Measurable (fracF (n := N - 1) f) := measurable_fracF hfm
  have hmem : MemLp (fracF (n := N - 1) f) 2 P :=
    MemLp.of_bound hfrm.aestronglyMeasurable H (Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs]; exact abs_fracF_le hn hfb Y)
  have hfrint : Integrable (fracF (n := N - 1) f) P := hmem.integrable (by norm_num)
  have hEF : ∫ Y, fracF f Y ∂P = ∫ z, f z ∂ν :=
    integral_fracF hn hfm hfb P (poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t)
  have hAEA : ∀ Y, A Y - EA = (β / N) * ((N - 1 : ℕ) : ℝ) * (fracF f Y - ∫ Y', fracF f Y' ∂P) := by
    intro Y; rw [hEF]; simp only [hA, hEA]; ring
  have hδ0 : 0 ≤ deltaN d s N := (inv_nonneg.2 hN0.le).trans (inv_le_deltaN (d := d) hs0 N (by omega))
  have hc0 : 0 ≤ (β / N) * ((N - 1 : ℕ) : ℝ) := by positivity
  have hc1 : (β / N) * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [hn', div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hI1 : Integrable (fun Y => |A Y - EA|) P :=
    (((hfrint.const_mul ((β / N) * ((N - 1 : ℕ) : ℝ))).sub (integrable_const EA))).abs
  have hT1 : ∫ Y, |A Y - EA| ∂P ≤ β * Real.sqrt (2 * Cv) * Real.sqrt (deltaN d s N) := by
    have e1 : ∫ Y, |A Y - EA| ∂P =
        (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ Y, |fracF f Y - ∫ Y', fracF f Y' ∂P| ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
      show |A Y - EA| = _
      rw [hAEA Y, abs_mul, abs_of_nonneg hc0]
    have e2 := l1_le_sqrt_var hmem
    have hvar := hCv N hN x t ht y H hH2
    have hlogH : Real.log H ≤ (N : ℝ) * deltaN d s N := by
      have hN1 : 1 ≤ N := by omega
      have h2N : H ≤ 2 * N := by
        have : Real.sqrt N ≤ N := by nlinarith [Real.sq_sqrt hN0.le, Real.sqrt_nonneg (N : ℝ),
          (Real.one_le_sqrt.2 (by exact_mod_cast hN1 : (1 : ℝ) ≤ N))]
        simp only [hHdef]; linarith
      calc Real.log H ≤ Real.log (2 * N) := Real.log_le_log hH0 h2N
        _ = Real.log 2 + Real.log N := Real.log_mul (by norm_num) hN0.ne'
        _ ≤ 1 + Real.log N := by
            have := Real.log_two_lt_d9
            linarith
        _ = _ := (N_mul_deltaN_crit hcrit hN1).symm
    have hvar2 : Var[fracF (n := N - 1) f; P] ≤ 2 * Cv * deltaN d s N := by
      refine hvar.trans ?_
      rw [div_le_iff₀ hn0]
      have h1 : Cv * Real.log H ≤ Cv * ((N : ℝ) * deltaN d s N) := mul_le_mul_of_nonneg_left hlogH hCv0
      have h2 : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by rw [hn']; linarith
      nlinarith [mul_nonneg hCv0 hδ0]
    have e3 : Real.sqrt (Var[fracF (n := N - 1) f; P]) ≤
        Real.sqrt (2 * Cv) * Real.sqrt (deltaN d s N) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith [hvar2])
    rw [e1]
    calc (β / N) * ((N - 1 : ℕ) : ℝ) * ∫ Y, |fracF f Y - ∫ Y', fracF f Y' ∂P| ∂P
        ≤ β * (Real.sqrt (2 * Cv) * Real.sqrt (deltaN d s N)) :=
          mul_le_mul hc1 (e2.trans e3) (integral_nonneg fun Y => abs_nonneg _) hβ.le
      _ = _ := by ring
  have hvm : Measurable fun Y : Config d (N - 1) =>
      cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y := by
    unfold cavityField
    exact ((Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _).sub measurable_const
  have hvint : Integrable (fun Y => |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y|) P :=
    Integrable.mono' ((((hI1.add (integrable_const _)).add (integrable_const _)).add hRint))
      hvm.abs.aestronglyMeasurable (Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs, abs_abs]; exact hpt Y)
  refine ⟨hvint, ?_⟩
  have hbd : ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P ≤
      ∫ Y, (|A Y - EA| + |EA - β * h| + (β / N) * H + R Y) ∂P := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun Y => abs_nonneg _)
      ((((hI1.add (integrable_const _)).add (integrable_const _)).add hRint))
      (Eventually.of_forall hpt)
  have hsumint : ∫ Y, (|A Y - EA| + |EA - β * h| + (β / N) * H + R Y) ∂P =
      ∫ Y, |A Y - EA| ∂P + |EA - β * h| + (β / N) * H + ∫ Y, R Y ∂P := by
    have i2 : Integrable (fun Y => |A Y - EA| + |EA - β * h|) P := hI1.add (integrable_const _)
    have i3 : Integrable (fun Y => |A Y - EA| + |EA - β * h| + (β / N) * H) P :=
      i2.add (integrable_const _)
    rw [integral_add i3 hRint, integral_add i2 (integrable_const _), integral_add hI1 (integrable_const _)]
    simp
  obtain ⟨u1, u2⟩ := small_facts hd hcrit hβ hρ hc hs0 hN
  set u : ℝ := Real.sqrt (deltaN d s N) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hH1 : 1 / H ≤ u := by
    refine le_trans ?_ u2
    refine one_div_le_one_div_of_le hsq0 ?_
    simp only [hHdef]; linarith
  have hmean := hCm N hN x t ht y H hH2
  have hmean' : |EA - β * h| ≤ Cm * (u + 1 / (N : ℝ) + 1 / H) := hmean
  have hLH : (β / N) * H ≤ 3 * β * u := by
    have e1 : (β / N) * H = 2 * β * (1 / (N : ℝ)) + β * (1 / Real.sqrt N) := by
      simp only [hHdef]
      have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      field_simp
      nlinarith [this]
    rw [e1]
    linarith only [mul_le_mul_of_nonneg_left u1 hβ.le, mul_le_mul_of_nonneg_left u2 hβ.le]
  have hRu : Ct / H ≤ Ct * u := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hH1 hCt0
  have hmu : Cm * (u + 1 / (N : ℝ) + 1 / H) ≤ 3 * Cm * u := by
    linarith only [mul_le_mul_of_nonneg_left u1 hCm0, mul_le_mul_of_nonneg_left hH1 hCm0]
  calc ∫ Y, |cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) Y y| ∂P
      ≤ _ := hbd
    _ = _ := hsumint
    _ ≤ β * Real.sqrt (2 * Cv) * u + 3 * Cm * u + 3 * β * u + Ct * u := by linarith
    _ ≤ (βp * Real.sqrt (2 * Cv) + 3 * Cm + 3 * βp + Ct) * u := by
        have h1 := hβI.2
        nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.sqrt_nonneg (2 * Cv)) hu0),
          mul_le_mul_of_nonneg_right h1 hu0]

set_option maxHeartbeats 1600000 in
/-- Uniform `psi_bound`. -/
theorem psi_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      |∫ X, Real.exp (-cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) X y) /
          (∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') -
            cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) X y') ∂(withDensityReal ρ))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) - 1| ≤
        C * Real.sqrt (deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cg, hCg0, hCgU⟩ := conv_gPlus_unif hd hs0 hsd hc Λ
  obtain ⟨C1, hC10, hC1U⟩ := field_L1_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  have hβp : 0 ≤ βp := hβm.le.trans hββ
  refine ⟨Real.exp (4 * (βp * Cg)) * (2 * C1 + βp * Cg), by positivity,
    fun β hβI ρ hρ hΛ N hN x t ht y => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hCg := hCgU ρ hρ hΛ
  have hC1 := hC1U β hβI ρ hρ hΛ
  have hCle : Real.exp (4 * (β * Cg)) * (2 * C1 + β * Cg) ≤
      Real.exp (4 * (βp * Cg)) * (2 * C1 + βp * Cg) := by
    have h1 : β * Cg ≤ βp * Cg := mul_le_mul_of_nonneg_right hβI.2 hCg0
    exact mul_le_mul (Real.exp_le_exp.2 (by linarith)) (by linarith) (by positivity)
      (Real.exp_pos _).le
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hCle (Real.sqrt_nonneg _))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  obtain ⟨u1, -⟩ := small_facts hd hcrit hβ hρ hc hs0 hN
  have hC1' := hC1 N hN x t ht y
  set u : ℝ := Real.sqrt (deltaN d s N) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hM0 : 0 ≤ β * Cg := by positivity
  set M : ℝ := β * Cg with hM
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  set V : Config d (N - 1) → Torus d → ℝ := fun X y' =>
    cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) X y' with hV
  have hgm := measurable_gPlus hd hs0 hsd c
  have hVj : Measurable fun q : Config d (N - 1) × Torus d => V q.1 q.2 :=
    measurable_field_joint' hd hcrit hβ hρ hc N ⟨0, hn⟩
  have hVs : ∀ y', Measurable fun X : Config d (N - 1) => V X y' := fun y' =>
    measurable_field_slice_X hd hcrit hβ hρ hc N ⟨0, hn⟩ y'
  have hVv : ∀ X, Integrable (fun y' => V X y') (withDensityReal ρ) ∧
      Integrable (fun y' => |V X y'|) (withDensityReal ρ) ∧
      ∫ y', |V X y'| ∂(withDensityReal ρ) ≤ 2 * M :=
    fun X => v_integral hd hcrit hβ hρ hc hCg hN X ⟨0, hn⟩
  have hZb := fun X : Config d (N - 1) => Z_bounds hd hcrit hβ hρ hc hCg hN x ht X ⟨0, hn⟩
    (fun y' => -(t * (β / N)) * gPlus d s c (x - y') - V X y') (fun y' => rfl)
  -- the normaliser
  obtain ⟨Z, hZdef⟩ : ∃ Z : Config d (N - 1) → ℝ, ∀ X, Z X =
      ∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') - V X y') ∂(withDensityReal ρ) :=
    ⟨_, fun _ => rfl⟩
  have hZlo : ∀ X, Real.exp (-(3 * M)) ≤ Z X := fun X => by rw [hZdef]; exact (hZb X).2.2.2.2.1
  have hZhi : ∀ X, Z X ≤ Real.exp M := fun X => by rw [hZdef]; exact (hZb X).2.2.2.2.2
  have hZpos : ∀ X, 0 < Z X := fun X => (Real.exp_pos _).trans_le (hZlo X)
  have hAm : Measurable fun q : Config d (N - 1) × Torus d =>
      -(t * (β / N)) * gPlus d s c (x - q.2) - V q.1 q.2 :=
    ((hgm.comp (measurable_const.sub measurable_snd)).const_mul _).sub hVj
  have hZm : Measurable Z := by
    have h1 : StronglyMeasurable fun q : Config d (N - 1) × Torus d =>
        Real.exp (-(t * (β / N)) * gPlus d s c (x - q.2) - V q.1 q.2) :=
      (Real.measurable_exp.comp hAm).stronglyMeasurable
    have h2 := h1.integral_prod_right' (ν := withDensityReal ρ)
    have : Z = fun X => ∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') - V X y')
        ∂(withDensityReal ρ) := funext hZdef
    rw [this]; exact h2.measurable
  -- the integrand
  obtain ⟨g, hgdef⟩ : ∃ g : Config d (N - 1) → ℝ, ∀ X, g X = Real.exp (-V X y) / Z X :=
    ⟨_, fun _ => rfl⟩
  have hgm' : Measurable g := by
    have : g = fun X => Real.exp (-V X y) / Z X := funext hgdef
    rw [this]; exact (Real.measurable_exp.comp (hVs y).neg).div hZm
  have hnegV : ∀ X, -V X y ≤ M := fun X => neg_field_le hd hcrit hβ hρ hc hCg hN ⟨0, hn⟩ X y
  have hexpV : ∀ X, Real.exp (-V X y) ≤ Real.exp M := fun X => Real.exp_le_exp.2 (hnegV X)
  have hg0 : ∀ X, 0 ≤ g X := fun X => by
    rw [hgdef]; exact div_nonneg (Real.exp_pos _).le (hZpos X).le
  have hgb : ∀ X, g X ≤ Real.exp (4 * M) := fun X => by
    rw [hgdef, div_le_iff₀ (hZpos X)]
    calc Real.exp (-V X y) ≤ Real.exp M := hexpV X
      _ = Real.exp (4 * M) * Real.exp (-(3 * M)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (4 * M) * Z X := mul_le_mul_of_nonneg_left (hZlo X) (Real.exp_pos _).le
  have hgi : Integrable g P :=
    Integrable.of_bound (C := Real.exp (4 * M)) hgm'.aestronglyMeasurable
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 X)]; exact hgb X)
  have hψ : (∫ X, Real.exp (-cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) X y) /
          (∫ y', Real.exp (-(t * (β / N)) * gPlus d s c (x - y') -
            cavityField d s c β ρ N (⟨0, hn⟩ : Fin (N - 1)) X y') ∂(withDensityReal ρ)) ∂P) =
      ∫ X, g X ∂P := by
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    rw [hgdef, hZdef]
  rw [hψ]
  have hint1 : ∫ X, g X ∂P - 1 = ∫ X, (g X - 1) ∂P := by
    rw [integral_sub hgi (integrable_const _)]; simp
  rw [hint1]
  refine (abs_integral_le_integral_abs).trans ?_
  obtain ⟨W, hWdef⟩ : ∃ W : Config d (N - 1) → ℝ, ∀ X, W X = ∫ y', |V X y'| ∂(withDensityReal ρ) :=
    ⟨_, fun _ => rfl⟩
  have hW0 : ∀ X, 0 ≤ W X := fun X => by rw [hWdef]; exact integral_nonneg fun _ => abs_nonneg _
  have hW2 : ∀ X, W X ≤ 2 * M := fun X => by rw [hWdef]; exact (hVv X).2.2
  have hZ1 : ∀ X, |Z X - 1| ≤ Real.exp M * ((β / N) * Cg + W X) := by
    intro X
    obtain ⟨a, ha⟩ : ∃ a : Torus d → ℝ, ∀ y', a y' =
        -(t * (β / N)) * gPlus d s c (x - y') - V X y' := ⟨_, fun _ => rfl⟩
    obtain ⟨hup, hai, haia, -, -, -⟩ := Z_bounds hd hcrit hβ hρ hc hCg hN x ht X ⟨0, hn⟩ a ha
    have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
    have hexpi : Integrable (fun y' => Real.exp (a y')) (withDensityReal ρ) :=
      Integrable.mono' (integrable_const (Real.exp M))
        (Real.measurable_exp.comp_aemeasurable hai.aemeasurable).aestronglyMeasurable
        (Eventually.of_forall fun y' => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (hup y'))
    have e1 : Z X - 1 = ∫ y', (Real.exp (a y') - 1) ∂(withDensityReal ρ) := by
      have : Z X = ∫ y', Real.exp (a y') ∂(withDensityReal ρ) := by
        rw [hZdef]; exact integral_congr_ae (Eventually.of_forall fun y' => by
          show Real.exp (-(t * (β / N)) * gPlus d s c (x - y') - V X y') = Real.exp (a y')
          rw [ha])
      rw [this, integral_sub hexpi (integrable_const _)]; simp
    have htl : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
    have hle : ∀ y', |Real.exp (a y') - 1| ≤
        Real.exp M * ((t * (β / N)) * gPlus d s c (x - y') + |V X y'|) := by
      intro y'
      refine (abs_exp_sub_one_le hM0 (hup y')).trans
        (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      rw [ha]
      have h1 : 0 ≤ (t * (β / N)) * gPlus d s c (x - y') := mul_nonneg htl (hc _)
      calc _ ≤ |-(t * (β / N)) * gPlus d s c (x - y')| + |V X y'| := abs_sub _ _
        _ = _ := by rw [neg_mul, abs_neg, abs_of_nonneg h1]
    have hrint : Integrable (fun y' => Real.exp M * ((t * (β / N)) * gPlus d s c (x - y') +
        |V X y'|)) (withDensityReal ρ) :=
      ((hGi.const_mul _).add (hVv X).2.1).const_mul _
    rw [e1]
    refine (abs_integral_le_integral_abs).trans
      ((integral_mono_of_nonneg (Eventually.of_forall fun y' => abs_nonneg _) hrint
        (Eventually.of_forall hle)).trans ?_)
    rw [integral_const_mul, integral_add (hGi.const_mul _) (hVv X).2.1, integral_const_mul,
      ← hWdef X]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have e2 : (t * (β / N)) * ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) ≤ (β / N) * Cg := by
      have : t * (β / N) ≤ β / N := by nlinarith [ht.1, ht.2]
      calc _ ≤ (β / N) * ∫ y', gPlus d s c (x - y') ∂(withDensityReal ρ) :=
            mul_le_mul_of_nonneg_right this (integral_nonneg fun y' => hc _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hCg x).2 hlam
    linarith
  have hpt : ∀ X, |g X - 1| ≤
      Real.exp (3 * M) * (Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X)) := by
    intro X
    have hz := hZpos X
    have e1 : g X - 1 = (Real.exp (-V X y) - Z X) / Z X := by
      rw [hgdef]; field_simp
    rw [e1, abs_div, abs_of_pos hz, div_le_iff₀ hz]
    have h1 : |Real.exp (-V X y) - 1| ≤ Real.exp M * |V X y| := by
      have := abs_exp_sub_one_le hM0 (hnegV X)
      rwa [abs_neg] at this
    have h2 := hZ1 X
    have h3 : |Real.exp (-V X y) - Z X| ≤ |Real.exp (-V X y) - 1| + |Z X - 1| := by
      have := abs_sub_le (Real.exp (-V X y)) 1 (Z X)
      rwa [abs_sub_comm 1 (Z X)] at this
    have hK : 0 ≤ Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X) := by
      have := hW0 X
      positivity
    calc |Real.exp (-V X y) - Z X| ≤ Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X) := by
          linarith
      _ = Real.exp (3 * M) * (Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X)) *
            Real.exp (-(3 * M)) := by
          rw [mul_comm (Real.exp (3 * M)), mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hZlo X) (by positivity)
  have hWm : Measurable W := by
    have h1 : StronglyMeasurable fun q : Config d (N - 1) × Torus d => |V q.1 q.2| :=
      hVj.abs.stronglyMeasurable
    have h2 := h1.integral_prod_right' (ν := withDensityReal ρ)
    have : W = fun X => ∫ y', |V X y'| ∂(withDensityReal ρ) := funext hWdef
    rw [this]; exact h2.measurable
  have hWint : Integrable W P :=
    Integrable.of_bound (C := 2 * M) hWm.aestronglyMeasurable (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 X)]; exact hW2 X)
  have hFm : Measurable fun q : Config d (N - 1) × Torus d => |V q.1 q.2| := hVj.abs
  have hFi : Integrable (fun q : Config d (N - 1) × Torus d => |V q.1 q.2|)
      (P.prod (withDensityReal ρ)) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2
      ⟨Eventually.of_forall fun X => (hVv X).2.1, ?_⟩
    have : (fun X => ∫ y', ‖|V X y'|‖ ∂(withDensityReal ρ)) = W := by
      funext X; rw [hWdef]; simp only [Real.norm_eq_abs, abs_abs]
    rw [this]; exact hWint
  have hWP : ∫ X, W X ∂P ≤ C1 * u := by
    have e1 : ∫ X, W X ∂P = ∫ q, |V q.1 q.2| ∂(P.prod (withDensityReal ρ)) := by
      rw [integral_prod _ hFi]
      refine integral_congr_ae (Eventually.of_forall fun X => ?_)
      show W X = ∫ y', |V X y'| ∂(withDensityReal ρ)
      exact hWdef X
    have e2 : ∫ q, |V q.1 q.2| ∂(P.prod (withDensityReal ρ)) =
        ∫ y', ∫ X, |V X y'| ∂P ∂(withDensityReal ρ) := integral_prod_symm _ hFi
    rw [e1, e2]
    calc _ ≤ ∫ _y', C1 * u ∂(withDensityReal ρ) :=
          integral_mono hFi.integral_prod_right (integrable_const _)
            fun y' => (hC1 N hN x t ht y').2
      _ = C1 * u := by simp
  have i1 : Integrable (fun X => Real.exp M * |V X y|) P := hC1'.1.const_mul _
  have i2 : Integrable (fun X => Real.exp M * ((β / N) * Cg + W X)) P :=
    ((integrable_const _).add hWint).const_mul _
  have hBint : Integrable (fun X => Real.exp (3 * M) *
      (Real.exp M * |V X y| + Real.exp M * ((β / N) * Cg + W X))) P := (i1.add i2).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun X => abs_nonneg _) hBint
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_add (integrable_const _) hWint]
  simp only [integral_const, probReal_univ, one_smul]
  have hI1 : ∫ X, |V X y| ∂P ≤ C1 * u := hC1'.2
  have hlamC : (β / N) * Cg ≤ M * u := by
    calc (β / N) * Cg = (β * Cg) * (1 / (N : ℝ)) := by ring
      _ ≤ (β * Cg) * u := mul_le_mul_of_nonneg_left u1 hM0
  have hsum : ∫ X, |V X y| ∂P + ((β / N) * Cg + ∫ X, W X ∂P) ≤ (2 * C1 + β * Cg) * u := by
    have : M = β * Cg := rfl
    nlinarith
  have e3 : Real.exp (4 * M) = Real.exp (3 * M) * Real.exp M := by rw [← Real.exp_add]; congr 1; ring
  rw [e3]
  calc Real.exp (3 * M) * (Real.exp M * ∫ X, |V X y| ∂P + Real.exp M * ((β / N) * Cg + ∫ X, W X ∂P))
      = Real.exp (3 * M) * Real.exp M * (∫ X, |V X y| ∂P + ((β / N) * Cg + ∫ X, W X ∂P)) := by ring
    _ ≤ Real.exp (3 * M) * Real.exp M * ((2 * C1 + β * Cg) * u) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Uniform `pole_prefactor`. -/
theorem pole_prefactor_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
              Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
            C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C, hC0, hCU⟩ := psi_bound_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  refine ⟨C, hC0, fun β hβI ρ hρ hΛ N hN x t ht => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hC := hCU β hβI ρ hρ hΛ
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  obtain ⟨hac, hae⟩ := critPole_formula hd hs0 hsd β hβ hρ hc m x ht.1
  refine ⟨hac, ?_⟩
  filter_upwards [hae] with y hy
  rw [hy]
  have hψ := hC (m + 2) hN x t ht y
  rw [critPole_eq_poleLaw hd hs0 hsd β hβ hρ hN x t]
  have key : ∀ (E ψ B : ℝ), 0 < E → |ψ - 1| ≤ B → |E * ψ - E| ≤ B * E := fun E ψ B hE h => by
    rw [show E * ψ - E = E * (ψ - 1) by ring, abs_mul, abs_of_pos hE, mul_comm]
    exact mul_le_mul_of_nonneg_right h hE.le
  exact key _ _ _ (Real.exp_pos _) hψ

end HRS.ME.Unif

end
