import HRS.ME.UnifP5D

/-!
# Uniform Lemma 4.6 (cavity response), part E (packet P5)

Uniform versions of `var_trunc`, `conv_abs_bound`, `mean_trunc` and `tail_bound`
(`HRS/Equilibrium/CavityField.lean`): the three estimates (variance, mean, tail) of the truncated cavity
field, with constants chosen after `d, s, βm, βp, Λ, c` and before `β ∈ [βm, βp]` and the smooth density `ρ ≤ Λ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

/-- Uniform `var_trunc`. -/
theorem var_trunc_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      ∀ H : ℝ, 2 ≤ H →
      Var[fracF (n := N - 1) (fun z => gTrunc d s c H (y - z));
        poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t] ≤
        Cv * Real.log H / ((N - 1 : ℕ) : ℝ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C1, hC1, hvarU⟩ := pole_variance_clause_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨Cc, hCint, -, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  refine ⟨C1 * Real.exp (βp * max B 0) * |Cc|, by positivity,
    fun β hβI ρ hρ hΛ N hN x t ht y H hH => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hβle : β ≤ βp := hβI.2
  have hμ := isProbabilityMeasure_mu hρ
  have hvar := hvarU β hβI ρ hρ hΛ
  have h1 := (hCint ρ hρ hΛ).1
  have hgm := measurable_gPlus hd hs0 hsd c
  have hfm : Measurable fun z => gTrunc d s c H (y - z) :=
    (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hfb : ∀ z, |gTrunc d s c H (y - z)| ≤ H := fun z => by
    obtain ⟨a, b, -⟩ := gTrunc_bounds hd hcrit hβ hρ hc H (by linarith) (y - z)
    rwa [abs_of_nonneg a]
  have hv := var_fracF_le hd hs0 hsd hβ hρ hC1 hvar (le_max_right B 0)
    (fun z => (neg_le_neg (le_max_left B 0)).trans (hB z)) hN x ht hfm hfb
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hI : ∫ z, gTrunc d s c H (y - z) ^ 2 ∂(withDensityReal ρ) ≤ |Cc| * Real.log H := by
    have := (integ_of_lint (μ := withDensityReal ρ) (f := fun z => gTrunc d s c H (y - z) ^ 2)
      (hfm.pow_const 2) (fun z => sq_nonneg _) (by positivity)
      ((h1 H hH y).1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) hlog)))).2
    exact this
  refine hv.trans ?_
  have hE := Real.exp_pos (β * max B 0)
  calc C1 * Real.exp (β * max B 0) * (∫ z, gTrunc d s c H (y - z) ^ 2 ∂(withDensityReal ρ)) / ((N - 1 : ℕ) : ℝ)
      ≤ C1 * Real.exp (β * max B 0) * (|Cc| * Real.log H) / ((N - 1 : ℕ) : ℝ) := by
        gcongr
    _ = C1 * Real.exp (β * max B 0) * |Cc| * Real.log H / ((N - 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := by gcongr

/-- Uniform `conv_abs_bound` (does not involve `β`). -/
theorem conv_abs_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) (M : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ h : Torus d → ℝ, Measurable h → (∀ y, |h y| ≤ M) →
      ∀ e : ℝ, 0 ≤ e → ∫ y, |h y| ∂(withDensityReal ρ) ≤ e → ∀ x : Torus d,
        ∫ y, gPlus d s c (x - y) * |h y| ∂(withDensityReal ρ) ≤ C' * Real.sqrt e := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨CM, hCM0, hCMU⟩ := gplus_abs_conv_small_unif hd hcrit hc Λ hΛ1 M
  obtain ⟨Cg, hCg0, hCgU⟩ := conv_gPlus_unif hd hs0 hsd hc Λ
  refine ⟨max CM (|M| * Cg), by positivity, fun ρ hρ hΛ h hm hb e he hl x => ?_⟩
  have hβ : (0 : ℝ) < 1 := one_pos
  have hμ := isProbabilityMeasure_mu hρ
  have hCM := hCMU ρ hρ hΛ
  have hCg := hCgU ρ hρ hΛ
  by_cases he1 : e ≤ 1
  · exact (hCM h hm hb e he he1 hl x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · push_neg at he1
    have hs1 : 1 ≤ Real.sqrt e := by rw [Real.one_le_sqrt]; exact he1.le
    have hgi := gPlus_int hd hcrit hβ hρ hc hs0 hsd x
    calc ∫ y, gPlus d s c (x - y) * |h y| ∂(withDensityReal ρ)
        ≤ ∫ y, |M| * gPlus d s c (x - y) ∂(withDensityReal ρ) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (hc _) (abs_nonneg _))
            (hgi.const_mul _) (Eventually.of_forall fun y => ?_)
          have := hb y
          have h2 := hc (x - y)
          calc gPlus d s c (x - y) * |h y| ≤ gPlus d s c (x - y) * |M| :=
                mul_le_mul_of_nonneg_left (this.trans (le_abs_self _)) h2
            _ = _ := by ring
      _ = |M| * convMeasure (gPlus d s c) (withDensityReal ρ) x := by
          rw [integral_const_mul]; rfl
      _ ≤ |M| * Cg := mul_le_mul_of_nonneg_left (hCg x).2 (abs_nonneg _)
      _ ≤ max CM (|M| * Cg) * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max CM (|M| * Cg) * Real.sqrt e :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)

set_option maxHeartbeats 1600000 in
/-- Uniform `mean_trunc`. -/
theorem mean_trunc_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      ∀ H : ℝ, 2 ≤ H →
      |(β / N) * ((N - 1 : ℕ) : ℝ) * ∫ z, gTrunc d s c H (y - z)
          ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
        β * convMeasure (gPlus d s c) (withDensityReal ρ) y| ≤
      Cm * (Real.sqrt (deltaN d s N) + 1 / (N : ℝ) + 1 / H) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Ce, hCe0, hCeU⟩ := pole_marginal_l1_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨M1, hM1, hMargU⟩ := pole_marg_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Cg, hCg0, hCgU⟩ := conv_gPlus_unif hd hs0 hsd hc Λ
  obtain ⟨Cc, hCint, -, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  obtain ⟨C', hC'0, hC'U⟩ := conv_abs_bound_unif hd hcrit hc Λ hΛ1 (M1 + 1)
  have hβp : 0 ≤ βp := hβm.le.trans hββ
  refine ⟨βp * C' * Real.sqrt Ce + βp * Cg + βp * |Cc|, by positivity,
    fun β hβI ρ hρ hΛ N hN x t ht y H hH => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hH0 : 0 < H := by linarith
  have hN0' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hCle : β * C' * Real.sqrt Ce + β * Cg + β * |Cc| ≤
      βp * C' * Real.sqrt Ce + βp * Cg + βp * |Cc| := by
    have h1 := hβI.2
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hC'0 (Real.sqrt_nonneg Ce)),
      mul_le_mul_of_nonneg_right h1 hCg0, mul_le_mul_of_nonneg_right h1 (abs_nonneg Cc)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hCle (by positivity))
  have hμ := isProbabilityMeasure_mu hρ
  have hCe := hCeU β hβI ρ hρ hΛ
  have hMarg := hMargU β hβI ρ hρ hΛ
  have hCg := hCgU ρ hρ hΛ
  have h1 := (hCint ρ hρ hΛ).1
  have hC' := hC'U ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  haveI hνp := isProb_firstMarginal hn (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
  obtain ⟨hac, hmap⟩ := hMarg N hN x t ht
  have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn⟩) := by
    unfold firstMarginal; rw [dif_pos hn]
  have hbd : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
      ENNReal.ofReal M1 • withDensityReal ρ := by rw [hfm]; exact hmap ⟨0, hn⟩
  obtain ⟨hqi, hq1, hqeq⟩ := dens_facts hac
  have hqM : ∀ᵐ z ∂(withDensityReal ρ),
      ((firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) z).toReal ≤ M1 := by
    filter_upwards [rnDeriv_ae_le hac hbd] with z hz
    exact ENNReal.toReal_le_of_le_ofReal hM1.le hz
  have hδ0 : 0 ≤ deltaN d s N := (inv_nonneg.2 hN0.le).trans (inv_le_deltaN (d := d) hs0 N (by omega))
  set q : Torus d → ℝ := fun z =>
    ((firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
      (withDensityReal ρ) z).toReal with hq
  have hqm : Measurable q := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hq0 : ∀ z, 0 ≤ q z := fun z => ENNReal.toReal_nonneg
  have hgm := measurable_gPlus hd hs0 hsd c
  have hH0 : 0 ≤ H := by linarith
  set f : Torus d → ℝ := fun z => gTrunc d s c H (y - z) with hf
  have hfm' : Measurable f := (hgm.comp (measurable_const.sub measurable_id)).min measurable_const
  have hf0 : ∀ z, 0 ≤ f z := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).1
  have hfH : ∀ z, f z ≤ H := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).2.1
  have hfG : ∀ z, f z ≤ gPlus d s c (y - z) := fun z => (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).2.2
  have hfi : Integrable f (withDensityReal ρ) :=
    Integrable.of_bound (C := H) hfm'.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hfH z)
  have hGi := gPlus_int hd hcrit hβ hρ hc hs0 hsd y
  have hGm : Measurable fun z => gPlus d s c (y - z) := hgm.comp (measurable_const.sub measurable_id)
  -- the marginal expectation
  have hint : ∫ z, f z ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) =
      ∫ z, q z * f z ∂(withDensityReal ρ) := by
    calc _ = ∫ z, f z ∂((withDensityReal ρ).withDensity fun z => ENNReal.ofReal (q z)) := by
          rw [← hqeq]
      _ = _ := integral_withDensity_real hqm hq0 f
  have hqfi : Integrable (fun z => q z * f z) (withDensityReal ρ) :=
    Integrable.mono' (hqi.mul_const H) (hqm.mul hfm').aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 z) (hf0 z))]
        exact mul_le_mul_of_nonneg_left (hfH z) (hq0 z) |>.trans (by rw [mul_comm]))
  -- the truncation tail
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - f z with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z => sub_nonneg.2 (hfG z)
  have hrm : Measurable r := hGm.sub hfm'
  have hH0' : 0 < H := by linarith
  have hrI : ∫ z, r z ∂(withDensityReal ρ) ≤ |Cc| / H := by
    refine (integ_of_lint hrm hr0 (by positivity) ((h1 H hH y).2.trans (ENNReal.ofReal_le_ofReal ?_))).2
    exact div_le_div_of_nonneg_right (le_abs_self _) hH0'.le
  have hrInt : ∫ z, r z ∂(withDensityReal ρ) =
      convMeasure (gPlus d s c) (withDensityReal ρ) y - ∫ z, f z ∂(withDensityReal ρ) := by
    show ∫ z, (gPlus d s c (y - z) - f z) ∂(withDensityReal ρ) = _
    rw [integral_sub hGi hfi]; rfl
  have hr0' : 0 ≤ ∫ z, r z ∂(withDensityReal ρ) := integral_nonneg hr0
  -- the fluctuation part
  have hint1 : Integrable (fun z => (q z - 1) * f z) (withDensityReal ρ) := by
    refine (hqfi.sub hfi).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  have hsplit : ∫ z, q z * f z ∂(withDensityReal ρ) =
      ∫ z, (q z - 1) * f z ∂(withDensityReal ρ) + ∫ z, f z ∂(withDensityReal ρ) := by
    rw [← integral_add hint1 hfi]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
  set hh : Torus d → ℝ := fun z => max (-1) (min (q z - 1) M1) with hhdef
  have hhm : Measurable hh := measurable_const.max ((hqm.sub measurable_const).min measurable_const)
  have hhb : ∀ z, |hh z| ≤ M1 + 1 := fun z => by
    rw [abs_le]
    refine ⟨?_, max_le (by linarith) ((min_le_right _ _).trans (by linarith))⟩
    exact (by linarith : -(M1 + 1) ≤ -1).trans (le_max_left _ _)
  have hhq : ∀ᵐ z ∂(withDensityReal ρ), hh z = q z - 1 := by
    filter_upwards [hqM] with z hz
    simp only [hhdef]
    rw [min_eq_left (by linarith), max_eq_right (by linarith [hq0 z])]
  have hab : ∫ z, |hh z| ∂(withDensityReal ρ) ≤ Ce * deltaN d s N := by
    have := hCe N hN x t ht
    refine le_trans (le_of_eq ?_) this
    exact integral_congr_ae (hhq.mono fun z hz => by show |hh z| = |q z - 1|; rw [hz])
  have hCC := hC' hh hhm hhb (Ce * deltaN d s N) (by positivity) hab y
  have hGhh : Integrable (fun z => gPlus d s c (y - z) * |hh z|) (withDensityReal ρ) :=
    Integrable.mono' (hGi.mul_const (M1 + 1)) (hGm.mul hhm.abs).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        have h0 : 0 ≤ gPlus d s c (y - z) * |hh z| := mul_nonneg (hc _) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_left (hhb z) (hc _))
  have ha : |∫ z, (q z - 1) * f z ∂(withDensityReal ρ)| ≤ C' * Real.sqrt (Ce * deltaN d s N) := by
    have e1 : ∫ z, (q z - 1) * f z ∂(withDensityReal ρ) = ∫ z, hh z * f z ∂(withDensityReal ρ) :=
      integral_congr_ae (hhq.mono fun z hz => by show (q z - 1) * f z = hh z * f z; rw [hz])
    rw [e1]
    refine (abs_integral_le_integral_abs).trans ((integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
      hGhh (Eventually.of_forall fun z => ?_)).trans hCC)
    show |hh z * f z| ≤ gPlus d s c (y - z) * |hh z|
    rw [abs_mul, abs_of_nonneg (hf0 z), mul_comm]
    exact mul_le_mul_of_nonneg_right (hfG z) (abs_nonneg _)
  rw [Real.sqrt_mul hCe0] at ha
  -- assemble
  have hGI : 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y := (hCg y).1
  have hGC : convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg := (hCg y).2
  have hn' : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hint, hsplit]
  have hfeq : ∫ z, f z ∂(withDensityReal ρ) =
      convMeasure (gPlus d s c) (withDensityReal ρ) y - ∫ z, r z ∂(withDensityReal ρ) := by
    rw [hrInt]; ring
  rw [hfeq]
  have hkey := alg_eq (β / N) β ((N - 1 : ℕ) : ℝ) (N : ℝ) (∫ z, (q z - 1) * f z ∂(withDensityReal ρ))
    (∫ z, r z ∂(withDensityReal ρ)) (convMeasure (gPlus d s c) (withDensityReal ρ) y)
    (by field_simp) (by rw [hn']; ring)
  rw [hkey]
  refine (alg_bound _ _ _ _ _ hlam (by positivity) hr0' hGI).trans ?_
  have hLn : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [hn', div_mul_eq_mul_div, div_le_iff₀ hN0]; nlinarith
  have hLn0 : 0 ≤ β / N * ((N - 1 : ℕ) : ℝ) := by positivity
  have p1 : β / N * ((N - 1 : ℕ) : ℝ) * |∫ z, (q z - 1) * f z ∂(withDensityReal ρ)| ≤
      β * (C' * (Real.sqrt Ce * Real.sqrt (deltaN d s N))) :=
    mul_le_mul hLn ha (abs_nonneg _) hβ.le
  have p2 : β / N * convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ β * Cg * (1 / (N : ℝ)) := by
    calc _ ≤ β / N * Cg := mul_le_mul_of_nonneg_left hGC hlam
      _ = _ := by ring
  have p3 : β / N * ((N - 1 : ℕ) : ℝ) * ∫ z, r z ∂(withDensityReal ρ) ≤ β * |Cc| * (1 / H) :=
    calc _ ≤ β * (|Cc| / H) := mul_le_mul hLn hrI hr0' hβ.le
      _ = _ := by ring
  have hX := Real.sqrt_nonneg (deltaN d s N)
  have hY : 0 ≤ 1 / (N : ℝ) := by positivity
  have hZ : 0 ≤ 1 / H := by positivity
  have hq1 : 0 ≤ β * C' * Real.sqrt Ce := by positivity
  have hq2 : 0 ≤ β * Cg := by positivity
  have hq3 : 0 ≤ β * |Cc| := by positivity
  nlinarith [mul_nonneg hq1 hY, mul_nonneg hq1 hZ, mul_nonneg hq2 hX, mul_nonneg hq2 hZ,
    mul_nonneg hq3 hX, mul_nonneg hq3 hY]

/-- Uniform `tail_bound`. -/
theorem tail_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : Torus d,
      ∀ H : ℝ, 2 ≤ H →
      Integrable (fun Y : Config d (N - 1) => (β / N) * ∑ j, (gPlus d s c (y - Y j) - gTrunc d s c H (y - Y j)))
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
        ∫ Y, (β / N) * ∑ j, (gPlus d s c (y - Y j) - gTrunc d s c H (y - Y j))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤ Ct / H := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨M1, hM1, hMargU⟩ := pole_marg_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Cc, hCint, -, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  have hβp : 0 ≤ βp := hβm.le.trans hββ
  refine ⟨βp * M1 * |Cc|, by positivity, fun β hβI ρ hρ hΛ N hN x t ht y H hH => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hMarg := hMargU β hβI ρ hρ hΛ
  have h1 := (hCint ρ hρ hΛ).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  obtain ⟨-, hmap⟩ := hMarg N hN x t ht
  have hgm := measurable_gPlus hd hs0 hsd c
  have hH0 : 0 ≤ H := by linarith
  have hH0' : 0 < H := by linarith
  set r : Torus d → ℝ := fun z => gPlus d s c (y - z) - gTrunc d s c H (y - z) with hr
  have hr0 : ∀ z, 0 ≤ r z := fun z =>
    sub_nonneg.2 (gTrunc_bounds hd hcrit hβ hρ hc H hH0 (y - z)).2.2
  have hrm : Measurable r :=
    (hgm.comp (measurable_const.sub measurable_id)).sub
      ((hgm.comp (measurable_const.sub measurable_id)).min measurable_const)
  have hRm : Measurable fun Y : Config d (N - 1) => (β / N) * ∑ j, r (Y j) :=
    (Finset.measurable_sum _ fun j _ => hrm.comp (measurable_pi_apply j)).const_mul _
  have hR0 : ∀ Y : Config d (N - 1), 0 ≤ (β / N) * ∑ j, r (Y j) := fun Y =>
    mul_nonneg hlam (Finset.sum_nonneg fun j _ => hr0 _)
  have hrint : ∫⁻ z, ENNReal.ofReal (r z) ∂(withDensityReal ρ) ≤ ENNReal.ofReal (|Cc| / H) :=
    (h1 H hH y).2.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) hH0'.le))
  have hlint : ∫⁻ Y, ENNReal.ofReal ((β / N) * ∑ j, r (Y j))
      ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
      ENNReal.ofReal (βp * M1 * |Cc| / H) := by
    have e1 : ∀ Y : Config d (N - 1), ENNReal.ofReal ((β / N) * ∑ j, r (Y j)) =
        ∑ j, ENNReal.ofReal ((β / N) * r (Y j)) := fun Y => by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg hlam (hr0 _)]
    have hφm : Measurable fun z => ENNReal.ofReal ((β / N) * r z) :=
      ENNReal.measurable_ofReal.comp (hrm.const_mul _)
    have e2 : ∀ j : Fin (N - 1), ∫⁻ Y, ENNReal.ofReal ((β / N) * r (Y j))
        ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
        ENNReal.ofReal M1 * (ENNReal.ofReal (β / N) * ENNReal.ofReal (|Cc| / H)) := fun j => by
      rw [← lintegral_map hφm (measurable_pi_apply j)]
      calc _ ≤ ∫⁻ z, ENNReal.ofReal ((β / N) * r z) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
            lintegral_mono' (hmap j) le_rfl
        _ = ENNReal.ofReal M1 * ∫⁻ z, ENNReal.ofReal ((β / N) * r z) ∂(withDensityReal ρ) :=
            lintegral_smul_measure _ _
        _ ≤ _ := by
            refine mul_le_mul' le_rfl ?_
            simp_rw [ENNReal.ofReal_mul hlam]
            rw [lintegral_const_mul _ (show Measurable fun z => ENNReal.ofReal (r z) from ENNReal.measurable_ofReal.comp hrm)]
            exact mul_le_mul' le_rfl hrint
    calc _ = ∫⁻ Y, ∑ j, ENNReal.ofReal ((β / N) * r (Y j))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) :=
          lintegral_congr e1
      _ = ∑ j, ∫⁻ Y, ENNReal.ofReal ((β / N) * r (Y j))
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) :=
          lintegral_finset_sum _ fun j _ => hφm.comp (measurable_pi_apply j)
      _ ≤ ∑ _j : Fin (N - 1), ENNReal.ofReal M1 * (ENNReal.ofReal (β / N) * ENNReal.ofReal (|Cc| / H)) :=
          Finset.sum_le_sum fun j _ => e2 j
      _ = ENNReal.ofReal (((N - 1 : ℕ) : ℝ) * (M1 * ((β / N) * (|Cc| / H)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_mul hM1.le, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hLn : ((N - 1 : ℕ) : ℝ) * (β / N) ≤ β := by
            have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
            rw [this, mul_div_assoc', div_le_iff₀ hN0]; nlinarith
          have hq : 0 ≤ M1 * (|Cc| / H) := by positivity
          calc ((N - 1 : ℕ) : ℝ) * (M1 * ((β / N) * (|Cc| / H)))
              = (((N - 1 : ℕ) : ℝ) * (β / N)) * (M1 * (|Cc| / H)) := by ring
            _ ≤ β * (M1 * (|Cc| / H)) := mul_le_mul_of_nonneg_right hLn hq
            _ ≤ βp * (M1 * (|Cc| / H)) := mul_le_mul_of_nonneg_right hβI.2 hq
            _ = _ := by ring
  exact integ_of_lint hRm hR0 (by positivity) hlint

end HRS.ME.Unif

end
