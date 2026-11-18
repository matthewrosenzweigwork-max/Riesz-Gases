import HRS.Main.EqMargU1

/-!
# EQ-MARG-U, part 2: uniform pole-level bounds (cavity marginal, insertion defect, cavity TV)
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace EqMarg

open HRS.External HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

theorem eqmarg_cavity_marginal_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1),
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map (fun Y : Config d (N - 1) => Y i) ≤
        ENNReal.ofReal C • withDensityReal ρ := by
  obtain ⟨B, Cc, hB0, hCc0, hKU⟩ := eqmarg_kerData hd hs0 hsd Λ0
  refine ⟨Real.exp (Kbound (periodicRiesz d s) B Cc βp 1), Real.exp_pos _,
    fun β hβ1 hβ2 ρ hρ hΛ N hN i => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hK := hKU ρ hρ hΛ
  have hKle : Real.exp (Kbound (periodicRiesz d s) B Cc β 1) ≤
      Real.exp (Kbound (periodicRiesz d s) B Cc βp 1) :=
    Real.exp_le_exp.2 (eqmarg_Kbound_mono _ hB0 hCc0 hβ.le hβ2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hlb : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]
    linarith
  haveI hP := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam 0 0 le_rfl
  have h := pole_one_le hK hB0 i hβ.le le_rfl zero_le_one hlam hlb hln 0 (hP := hP)
  rw [poleLaw_zero_eq hd hs0 hsd β hρ _ _ hlam] at h
  refine h.trans ?_
  rw [← withDensity_const]
  refine withDensity_mono (Filter.Eventually.of_forall fun y => ?_)
  simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  exact ENNReal.ofReal_le_ofReal hKle

theorem eqmarg_w_integral_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Cw * ((N : ℝ) * deltaN d s N)) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  obtain ⟨CI, hCI0, hCI⟩ := Ibound hd hs0 hsd βm hβm
  set Λ : ℝ := max Λ0 1 with hΛdef
  have hΛ0 : 0 < Λ := lt_max_of_lt_right one_pos
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Λ * (B ^ 2 * Real.exp (βp * B) + CI), by positivity,
    fun β hβ1 hβ2 ρ hρ hΛρ N hN x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => (hΛρ x).trans (le_max_left _ _)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 < β / N := by positivity
  have hlamle : β / N ≤ β := by
    rw [div_le_iff₀ hN0]; have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  set lam : ℝ := β / N with hlamdef
  have hlamP : lam ≤ βp := hlamle.trans hβ2
  -- joint measurability
  have hF : Measurable fun q : ℝ × Torus d => ‖periodicRiesz d s (x - q.2)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(q.1 * lam) * periodicRiesz d s (x - q.2))) := by
    refine (((hgm.comp (measurable_const.sub measurable_snd)).enorm).pow_const 2).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_fst.mul_const lam).neg.mul (hgm.comp (measurable_const.sub measurable_snd))))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  -- pointwise bound in y
  set Mfun : Torus d → ℝ := fun z => min (rieszPos d s z ^ 2) ((N : ℝ) / β * rieszPos d s z) with hMfun
  have hMmono : ∀ z, Mfun z ≤ min (rieszPos d s z ^ 2) ((N : ℝ) / βm * rieszPos d s z) := by
    intro z
    have h0 : 0 ≤ rieszPos d s z := le_max_right _ _
    refine min_le_min le_rfl ?_
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hN0.le hβm hβ1) h0
  have hpt : ∀ y : Torus d, ∫⁻ t in Ioc (0 : ℝ) 1, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ≤
      ENNReal.ofReal (B ^ 2 * Real.exp (βp * B) + Mfun (x - y)) := by
    intro y
    have hmt : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((measurable_id.mul_const lam).neg.mul_const _))
    rw [lintegral_const_mul _ hmt]
    refine (int_t_bound hlam hB0 _ (hB _)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : B ^ 2 * Real.exp (lam * B) ≤ B ^ 2 * Real.exp (βp * B) := by
      gcongr
    have h2 : min (max (periodicRiesz d s (x - y)) 0 ^ 2) ((1 / lam) * max (periodicRiesz d s (x - y)) 0) =
        Mfun (x - y) := by
      simp only [hMfun, rieszPos, hlamdef, one_div_div]
    rw [h2]; linarith
  calc ∫⁻ y, (∫⁻ t in Ioc (0 : ℝ) 1, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y)))) ∂(withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal (B ^ 2 * Real.exp (βp * B) + Mfun (x - y)) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (B ^ 2 * Real.exp (βp * B) + Mfun z) :=
        KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (B ^ 2 * Real.exp (βp * B) + Mfun z)) x
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal (B ^ 2 * Real.exp (βp * B)) + ENNReal.ofReal (CI * ((N : ℝ) * deltaN d s N))) := by
        gcongr
        have hMn : ∀ z, 0 ≤ Mfun z := fun z => by
          have h0 : 0 ≤ rieszPos d s z := le_max_right _ _
          exact le_min (by positivity) (by positivity)
        calc ∫⁻ z : Torus d, ENNReal.ofReal (B ^ 2 * Real.exp (βp * B) + Mfun z)
            = ∫⁻ z : Torus d, (ENNReal.ofReal (B ^ 2 * Real.exp (βp * B)) + ENNReal.ofReal (Mfun z)) := by
              refine lintegral_congr fun z => ?_
              rw [ENNReal.ofReal_add (by positivity) (hMn z)]
          _ = ENNReal.ofReal (B ^ 2 * Real.exp (βp * B)) + ∫⁻ z : Torus d, ENNReal.ofReal (Mfun z) := by
              have hpm := measurable_rieszPos hd hs0 hsd
              have hmM : Measurable fun z : Torus d => ENNReal.ofReal (Mfun z) :=
                ENNReal.measurable_ofReal.comp ((hpm.pow_const 2).min (measurable_const.mul hpm))
              rw [lintegral_add_right (fun _ : Torus d => ENNReal.ofReal (B ^ 2 * Real.exp (βp * B))) hmM,
                lintegral_const, measure_univ, mul_one]
          _ ≤ _ := by
            gcongr
            exact (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hMmono z)).trans (hCI N hN)
    _ ≤ ENNReal.ofReal (Λ * (B ^ 2 * Real.exp (βp * B) + CI) * ((N : ℝ) * deltaN d s N)) := by
        have h1 := PreparationAux.one_le_N_deltaN (d := d) hs0 N (by omega)
        rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hCI0 (by linarith)),
          ← ENNReal.ofReal_mul hΛ0.le]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : 0 ≤ B ^ 2 * Real.exp (βp * B) := by positivity
        nlinarith [mul_nonneg hΛ0.le (mul_nonneg h2 (sub_nonneg.2 h1))]

theorem eqmarg_insDefect_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      0 ≤ insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ∧
      insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ C * deltaN d s N ∧
      cgf (Xx (periodicRiesz d s) (β / N) x)
          (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) 1 -
        2 * cgf (Xx (periodicRiesz d s) (β / N) x)
          (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) (1 / 2) ≤ C * deltaN d s N := by
  obtain ⟨C₁, hC₁, hvarU⟩ := eqmarg_pole_variance hd hs0 hsd βm βp hβm Λ0
  obtain ⟨Cw, hCw0, hCwU⟩ := eqmarg_w_integral_bound hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨βp ^ 2 * C₁ * Cw, fun β hβ1 hβ2 ρ hρ hΛ N hN x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hvar := hvarU β hβ1 hβ2 ρ hρ hΛ
  have hCw := hCwU β hβ1 hβ2 ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlam : 0 ≤ β / N := by positivity
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam
  set lam : ℝ := β / N with hlamdef
  set n : ℕ := N - 1 with hn
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0def
  have hXm := measurable_Xx hgm (n := n) lam x
  have hb : ∀ Y : Config d n, Xx (periodicRiesz d s) lam x Y ≤ β * B := by
    intro Y
    have h1 := sum_ge_of_ge (periodicRiesz d s) (fun z => hB z) (n := n) x Y
    unfold Xx
    have : lam * (B * n) ≤ β * B := by
      have : lam * (B * n) = (lam * n) * B := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right hln hB0
    nlinarith
  have hXi := integrable_Xx hd hs0 hsd hβ hρ hN x
  -- the dominating function
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (C₁ * (n : ℝ)) *
    ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ)) with hw
  have hwle : ∀ t ∈ Ioc (0 : ℝ) 1,
      ENNReal.ofReal (Var[Xx (periodicRiesz d s) lam x; P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)]) ≤ w t := by
    intro t ht
    rw [← poleLaw_eq_tilted_cavity hd hs0 hsd β hρ n lam hlam x t]
    have h1 := hvar N hN x t ⟨ht.1.le, ht.2⟩ (fun y => periodicRiesz d s (x - y))
      (hgm.comp (measurable_const.sub measurable_id))
    have h2 : Var[Xx (periodicRiesz d s) lam x; poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t] =
        lam ^ 2 * (evariance (fun Y : Config d n => ∑ j, periodicRiesz d s (x - Y j))
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)).toReal := by
      have := variance_const_mul (-lam) (fun Y : Config d n => ∑ j, periodicRiesz d s (x - Y j))
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)
      rw [neg_sq] at this
      exact this
    rw [h2, ENNReal.ofReal_mul (sq_nonneg _)]
    unfold w
    refine mul_le_mul' le_rfl ?_
    exact (ENNReal.ofReal_toReal_le).trans h1
  -- the integral of the dominating function
  have hFm := measurable_Ft hd hs0 hsd lam x
  have hint_t : Measurable fun t : ℝ => ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) :=
    Measurable.lintegral_prod_right' (f := fun q : ℝ × Torus d => ‖periodicRiesz d s (x - q.2)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(q.1 * lam) * periodicRiesz d s (x - q.2)))) hFm
  have hWint : ∫⁻ t in Ioc (0 : ℝ) 1, w t ≤
      ENNReal.ofReal (lam ^ 2 * (C₁ * (n : ℝ)) * (Cw * ((N : ℝ) * deltaN d s N))) := by
    unfold w
    rw [lintegral_const_mul _ (hint_t.const_mul _), lintegral_const_mul _ hint_t]
    have := hCw N hN x
    calc ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (C₁ * (n : ℝ)) * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ))
        ≤ ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (C₁ * (n : ℝ)) * ENNReal.ofReal (Cw * ((N : ℝ) * deltaN d s N))) := by
          gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hWfin : ∫⁻ t in Ioc (0 : ℝ) 1, w t ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hWint
  obtain ⟨hD1, hD2⟩ := EF.ef_main hXm hb hXi w hwle hWfin
  have hWb : (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal ≤ βp ^ 2 * C₁ * Cw * deltaN d s N := by
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hWint).trans ?_
    rw [ENNReal.toReal_ofReal (by
      have := PreparationAux.one_le_N_deltaN (d := d) hs0 N (by omega)
      positivity)]
    have hq : lam ^ 2 * (n : ℝ) * N ≤ β ^ 2 := by
      rw [hlamdef, hn, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      have : (β / N) ^ 2 * ((N : ℝ) - 1) * N = β ^ 2 * ((N : ℝ) - 1) / N := by field_simp
      rw [this, div_le_iff₀ hN0]
      nlinarith [sq_nonneg β]
    have hδ0 : 0 ≤ deltaN d s N := by
      have := inv_le_deltaN (d := d) hs0 N (by omega)
      exact (inv_nonneg.2 hN0.le).trans this
    calc lam ^ 2 * (C₁ * (n : ℝ)) * (Cw * ((N : ℝ) * deltaN d s N))
        = (lam ^ 2 * (n : ℝ) * N) * (C₁ * Cw * deltaN d s N) := by ring
      _ ≤ βp ^ 2 * (C₁ * Cw * deltaN d s N) :=
          mul_le_mul_of_nonneg_right (hq.trans (pow_le_pow_left₀ hβ.le hβ2 2)) (by positivity)
      _ = βp ^ 2 * C₁ * Cw * deltaN d s N := by ring
  have hWnn : 0 ≤ (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal := ENNReal.toReal_nonneg
  rw [insDefect_eq hd hs0 hsd β hρ n lam hlam x]
  refine ⟨sub_nonneg.2 (EF.ef_cgf_ge hXm hb hXi), hD1.trans hWb, ?_⟩
  linarith

theorem eqmarg_cavity_tv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ N : ℕ, 2 ≤ N → ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) N (β / N) β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) A).toReal| ≤
        C * Real.sqrt (deltaN d s N / N) := by
  obtain ⟨C₁, hC₁, hvarU⟩ := eqmarg_pole_variance hd hs0 hsd βm βp hβm Λ0
  obtain ⟨Cd, hCdU⟩ := eqmarg_insDefect_le hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  set K1 : ℝ := C₁ * Real.exp (βp * B) with hK1
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  refine ⟨2 * Real.sqrt (2 * (K1 * K2)), by positivity, fun β hβ1 hβ2 ρ hρ hΛ N hN A hA => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hvar := hvarU β hβ1 hβ2 ρ hρ hΛ
  have hCd := hCdU β hβ1 hβ2 ρ hρ hΛ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hn1 hn0 hnN
  change |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) (β / ((n + 1 : ℕ) : ℝ)) β) A).toReal -
      (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β) A).toReal| ≤
      2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ))
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlamdef
  have hlnβ : lam * (n : ℝ) ≤ β := by
    rw [hlamdef]
    have : β / ((n + 1 : ℕ) : ℝ) * (n : ℝ) = β * ((n : ℝ) / ((n : ℝ) + 1)) := by push_cast; ring
    rw [this]
    have : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI hQ := cavity_isProb hd hs0 hsd β hρ (n + 1) lam hlam
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0def
  set Q := cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β with hQdef
  set i0 : Fin n := ⟨0, hn1⟩ with hi0
  set A' : Set (Config d n) := {Y | Y i0 ∈ A} with hA'
  have hA'm : MeasurableSet A' := (measurable_pi_apply i0) hA
  haveI hπ : IsProbabilityMeasure (firstMarginal Q) := by
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    infer_instance
  have hνA : firstMarginal P0 A = P0 A' := by
    unfold firstMarginal
    rw [dif_pos hn1, Measure.map_apply (measurable_pi_apply i0) hA]
    rfl
  have hdis := firstMarginal_disint hd hs0 hsd hρ hlam hlnβ hn1 hA
  -- the bound at each pole position
  have hδ0 : 0 ≤ deltaN d s (n + 1) := by
    have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ1 : deltaN d s (n + 1) ≤ 1 := deltaN_le_one hs0 hsd (by omega) (n + 1) (by omega)
  have hx : ∀ x : Torus d, |((poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A').toReal -
      (P0 A').toReal| ≤ 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)) := by
    intro x
    have hXm := measurable_Xx hgm (n := n) lam x
    have hb := Xx_le hd hs0 hsd hlam hlnβ hB0 hB x
    have hXi : Integrable (Xx (periodicRiesz d s) lam x) P0 :=
      integrable_Xx hd hs0 hsd hβ hρ (N := n + 1) hN x
    have hφm := measurable_fracIn (n := n) hA
    have htv := EF.ef_tv (P := P0) hXm hb hφm (fun Y => abs_fracIn_le hn1 A Y)
    have e1 : P0.tilted (Xx (periodicRiesz d s) lam x) =
        poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1 :=
      (poleLaw_one_eq hd hs0 hsd hρ hlam hlnβ x).symm
    have e0 : P0 = poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 0 :=
      (poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x).symm
    haveI hP1 := pole_isProb hd hs0 hsd β hρ n lam hlam x 1 zero_le_one
    haveI hP00 := pole_isProb hd hs0 hsd β hρ n lam hlam x 0 le_rfl
    have hint1 : ∫ Y, fracIn A Y ∂(P0.tilted (Xx (periodicRiesz d s) lam x)) =
        ((poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A').toReal := by
      rw [e1]
      exact integral_fracIn hn1 hA _ (poleLaw_exchangeable hd hs0 hsd β hρ n lam hlam x 1)
    have hint0 : ∫ Y, fracIn A Y ∂P0 = (P0 A').toReal :=
      integral_fracIn hn1 hA P0 (cavityLaw_exchangeable hd hs0 hsd β hρ n lam)
    have hV0 : Var[fracIn (n := n) A; P0] ≤ K1 / (n : ℝ) := by
      rw [e0]
      refine (var_fracIn_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := n + 1) hN x (t := 0) ⟨le_rfl, zero_le_one⟩ hA).trans ?_
      rw [hK1]
      gcongr <;> omega
    have hV1 : Var[fracIn (n := n) A; P0.tilted (Xx (periodicRiesz d s) lam x)] ≤ K1 / (n : ℝ) := by
      rw [e1]
      refine (var_fracIn_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := n + 1) hN x (t := 1) ⟨zero_le_one, le_rfl⟩ hA).trans ?_
      rw [hK1]
      gcongr <;> omega
    obtain ⟨-, -, hΔ⟩ := hCd (n + 1) hN x
    have hΔ' : cgf (Xx (periodicRiesz d s) lam x) P0 1 - 2 * cgf (Xx (periodicRiesz d s) lam x) P0 (1 / 2) ≤
        |Cd| * deltaN d s (n + 1) := hΔ.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
    have hee := exp_sub_one_le _ |Cd| (deltaN d s (n + 1)) hδ0 hδ1 (abs_nonneg _) hΔ'
    rw [hint1, hint0] at htv
    refine htv.trans ?_
    exact sqrt_chain (n := (n : ℝ)) (N := ((n + 1 : ℕ) : ℝ)) hn0 hN0 hnN (by positivity) (by positivity) hδ0 hV0 hV1 hee
  -- integrate
  have hfm : AEMeasurable (fun x : Torus d => (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A')
      (firstMarginal Q) := (measurable_poleLaw_set hd hs0 hsd hρ hlam hlnβ hA'm).aemeasurable
  have hfin : ∀ x : Torus d, (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A' < ∞ := fun x => by
    haveI := pole_isProb hd hs0 hsd β hρ n lam hlam x 1 zero_le_one
    exact measure_lt_top _ _
  have hπA : (firstMarginal Q A).toReal =
      ∫ x, ((poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A').toReal ∂(firstMarginal Q) := by
    rw [integral_toReal hfm (Filter.Eventually.of_forall hfin), ← hdis]
  rw [hνA]
  have hdiff : (firstMarginal Q A).toReal - (P0 A').toReal =
      ∫ x, (((poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A').toReal - (P0 A').toReal)
        ∂(firstMarginal Q) := by
    have hinteg : Integrable (fun x : Torus d =>
        ((poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A').toReal) (firstMarginal Q) :=
      Integrable.of_bound (C := 1) ((measurable_poleLaw_set hd hs0 hsd hρ hlam hlnβ hA'm).ennreal_toReal.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          haveI := pole_isProb hd hs0 hsd β hρ n lam hlam x 1 zero_le_one
          rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one))
    rw [integral_sub hinteg (integrable_const _), hπA]
    simp
  rw [hdiff, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := firstMarginal Q)
    (f := fun x : Torus d => ((poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A').toReal - (P0 A').toReal)
    (C := 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt (deltaN d s (n + 1) / ((n + 1 : ℕ) : ℝ)))
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hx x)
  simpa using this

end EqMarg

end HRS
