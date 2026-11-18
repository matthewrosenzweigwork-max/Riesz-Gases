/-
# HRS.Equilibrium.MarginalPole -- insertion defect and cavity total variation (EQ-02)

With `P₀ = cavityLaw g μ n λ β` (`n = N-1`, `λ = β/N`) and `X_x = -λ ∑_j g(x - y_j)`:

* `insDefect_le`: `0 ≤ D_N(x) = F_{N,x}(1) - F'_{N,x}(0) ≤ C δ_N` uniformly in `x`
  (`A:eq:insertion-estimates`), from the variance clause of Lemma 4.1 along the pole path
  `P₀.tilted (t X_x) = P_n^{x,t}`;
* `cavity_tv`: `|π_N(A) - ν_n(A)| ≤ C √(δ_N/N)` (`A:eq:cavity-TV`).
-/
import HRS.Equilibrium.MarginalCavity
import HRS.Equilibrium.PreparationAux

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MarginalAux

variable {d : ℕ}

/-! ### The `t`-integral of the pole weight -/

theorem int_t_exact {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    ∫ t in (0 : ℝ)..1, a ^ 2 * Real.exp (-(t * lam) * a) = (a / lam) * (1 - Real.exp (-lam * a)) := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => -(a / lam) * Real.exp (-(t * lam) * a))
      (a ^ 2 * Real.exp (-(t * lam) * a)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(t * lam) * a) (-lam * a) t := by
      have := ((hasDerivAt_id t).mul_const lam).neg.mul_const a
      simpa using this
    have h2 := (h1.exp).const_mul (-(a / lam))
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by exact (Continuous.intervalIntegrable (by fun_prop) _ _))]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul, mul_one]
  ring_nf

theorem int_t_bound {lam : ℝ} (hlam : 0 < lam) {B : ℝ} (hB0 : 0 ≤ B) (a : ℝ) (ha : -B ≤ a) :
    ‖a‖ₑ ^ 2 * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (-(t * lam) * a)) ≤
      ENNReal.ofReal (B ^ 2 * Real.exp (lam * B) + min (max a 0 ^ 2) ((1 / lam) * max a 0)) := by
  have hcont : Continuous fun t : ℝ => Real.exp (-(t * lam) * a) := by fun_prop
  rw [PoleCavityAux.lintegral_Ioc_ofReal 0 1 zero_le_one _ (hcont.intervalIntegrable _ _)
    (fun t _ => (Real.exp_pos _).le), Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), sq_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : a ^ 2 * ∫ t in (0 : ℝ)..1, Real.exp (-(t * lam) * a) = (a / lam) * (1 - Real.exp (-lam * a)) := by
    rw [← int_t_exact hlam a, intervalIntegral.integral_const_mul]
  rw [h1]
  rcases le_total 0 a with h0 | h0
  · rw [max_eq_left h0]
    have e1 : (a / lam) * (1 - Real.exp (-lam * a)) ≤ (1 / lam) * a := by
      have h5 : 1 - Real.exp (-lam * a) ≤ 1 := by linarith [Real.exp_pos (-lam * a)]
      calc (a / lam) * (1 - Real.exp (-lam * a)) ≤ (a / lam) * 1 :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = (1 / lam) * a := by ring
    have e2 : (a / lam) * (1 - Real.exp (-lam * a)) ≤ a ^ 2 := by
      have h3 := Real.add_one_le_exp (-lam * a)
      have : 1 - Real.exp (-lam * a) ≤ lam * a := by linarith
      calc (a / lam) * (1 - Real.exp (-lam * a)) ≤ (a / lam) * (lam * a) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = a ^ 2 := by field_simp
    have : 0 ≤ B ^ 2 * Real.exp (lam * B) := by positivity
    linarith [le_min e2 e1]
  · rw [max_eq_right h0]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, min_self, add_zero]
    have hb : |a| ≤ B := by rw [abs_of_nonpos h0]; linarith
    have e3 : Real.exp (-lam * a) - 1 ≤ (lam * |a|) * Real.exp (lam * |a|) := by
      have h3 := Real.add_one_le_exp (-(lam * |a|))
      have h4 : Real.exp (-lam * a) = Real.exp (lam * |a|) := by
        rw [abs_of_nonpos h0]; congr 1; ring
      rw [h4]
      have h5 : Real.exp (-(lam * |a|)) * Real.exp (lam * |a|) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (lam * |a|)]
    have e4 : (a / lam) * (1 - Real.exp (-lam * a)) = (|a| / lam) * (Real.exp (-lam * a) - 1) := by
      rw [abs_of_nonpos h0]; field_simp; ring
    rw [e4]
    calc (|a| / lam) * (Real.exp (-lam * a) - 1) ≤ (|a| / lam) * ((lam * |a|) * Real.exp (lam * |a|)) :=
          mul_le_mul_of_nonneg_left e3 (by positivity)
      _ = |a| ^ 2 * Real.exp (lam * |a|) := by field_simp
      _ ≤ B ^ 2 * Real.exp (lam * B) := by
          gcongr
      _ ≤ _ := by simp

/-! ### The pole path and the cavity marginals -/

section Pole

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-- `X_x(Y) = -λ ∑_j g(x - y_j)`. -/
def Xx (g : Torus d → ℝ) {n : ℕ} (lam : ℝ) (x : Torus d) (Y : Config d n) : ℝ :=
  (-lam) * ∑ j, g (x - Y j)

theorem measurable_Xx {g : Torus d → ℝ} (hg : Measurable g) {n : ℕ} (lam : ℝ) (x : Torus d) :
    Measurable (Xx g (n := n) lam x) :=
  (Finset.measurable_sum _ fun j _ => hg.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _

theorem poleLaw_eq_tilted_cavity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (x : Torus d)
    (t : ℝ) :
    poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t =
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β).tilted
        (fun Y => t * Xx (periodicRiesz d s) lam x Y) := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  have hgm := measurable_periodicRiesz hd hs0 hsd
  unfold poleLaw
  have hm : Measurable fun Y : Config d n => -(t * lam) * ∑ i, periodicRiesz d s (x - Y i) :=
    (Finset.measurable_sum _ fun j _ => hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _
  rw [Glue.tiltMeasure_eq_tilted_of_measurable _ _ hm]
  congr 1
  funext Y
  unfold Xx
  ring

theorem poleLaw_zero_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (x : Torus d) :
    poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 0 =
      cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  rw [poleLaw_eq_tilted_cavity hd hs0 hsd β hρ n lam hlam x 0]
  simp only [zero_mul]
  exact tilted_zero _

/-- Every one-coordinate marginal of the cavity law has bounded density with respect to `μ`. -/
theorem cavity_marginal_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1),
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map (fun Y : Config d (N - 1) => Y i) ≤
        ENNReal.ofReal C • withDensityReal ρ := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  refine ⟨Real.exp (Kbound (periodicRiesz d s) B Cc β 1), Real.exp_pos _, fun N hN i => ?_⟩
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
  refine h.trans (le_of_eq ?_)
  rw [← withDensity_const]
  congr 1
  funext y
  simp

end Pole


section Pole2

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

theorem integrable_coord (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) (x : Torus d) (j : Fin (N - 1)) :
    Integrable (fun Y : Config d (N - 1) => periodicRiesz d s (x - Y j))
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C, hC, hmarg⟩ := cavity_marginal_le hd hs0 hsd hβ hρ
  obtain ⟨B, Cc, hB0, hK⟩ := kerData_periodicRiesz hd hs0 hsd hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hint : Integrable (fun y => periodicRiesz d s (x - y))
      ((cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
        (fun Y : Config d (N - 1) => Y j)) :=
    ((hK.int x).smul_measure (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top).mono_measure (hmarg N hN j)
  have := (integrable_map_measure (hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).1 hint
  exact this

theorem integrable_Xx (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) (x : Torus d) :
    Integrable (Xx (periodicRiesz d s) (β / N) x)
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) :=
  (integrable_finset_sum _ fun j _ => integrable_coord hd hs0 hsd hβ hρ hN x j).const_mul _

end Pole2


section Defect

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

theorem inv_le_deltaN (hs0 : 0 ≤ s) (N : ℕ) (hN : 1 ≤ N) : (N : ℝ)⁻¹ ≤ deltaN d s N := by
  have h := PreparationAux.one_le_N_deltaN (d := d) hs0 N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [inv_le_iff_one_le_mul₀ hN0]
  linarith

/-- `D_N(x) = F_{N,x}(1) - F'_{N,x}(0)`. -/
def insDefect (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β : ℝ) (x : Torus d) : ℝ :=
  Real.log (phiIns g μ n lam β x) + lam * ∫ Y, ∑ j, g (x - Y j) ∂(cavityLaw g μ n lam β)

theorem insDefect_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (x : Torus d) :
    insDefect (periodicRiesz d s) (withDensityReal ρ) n lam β x =
      cgf (Xx (periodicRiesz d s) lam x) (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) 1 -
        (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β)[Xx (periodicRiesz d s) lam x] := by
  unfold insDefect phiIns cgf mgf Xx
  simp only [one_mul, integral_const_mul]
  have : ∀ Y : Config d n, (-lam) * ∑ j, periodicRiesz d s (x - Y j) = -lam * ∑ j, periodicRiesz d s (x - Y j) :=
    fun Y => rfl
  ring

theorem w_integral_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Cw * ((N : ℝ) * deltaN d s N)) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_density_bound hρ
  obtain ⟨CI, hCI0, hCI⟩ := Ibound hd hs0 hsd β hβ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨Λ * (B ^ 2 * Real.exp (β * B) + CI), by positivity, fun N hN x => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 < β / N := by positivity
  have hlamle : β / N ≤ β := by
    rw [div_le_iff₀ hN0]; have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  set lam : ℝ := β / N with hlamdef
  -- joint measurability
  have hF : Measurable fun q : ℝ × Torus d => ‖periodicRiesz d s (x - q.2)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(q.1 * lam) * periodicRiesz d s (x - q.2))) := by
    refine (((hgm.comp (measurable_const.sub measurable_snd)).enorm).pow_const 2).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_fst.mul_const lam).neg.mul (hgm.comp (measurable_const.sub measurable_snd))))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  -- pointwise bound in y
  set Mfun : Torus d → ℝ := fun z => min (rieszPos d s z ^ 2) ((N : ℝ) / β * rieszPos d s z) with hMfun
  have hpt : ∀ y : Torus d, ∫⁻ t in Ioc (0 : ℝ) 1, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ≤
      ENNReal.ofReal (B ^ 2 * Real.exp (β * B) + Mfun (x - y)) := by
    intro y
    have hmt : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((measurable_id.mul_const lam).neg.mul_const _))
    rw [lintegral_const_mul _ hmt]
    refine (int_t_bound hlam hB0 _ (hB _)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : B ^ 2 * Real.exp (lam * B) ≤ B ^ 2 * Real.exp (β * B) := by
      gcongr
    have h2 : min (max (periodicRiesz d s (x - y)) 0 ^ 2) ((1 / lam) * max (periodicRiesz d s (x - y)) 0) =
        Mfun (x - y) := by
      simp only [hMfun, rieszPos, hlamdef, one_div_div]
    rw [h2]; linarith
  calc ∫⁻ y, (∫⁻ t in Ioc (0 : ℝ) 1, ‖periodicRiesz d s (x - y)‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y)))) ∂(withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal (B ^ 2 * Real.exp (β * B) + Mfun (x - y)) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (B ^ 2 * Real.exp (β * B) + Mfun z) :=
        KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (B ^ 2 * Real.exp (β * B) + Mfun z)) x
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal (B ^ 2 * Real.exp (β * B)) + ENNReal.ofReal (CI * ((N : ℝ) * deltaN d s N))) := by
        gcongr
        have hMn : ∀ z, 0 ≤ Mfun z := fun z => by
          have h0 : 0 ≤ rieszPos d s z := le_max_right _ _
          exact le_min (by positivity) (by positivity)
        calc ∫⁻ z : Torus d, ENNReal.ofReal (B ^ 2 * Real.exp (β * B) + Mfun z)
            = ∫⁻ z : Torus d, (ENNReal.ofReal (B ^ 2 * Real.exp (β * B)) + ENNReal.ofReal (Mfun z)) := by
              refine lintegral_congr fun z => ?_
              rw [ENNReal.ofReal_add (by positivity) (hMn z)]
          _ = ENNReal.ofReal (B ^ 2 * Real.exp (β * B)) + ∫⁻ z : Torus d, ENNReal.ofReal (Mfun z) := by
              have hpm := measurable_rieszPos hd hs0 hsd
              have hmM : Measurable fun z : Torus d => ENNReal.ofReal (Mfun z) :=
                ENNReal.measurable_ofReal.comp ((hpm.pow_const 2).min (measurable_const.mul hpm))
              rw [lintegral_add_right (fun _ : Torus d => ENNReal.ofReal (B ^ 2 * Real.exp (β * B))) hmM,
                lintegral_const, measure_univ, mul_one]
          _ ≤ _ := by gcongr; exact hCI N hN
    _ ≤ ENNReal.ofReal (Λ * (B ^ 2 * Real.exp (β * B) + CI) * ((N : ℝ) * deltaN d s N)) := by
        have h1 := PreparationAux.one_le_N_deltaN (d := d) hs0 N (by omega)
        rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hCI0 (by linarith)),
          ← ENNReal.ofReal_mul hΛ0.le]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : 0 ≤ B ^ 2 * Real.exp (β * B) := by positivity
        nlinarith [mul_nonneg hΛ0.le (mul_nonneg h2 (sub_nonneg.2 h1))]

theorem measurable_Ft (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (lam : ℝ) (x : Torus d) :
    Measurable fun q : ℝ × Torus d => ‖periodicRiesz d s (x - q.2)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(q.1 * lam) * periodicRiesz d s (x - q.2))) := by
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine (((hgm.comp (measurable_const.sub measurable_snd)).enorm).pow_const 2).mul ?_
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_fst.mul_const lam).neg.mul (hgm.comp (measurable_const.sub measurable_snd))))

theorem insDefect_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      0 ≤ insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ∧
      insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ C * deltaN d s N ∧
      cgf (Xx (periodicRiesz d s) (β / N) x)
          (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) 1 -
        2 * cgf (Xx (periodicRiesz d s) (β / N) x)
          (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) (1 / 2) ≤ C * deltaN d s N := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C₁, hC₁, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  obtain ⟨Cw, hCw0, hCw⟩ := w_integral_bound hd hs0 hsd hβ hρ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  refine ⟨β ^ 2 * C₁ * Cw, fun N hN x => ?_⟩
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
  have hWb : (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal ≤ β ^ 2 * C₁ * Cw * deltaN d s N := by
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
      _ ≤ β ^ 2 * (C₁ * Cw * deltaN d s N) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = β ^ 2 * C₁ * Cw * deltaN d s N := by ring
  have hWnn : 0 ≤ (∫⁻ t in Ioc (0 : ℝ) 1, w t).toReal := ENNReal.toReal_nonneg
  rw [insDefect_eq hd hs0 hsd β hρ n lam hlam x]
  refine ⟨sub_nonneg.2 (EF.ef_cgf_ge hXm hb hXi), hD1.trans hWb, ?_⟩
  linarith

end Defect


/-! ### Disintegration of `Q_{N,β}(μ)`: conditional law of the other particles -/

section Disint

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

theorem Xx_perm (g : Torus d → ℝ) {n : ℕ} (lam : ℝ) (x : Torus d) (σ : Equiv.Perm (Fin n))
    (Y : Config d n) : Xx g lam x (fun i => Y (σ i)) = Xx g lam x Y := by
  unfold Xx
  rw [Equiv.sum_comp σ (fun i => g (x - Y i))]

theorem poleLaw_exchangeable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (x : Torus d)
    (t : ℝ) :
    Entropy.IsExchangeable (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t) := by
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hP0 := cavityLaw_exchangeable hd hs0 hsd β hρ n lam
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  intro σ
  unfold poleLaw
  have hm : Measurable fun Y : Config d n => -(t * lam) * ∑ i, periodicRiesz d s (x - Y i) :=
    (Finset.measurable_sum _ fun j _ => hgm.comp (measurable_const.sub (measurable_pi_apply j))).const_mul _
  exact RefSmall.tiltMeasure_map_perm _ _ hm _ (measurable_pi_iff.2 fun k => measurable_pi_apply _)
    (hP0 σ) (fun Y => by
      show -(t * lam) * ∑ i, periodicRiesz d s (x - Y (σ i)) = -(t * lam) * ∑ i, periodicRiesz d s (x - Y i)
      rw [Equiv.sum_comp σ (fun i => periodicRiesz d s (x - Y i))])

end Disint


section Disint2

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
  {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (hln : lam * n ≤ β)

include hd hs0 hsd hρ hlam hln

theorem poleLaw_one_eq (x : Torus d) :
    poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1 =
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β).tilted (Xx (periodicRiesz d s) lam x) := by
  rw [poleLaw_eq_tilted_cavity hd hs0 hsd β hρ n lam hlam x 1]
  simp only [one_mul]

theorem lintegral_jointW_indicator (x : Torus d) {A' : Set (Config d n)} (hA' : MeasurableSet A') :
    ∫⁻ Y in A', jointW (periodicRiesz d s) (withDensityReal ρ) lam β (x, Y)
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      ENNReal.ofReal (Real.exp (uIns (periodicRiesz d s) (withDensityReal ρ) n lam β x)) *
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A' := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hphi := phiIns_pos hd hs0 hsd hρ hlam hln x
  rw [poleLaw_one_eq hd hs0 hsd hρ hlam hln x, tilted_apply' _ _ hA']
  have hphi' : ∫ Y, Real.exp (Xx (periodicRiesz d s) lam x Y)
      ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x := rfl
  rw [hphi']
  have h1 : ∀ Y : Config d n, jointW (periodicRiesz d s) (withDensityReal ρ) lam β (x, Y) =
      ENNReal.ofReal (Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)) *
        ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam x Y)) := by
    intro Y
    unfold jointW Xx
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hmX : Measurable fun Y : Config d n => ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam x Y)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_Xx hgm lam x))
  have e2 : ∀ Y : Config d n, ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam x Y) /
        phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x) =
      ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam x Y)) *
        (ENNReal.ofReal (phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x))⁻¹ := fun Y => by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_inv_of_pos hphi]
  simp_rw [e2]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hphi).ne')]
  have hL : ∫⁻ Y in A', jointW (periodicRiesz d s) (withDensityReal ρ) lam β (x, Y)
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) =
      ENNReal.ofReal (Real.exp (β * convMeasure (periodicRiesz d s) (withDensityReal ρ) x)) *
        ∫⁻ Y in A', ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam x Y))
          ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
    rw [← lintegral_const_mul _ hmX]
    exact lintegral_congr fun Y => h1 Y
  rw [hL, exp_uIns hd hs0 hsd hρ hlam hln x, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc,
    ← mul_assoc (ENNReal.ofReal (phiIns _ _ _ _ _ x)), mul_comm (ENNReal.ofReal (phiIns _ _ _ _ _ x)),
    mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hphi).ne' ENNReal.ofReal_ne_top, mul_one]

theorem measurable_poleLaw_set {A' : Set (Config d n)} (hA' : MeasurableSet A') :
    Measurable fun x : Torus d => (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A' := by
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hphim := measurable_phiIns hd hs0 hsd hρ hlam hln
  have e : ∀ x, (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1) A' =
      ∫⁻ Y, A'.indicator (fun Y => ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam x Y) /
        phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β x)) Y
        ∂(cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β) := by
    intro x
    rw [poleLaw_one_eq hd hs0 hsd hρ hlam hln x, tilted_apply' _ _ hA', ← lintegral_indicator hA']
    rfl
  simp_rw [e]
  have hXj : Measurable fun q : Torus d × Config d n => Xx (periodicRiesz d s) lam q.1 q.2 :=
    (Finset.measurable_sum _ fun j _ =>
      hgm.comp (measurable_fst.sub ((measurable_pi_apply j).comp measurable_snd))).const_mul _
  refine Measurable.lintegral_prod_right' (f := fun q : Torus d × Config d n =>
    A'.indicator (fun Y => ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam q.1 Y) /
        phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β q.1)) q.2) ?_
  have : (fun q : Torus d × Config d n =>
    A'.indicator (fun Y => ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam q.1 Y) /
        phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β q.1)) q.2) =
      fun q => (Prod.snd ⁻¹' A').indicator (fun q : Torus d × Config d n =>
        ENNReal.ofReal (Real.exp (Xx (periodicRiesz d s) lam q.1 q.2) /
        phiIns (periodicRiesz d s) (withDensityReal ρ) n lam β q.1)) q := by
    funext q; by_cases h : q.2 ∈ A' <;> simp [Set.indicator, h]
  rw [this]
  exact (ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hXj).div
    (hphim.comp measurable_fst))).indicator (measurable_snd hA')

theorem firstMarginal_disint (hn : 0 < n) {A : Set (Torus d)} (hA : MeasurableSet A) :
    firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β) A =
      ∫⁻ x, (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 1)
        {Y : Config d n | Y ⟨0, hn⟩ ∈ A}
        ∂(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1) lam β)) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_periodicRiesz hd hs0 hsd
  haveI := cavity_isProb hd hs0 hsd β hρ n lam hlam
  haveI := cavity_isProb hd hs0 hsd β hρ (n + 1) lam hlam
  obtain ⟨κ, hκ, hpt, hfm⟩ := kappa_spec hd hs0 hsd hρ hlam hln
  set μ := withDensityReal ρ with hμdef
  set Q := cavityLaw (periodicRiesz d s) μ (n + 1) lam β with hQ
  set P0 := cavityLaw (periodicRiesz d s) μ n lam β with hP0
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set A' : Set (Config d n) := {Y | Y i0 ∈ A} with hA'
  have hA'm : MeasurableSet A' := (measurable_pi_apply i0) hA
  have hQex := cavityLaw_exchangeable hd hs0 hsd β hρ (n + 1) lam
  have hmarg : firstMarginal Q = Q.map (fun X : Config d (n + 1) => X (Fin.succ i0)) := by
    unfold firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    exact hQex.marginal_eq ⟨0, Nat.succ_pos n⟩ (Fin.succ i0)
  have hT : Measurable fun X : Config d (n + 1) => (X 0, Fin.tail X) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  set S : Set (Torus d × Config d n) := {p | p.2 i0 ∈ A} with hS
  have hSm : MeasurableSet S := ((measurable_pi_apply i0).comp measurable_snd) hA
  have hjm := measurable_jointW hgm μ (n := n) lam β
  calc firstMarginal Q A = Q.map (fun X : Config d (n + 1) => X (Fin.succ i0)) A := by rw [hmarg]
    _ = (Q.map fun X : Config d (n + 1) => (X 0, Fin.tail X)) S := by
        rw [Measure.map_apply (measurable_pi_apply (Fin.succ i0)) hA, Measure.map_apply hT hSm]
        rfl
    _ = κ * ∫⁻ x, ∫⁻ Y in A', jointW (periodicRiesz d s) μ lam β (x, Y) ∂P0 ∂μ := by
        rw [hκ, Measure.smul_apply, withDensity_apply _ hSm, smul_eq_mul, ← lintegral_indicator hSm,
          lintegral_prod _ (hjm.indicator hSm).aemeasurable]
        congr 1
        refine lintegral_congr fun x => ?_
        rw [← lintegral_indicator hA'm]
        refine lintegral_congr fun Y => ?_
        by_cases hY : Y i0 ∈ A
        · have : (x, Y) ∈ S := hY
          simp [Set.indicator, hY, this, hA']
        · have : (x, Y) ∉ S := hY
          simp [Set.indicator, hY, this, hA']
    _ = κ * ∫⁻ x, ENNReal.ofReal (Real.exp (uIns (periodicRiesz d s) μ n lam β x)) *
          (poleLaw (periodicRiesz d s) μ n lam β x 1) A' ∂μ := by
        congr 1
        refine lintegral_congr fun x => ?_
        exact lintegral_jointW_indicator hd hs0 hsd hρ hlam hln x hA'm
    _ = _ := by
        have hum := measurable_uIns hd hs0 hsd hρ hlam hln
        have hdens : Measurable fun x : Torus d => ENNReal.ofReal (Real.exp
            (uIns (periodicRiesz d s) μ n lam β x - Real.log (∫ y, Real.exp
              (uIns (periodicRiesz d s) μ n lam β y) ∂μ))) :=
          ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hum.sub measurable_const))
        have hmeas : Measurable fun x : Torus d => ENNReal.ofReal (Real.exp (uIns (periodicRiesz d s) μ n lam β x)) *
            (poleLaw (periodicRiesz d s) μ n lam β x 1) A' :=
          (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hum)).mul
            (measurable_poleLaw_set hd hs0 hsd hρ hlam hln hA'm)
        rw [hfm, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdens
          (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top), ← lintegral_const_mul _ hmeas]
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, ← hpt x, mul_assoc]

end Disint2


/-! ### The cavity total variation -/

section TV

variable {s : ℝ}

open HRS.External HRS.PoleCavityAux

/-- The fraction `φ_A(Y) = n⁻¹ ∑_j 1_A(y_j)` of particles in `A`. -/
def fracIn {n : ℕ} (A : Set (Torus d)) (Y : Config d n) : ℝ :=
  (1 / (n : ℝ)) * ∑ j, A.indicator (fun _ => (1 : ℝ)) (Y j)

theorem measurable_fracIn {n : ℕ} {A : Set (Torus d)} (hA : MeasurableSet A) :
    Measurable (fracIn (n := n) A) :=
  (Finset.measurable_sum _ fun j _ =>
    (measurable_const.indicator hA).comp (measurable_pi_apply j)).const_mul _

theorem abs_fracIn_le {n : ℕ} (hn : 0 < n) (A : Set (Torus d)) (Y : Config d n) :
    |fracIn A Y| ≤ 1 := by
  unfold fracIn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ∀ j, |A.indicator (fun _ => (1 : ℝ)) (Y j)| ≤ 1 := fun j => by
    by_cases h : Y j ∈ A <;> simp [Set.indicator, h]
  rw [abs_mul, abs_of_pos (by positivity)]
  have : |∑ j, A.indicator (fun _ => (1 : ℝ)) (Y j)| ≤ n := by
    calc _ ≤ ∑ j, |A.indicator (fun _ => (1 : ℝ)) (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => h1 j
      _ = n := by simp
  calc 1 / (n : ℝ) * |∑ j, A.indicator (fun _ => (1 : ℝ)) (Y j)| ≤ 1 / (n : ℝ) * n :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 := by field_simp

theorem integral_fracIn {n : ℕ} (hn : 0 < n) {A : Set (Torus d)} (hA : MeasurableSet A)
    (Pm : Measure (Config d n)) [IsProbabilityMeasure Pm] (hR : Entropy.IsExchangeable Pm) :
    ∫ Y, fracIn A Y ∂Pm = (Pm {Y : Config d n | Y ⟨0, hn⟩ ∈ A}).toReal := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold fracIn
  rw [integral_const_mul, integral_finset_sum]
  · have : ∀ j : Fin n, ∫ Y, A.indicator (fun _ => (1 : ℝ)) (Y j) ∂Pm =
        (Pm {Y : Config d n | Y ⟨0, hn⟩ ∈ A}).toReal := by
      intro j
      have h1 : ∫ Y, A.indicator (fun _ => (1 : ℝ)) (Y j) ∂Pm = (Pm {Y : Config d n | Y j ∈ A}).toReal := by
        have : (fun Y : Config d n => A.indicator (fun _ => (1 : ℝ)) (Y j)) =
            ({Y : Config d n | Y j ∈ A}).indicator (fun _ => (1 : ℝ)) := by
          funext Y; simp [Set.indicator]
        have hm : MeasurableSet {Y : Config d n | Y j ∈ A} := (measurable_pi_apply j) hA
        rw [this, integral_indicator_const _ hm]
        simp [Measure.real]
      rw [h1]
      have := hR.marginal_eq j ⟨0, hn⟩
      have h2 := congrArg (fun m => m A) this
      rw [Measure.map_apply (measurable_pi_apply j) hA, Measure.map_apply (measurable_pi_apply (⟨0, hn⟩ : Fin n)) hA] at h2
      exact congrArg ENNReal.toReal h2
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro j _
    exact (Integrable.of_bound (C := 1) ((measurable_const.indicator hA).comp (measurable_pi_apply j)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun Y => by
        by_cases h : Y j ∈ A <;> simp [Set.indicator, h]))

theorem deltaN_le_one (hs0 : 0 ≤ s) (hsd : s < d) (hd : 1 ≤ d) (N : ℕ) (hN : 1 ≤ N) :
    deltaN d s N ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs with h1 h2
  · exact inv_le_one_of_one_le₀ hN1
  · rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp, inv_mul_le_iff₀ hN0]
    have := Real.log_le_sub_one_of_pos hN0
    linarith
  · have hspos : 0 < s := by
      push Not at h1
      have : (0 : ℝ) < (d : ℝ) / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        positivity
      linarith
    have hp : 1 < (d : ℝ) / s := by
      rw [lt_div_iff₀ hspos]; linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)

theorem var_fracIn_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hvar : ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C₁ * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ periodicRiesz d s z) {N : ℕ} (hN : 2 ≤ N) (x : Torus d)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {A : Set (Torus d)} (hA : MeasurableSet A) :
    Var[fracIn (n := N - 1) A; poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t] ≤
      C₁ * Real.exp (β * B) / ((N - 1 : ℕ) : ℝ) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - 1)
  have hlam : 0 ≤ β / N := by positivity
  have hlamle : β / N ≤ β := by
    rw [div_le_iff₀ hN0]; have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  set n : ℕ := N - 1 with hn
  set lam : ℝ := β / N with hlamdef
  have hf : Measurable (A.indicator (fun _ : Torus d => (1 : ℝ))) := measurable_const.indicator hA
  have h1 := hvar N hN x t ht (A.indicator (fun _ => (1 : ℝ))) hf
  have h2 : Var[fracIn (n := n) A; poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t] =
      (1 / (n : ℝ)) ^ 2 * (evariance (fun Y : Config d n => ∑ i, A.indicator (fun _ : Torus d => (1 : ℝ)) (Y i))
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)).toReal :=
    variance_const_mul (1 / (n : ℝ)) (fun Y : Config d n => ∑ i, A.indicator (fun _ : Torus d => (1 : ℝ)) (Y i)) _
  rw [h2]
  have h3 : ∫⁻ y, ‖A.indicator (fun _ : Torus d => (1 : ℝ)) y‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Real.exp (β * B)) := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (β * B)) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e1 : ‖A.indicator (fun _ : Torus d => (1 : ℝ)) y‖ₑ ^ 2 ≤ 1 := by
            by_cases h : y ∈ A <;> simp [Set.indicator, h]
          have e2 : ENNReal.ofReal (Real.exp (-(t * lam) * periodicRiesz d s (x - y))) ≤
              ENNReal.ofReal (Real.exp (β * B)) := by
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have h4 := hB (x - y)
            have h5 : 0 ≤ t * lam := mul_nonneg ht.1 hlam
            have h6 : t * lam ≤ β := by nlinarith [ht.2]
            nlinarith
          calc _ ≤ 1 * ENNReal.ofReal (Real.exp (β * B)) := by gcongr
            _ = _ := one_mul _
      _ = ENNReal.ofReal (Real.exp (β * B)) := by simp
  have h4 : (evariance (fun Y : Config d n => ∑ i, A.indicator (fun _ : Torus d => (1 : ℝ)) (Y i))
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)).toReal ≤ C₁ * n * Real.exp (β * B) := by
    have h5 := h1.trans (mul_le_mul' le_rfl h3)
    rw [← ENNReal.ofReal_mul (by positivity)] at h5
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h5).trans (by rw [ENNReal.toReal_ofReal (by positivity)])
  calc (1 / (n : ℝ)) ^ 2 * (evariance _ _).toReal ≤ (1 / (n : ℝ)) ^ 2 * (C₁ * n * Real.exp (β * B)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = C₁ * Real.exp (β * B) / n := by field_simp

theorem Xx_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β lam : ℝ} {n : ℕ} (hlam : 0 ≤ lam)
    (hln : lam * n ≤ β) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, -B ≤ periodicRiesz d s z) (x : Torus d)
    (Y : Config d n) : Xx (periodicRiesz d s) lam x Y ≤ β * B := by
  have h1 := sum_ge_of_ge (periodicRiesz d s) (fun z => hB z) (n := n) x Y
  unfold Xx
  have : lam * (B * n) ≤ β * B := by
    have : lam * (B * n) = (lam * n) * B := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hln hB0
  nlinarith

theorem exp_sub_one_le (Δ c δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c) (hΔ : Δ ≤ c * δ) :
    Real.exp Δ - 1 ≤ (c * Real.exp c) * δ := by
  rcases le_total Δ 0 with h | h
  · have : Real.exp Δ ≤ 1 := Real.exp_le_one_iff.2 h
    have : 0 ≤ (c * Real.exp c) * δ := by positivity
    linarith
  · have h1 : Real.exp Δ - 1 ≤ Δ * Real.exp Δ := by
      have h2 := Real.add_one_le_exp (-Δ)
      have h3 : Real.exp (-Δ) * Real.exp Δ = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos Δ]
    have h4 : Δ ≤ c := hΔ.trans (by nlinarith)
    have h5 : Real.exp Δ ≤ Real.exp c := Real.exp_le_exp.2 h4
    calc Real.exp Δ - 1 ≤ Δ * Real.exp Δ := h1
      _ ≤ (c * δ) * Real.exp c := mul_le_mul hΔ h5 (Real.exp_pos _).le (by positivity)
      _ = (c * Real.exp c) * δ := by ring

theorem sqrt_chain {a b e K1 K2 δ : ℝ} {n N : ℝ} (hn : 0 < n) (hN : 0 < N) (hnN : N ≤ 2 * n)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hδ : 0 ≤ δ) (ha : a ≤ K1 / n) (hb : b ≤ K1 / n) (he : e ≤ K2 * δ) :
    (Real.sqrt a + Real.sqrt b) * Real.sqrt e ≤ 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt (δ / N) := by
  have h1 : Real.sqrt a ≤ Real.sqrt (K1 / n) := Real.sqrt_le_sqrt ha
  have h2 : Real.sqrt b ≤ Real.sqrt (K1 / n) := Real.sqrt_le_sqrt hb
  have h3 : Real.sqrt e ≤ Real.sqrt (K2 * δ) := Real.sqrt_le_sqrt he
  have h4 : (Real.sqrt a + Real.sqrt b) * Real.sqrt e ≤ (2 * Real.sqrt (K1 / n)) * Real.sqrt (K2 * δ) :=
    mul_le_mul (by linarith) h3 (Real.sqrt_nonneg _) (by positivity)
  refine h4.trans ?_
  have h5 : Real.sqrt (K1 / n) * Real.sqrt (K2 * δ) ≤ Real.sqrt (2 * (K1 * K2)) * Real.sqrt (δ / N) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : K1 / n * (K2 * δ) = (K1 * K2) * δ / n := by ring
    rw [this, show 2 * (K1 * K2) * (δ / N) = (2 * (K1 * K2) * δ) / N by ring]
    rw [div_le_div_iff₀ hn hN]
    have : 0 ≤ K1 * K2 * δ := by positivity
    nlinarith
  calc 2 * Real.sqrt (K1 / n) * Real.sqrt (K2 * δ) = 2 * (Real.sqrt (K1 / n) * Real.sqrt (K2 * δ)) := by ring
    _ ≤ 2 * (Real.sqrt (2 * (K1 * K2)) * Real.sqrt (δ / N)) := by gcongr
    _ = _ := by ring

/-- **The cavity total variation** (`A:eq:cavity-TV`): `|π_N(A) - ν_n(A)| ≤ C √(δ_N/N)`. -/
theorem cavity_tv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) N (β / N) β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) A).toReal| ≤
        C * Real.sqrt (deltaN d s N / N) := by
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨C₁, hC₁, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  obtain ⟨Cd, hCd⟩ := insDefect_le hd hs0 hsd hβ hρ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  set K1 : ℝ := C₁ * Real.exp (β * B) with hK1
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  refine ⟨2 * Real.sqrt (2 * (K1 * K2)), by positivity, fun N hN A hA => ?_⟩
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
      exact var_fracIn_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := n + 1) hN x (t := 0) ⟨le_rfl, zero_le_one⟩ hA
    have hV1 : Var[fracIn (n := n) A; P0.tilted (Xx (periodicRiesz d s) lam x)] ≤ K1 / (n : ℝ) := by
      rw [e1]
      exact var_fracIn_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := n + 1) hN x (t := 1) ⟨zero_le_one, le_rfl⟩ hA
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

end TV


end MarginalAux

end HRS
