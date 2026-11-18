import HRS.Equilibrium.PoleCavity
import HRS.Kernel.Riesz

/-!
# Packet PU1a, part A (uniform Riesz and pole-cavity envelope constants)

Uniform copies (namespace `HRS.ME.NfU`) of the following lemmas (see `docs/MAIN_E_NF_PLAN.md`, rule for uniform
statements). In each copy the constant is chosen before `ρ`, and the density enters only through a fixed bound
`ρ ≤ Λ` with `1 ≤ Λ` (in place of the `ρ`-dependent `exists_density_bound`).

* `convMeasure_bounded'_unif` of `HRS.KernelAux2.convMeasure_bounded'` (Riesz.lean l.3793). The constant
  `(ofReal Λ * ∫⁻ ‖g‖).toReal` already depended on `Λ` only; only the order of quantifiers changes.
* `convMeasure_bounded_unif` of `HRS.convMeasure_bounded` (Riesz.lean l.3917). Keeps `IsProbDensity ρ`.
* `kerData_periodicRiesz_unif` of `HRS.PoleCavityAux.kerData_periodicRiesz` (PoleCavity.lean l.934).
* `conj_trunc_unif` of `HRS.PoleCavityAux.conj_trunc` (PoleCavity.lean l.1844).
* `conj_pow_unif` of `HRS.PoleCavityAux.conj_pow` (PoleCavity.lean l.1876).
* `conj_expo_unif` of `HRS.PoleCavityAux.conj_expo` (PoleCavity.lean l.1921).

None of these involves `β`, so there is no range `β ∈ Icc βm βp`. The density hypothesis of each original
(`SmoothPosDensity ρ`, or `IsProbDensity ρ` for `convMeasure_bounded`) is kept, and `ρ ≤ Λ` is added.
`abs_log_le_of_mem` is a helper bounding `|log x|` on `[a, b]`, used by the later packets.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.NfU

open HRS HRS.PoleCavityAux HRS.KernelAux HRS.KernelAux2

variable {d : ℕ} {s : ℝ}

/-- `|log x|` on `[a, b]` with `0 < a` is bounded by `|log a| + |log b|`. -/
theorem abs_log_le_of_mem {a b x : ℝ} (ha : 0 < a) (hx : a ≤ x) (hx' : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have h1 : Real.log a ≤ Real.log x := Real.log_le_log ha hx
  have h2 : Real.log x ≤ Real.log b := Real.log_le_log hx0 hx'
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

/-- Uniform `convMeasure_bounded'`: the constant `(ofReal Λ * ∫⁻ ‖g‖).toReal` does not depend on `ρ`. -/
theorem convMeasure_bounded'_unif (g : Torus d → ℝ) (hg : Integrable g) (Λ : ℝ) :
    ∃ C, ∀ ρ : Torus d → ℝ, (∀ x, ρ x ≤ Λ) → ∀ x, |convMeasure g (withDensityReal ρ) x| ≤ C := by
  refine ⟨(ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal ‖g y‖).toReal, fun ρ hΛ x => ?_⟩
  have h1 := norm_integral_le_lintegral_norm (μ := withDensityReal ρ) (fun y => g (x - y))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_mono ?_ (lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal ‖g z‖) x))
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  have := hg.hasFiniteIntegral
  unfold HasFiniteIntegral at this
  simp only [← ofReal_norm] at this
  exact this.ne

/-- Uniform `convMeasure_bounded`: for `IsProbDensity ρ` with `ρ ≤ Λ`, the convolution of the periodic
Riesz kernel with `ρ` is bounded by a constant depending on `Λ` only. -/
theorem convMeasure_bounded_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ x, |convMeasure (periodicRiesz d s) (withDensityReal ρ) x| ≤ C := by
  obtain ⟨C, hC⟩ := convMeasure_bounded'_unif (periodicRiesz d s)
    (KernelAux.integrable_periodicRiesz hd hs0 hsd) Λ
  exact ⟨C, fun ρ _ hΛ => hC ρ hΛ⟩

/-- Uniform `kerData_periodicRiesz`: the constants `B, Cc` do not depend on `ρ` (only on `Λ`). -/
theorem kerData_periodicRiesz_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ B Cc : ℝ, 0 ≤ B ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      KerData (periodicRiesz d s) (withDensityReal ρ) B Cc := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  obtain ⟨Cc, hC⟩ := convMeasure_bounded_unif hd hs0 hsd Λ
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hgi := KernelAux.integrable_periodicRiesz hd hs0 hsd
  refine ⟨max B 0, |Cc|, le_max_right _ _, fun ρ hρ hΛ => ?_⟩
  have hμ := isProbabilityMeasure_mu hρ
  have hCc : ∀ x, |convMeasure (periodicRiesz d s) (withDensityReal ρ) x| ≤ |Cc| :=
    fun x => (hC ρ hρ.density hΛ x).trans (le_abs_self _)
  set g := periodicRiesz d s with hg
  have hint : ∀ x, Integrable (fun y => g (x - y)) (withDensityReal ρ) := by
    intro x
    refine ⟨(hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖g z‖ₑ) x) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact hgi.hasFiniteIntegral
  have hint2 : Integrable (fun q : Torus d × Torus d => g (q.1 - q.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
    have hm : AEStronglyMeasurable (fun q : Torus d × Torus d => g (q.1 - q.2))
        ((withDensityReal ρ).prod (withDensityReal ρ)) :=
      (hgm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall hint, ?_⟩
    have hmeas : Measurable fun x => ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) := by
      have : StronglyMeasurable (Function.uncurry fun x y : Torus d => ‖g (x - y)‖) :=
        (hgm.comp (measurable_fst.sub measurable_snd)).norm.stronglyMeasurable
      exact (this.integral_prod_right' (ν := withDensityReal ρ)).measurable
    refine Integrable.of_bound hmeas.aestronglyMeasurable (|Cc| + 2 * max B 0)
      (Filter.Eventually.of_forall fun x => ?_)
    have h1 : ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) ≤
        ∫ y, (g (x - y) + 2 * max B 0) ∂(withDensityReal ρ) := by
      refine integral_mono (hint x).norm ((hint x).add (integrable_const _)) fun y => ?_
      have := hB' (x - y)
      have h0 := le_max_right B 0
      simp only [Real.norm_eq_abs]
      rcases le_total 0 (g (x - y)) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    rw [integral_add (hint x) (integrable_const _)] at h1
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
    have h2 : ∫ y, g (x - y) ∂(withDensityReal ρ) = convMeasure g (withDensityReal ρ) x := rfl
    have h3 := hCc x
    have h4 : 0 ≤ ∫ y, ‖g (x - y)‖ ∂(withDensityReal ρ) := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h4]
    have := le_abs_self (convMeasure g (withDensityReal ρ) x)
    linarith
  exact ⟨hgm, fun z => periodicRiesz_neg z, hB', hint, hint2, hCc⟩

/-- Uniform `conj_trunc`: the constant `C` depends on `Λ` (and `d, s, c`), not on `ρ`. -/
theorem conj_trunc_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.log H) ∧
        ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) - gTrunc d s c H (x - y))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C / H) := by
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨C1, hC1, h1⟩ := vol_sq_trunc hd hcrit c hc
  obtain ⟨C2, hC2, h2⟩ := vol_excess hd hcrit c hc
  refine ⟨Λ * max C1 C2, by positivity, fun ρ _ hΛρ H hH x => ⟨?_, ?_⟩⟩
  · calc _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gTrunc d s c H z ^ 2) :=
          lintegral_conv_le ρ Λ hΛρ (fun z => ENNReal.ofReal (gTrunc d s c H z ^ 2)) x
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (C1 * Real.log H) := by gcongr; exact h1 H hH
      _ = ENNReal.ofReal (Λ * (C1 * Real.log H)) := (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
        have := le_max_left C1 C2
        nlinarith [mul_nonneg hΛ0.le hlog]
  · have hH0 : 0 < H := by linarith
    calc _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gPlus d s c z - gTrunc d s c H z) :=
          lintegral_conv_le ρ Λ hΛρ (fun z => ENNReal.ofReal (gPlus d s c z - gTrunc d s c H z)) x
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (C2 / H) := by gcongr; exact h2 H hH0
      _ = ENNReal.ofReal (Λ * (C2 / H)) := (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := le_max_right C1 C2
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this hH0.le) hΛ0.le

/-- Uniform `conj_pow`: the constant `Λ * C1` depends on `Λ` (and `d, s, c, v`), not on `ρ`. -/
theorem conj_pow_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (v : ℝ) (hv : 2 < v) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ v) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * H ^ (v - 2)) := by
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨C1, hC1, h1⟩ := vol_pow_trunc hd hcrit c hc v hv
  refine ⟨Λ * C1, by positivity, fun ρ _ hΛρ H hH x => ?_⟩
  calc _ ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gTrunc d s c H z ^ v) :=
        lintegral_conv_le ρ Λ hΛρ (fun z => ENNReal.ofReal (gTrunc d s c H z ^ v)) x
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (C1 * H ^ (v - 2)) := by
        gcongr; exact h1 H (by linarith)
    _ = ENNReal.ofReal (Λ * (C1 * H ^ (v - 2))) := (ENNReal.ofReal_mul hΛ0.le).symm
    _ = _ := by congr 1; ring

/-- Uniform `conj_expo`: the constant `max (4 * C1) 16` depends on `Λ` (and `d, s, c`), not on `ρ`. -/
theorem conj_expo_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (1 + |Real.log u|)) := by
  obtain ⟨C1, hC1, h1⟩ := conj_trunc_unif hd hcrit c hc Λ hΛ
  refine ⟨max (4 * C1) 16, by positivity, fun ρ hρ hΛρ u hu hu1 x => ?_⟩
  have := isProbabilityMeasure_mu hρ
  set H : ℝ := 1 / u with hH
  have hH1 : 1 ≤ H := by rw [hH, le_div_iff₀ hu]; linarith
  have hpt : ∀ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) := by
    intro y
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := sq_exp_le (gPlus d s c (x - y)) u (hc _) hu
    exact this
  have hlog : |Real.log u| = Real.log H := by
    rw [hH, one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hu.le hu1)]
  calc _ ≤ ∫⁻ y, ENNReal.ofReal 4 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal 4 * ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ∂(withDensityReal ρ) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max (4 * C1) 16 * (1 + |Real.log u|)) := by
        rcases le_or_gt 2 H with h2 | h2
        · have := (h1 ρ hρ hΛρ H h2 x).1
          calc _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (C1 * Real.log H) := by gcongr
            _ = ENNReal.ofReal (4 * (C1 * Real.log H)) := (ENNReal.ofReal_mul (by norm_num)).symm
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hl : 0 ≤ Real.log H := Real.log_nonneg hH1
              rw [hlog]
              have := le_max_left (4 * C1) 16
              have := le_max_right (4 * C1) 16
              nlinarith [abs_nonneg (Real.log u)]
        · have hb : ∀ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ 2) ≤ ENNReal.ofReal 4 := by
            intro y
            refine ENNReal.ofReal_le_ofReal ?_
            have h0 : 0 ≤ gTrunc d s c H (x - y) := le_min (hc _) (by linarith)
            have : gTrunc d s c H (x - y) ≤ 2 := (min_le_right _ _).trans h2.le
            nlinarith
          calc _ ≤ ENNReal.ofReal 4 * ∫⁻ y, ENNReal.ofReal 4 ∂(withDensityReal ρ) :=
                mul_le_mul' le_rfl (lintegral_mono hb)
            _ = ENNReal.ofReal 4 * ENNReal.ofReal 4 := by simp
            _ = ENNReal.ofReal 16 := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              have := le_max_right (4 * C1) 16
              nlinarith [abs_nonneg (Real.log u)]

end HRS.ME.NfU
