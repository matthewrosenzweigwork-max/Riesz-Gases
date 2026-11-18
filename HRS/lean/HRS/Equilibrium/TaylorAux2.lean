/-
# HRS.Equilibrium.TaylorAux2 — Young's inequality on the torus and tail-convolution moments
(Lemma 4.7, packet TAYLOR)

* `taylor_young`: for `a ≥ 0` measurable on `𝕋^d` and `p > 1`,
  `∫ (a * a)^p ≤ (∫ a^{2p/(p+1)})^{p+1}` (a special case of Young's convolution inequality,
  proved by a three-factor Hölder inequality).
* `taylor_tail_*`: the moments (`R:eq:tail-moments`, source line 4349) of
  `T_{H,x}(z) = ∫ g_+(x-y) (g_+-g_H)(y-z) dμ(y)`.  The `L^1` bound has the decay `H^{-1}`; for the
  higher moments only a uniform bound is needed in the chain of inequalities (the truncation of
  `T` at a level `M'` compensates; see `TaylorAux4`).
-/
import HRS.Equilibrium.PoleCavity

open MeasureTheory
open scoped ENNReal
open HRS.KernelAux HRS.KernelAux2

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.TaylorAux

variable {d : ℕ}

theorem taylor_rpow_split (x y : ℝ≥0∞) {p : ℝ} (hp : 1 < p) :
    x * y = ((x * y) ^ (2 * p / (p + 1))) ^ (1 / p) *
      ((x ^ (2 * p / (p + 1))) ^ ((p - 1) / (2 * p)) *
        (y ^ (2 * p / (p + 1))) ^ ((p - 1) / (2 * p))) := by
  have hp0 : 0 < p := by linarith
  set s : ℝ := 2 * p / (p + 1) with hs
  set c : ℝ := (p - 1) / (2 * p) with hc
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; apply div_nonneg <;> linarith
  have hsc : s * (1 / p + c) = 1 := by
    rw [hs, hc]; field_simp; ring
  have key : ∀ z : ℝ≥0∞, (z ^ s) ^ (1 / p) * (z ^ s) ^ c = z := by
    intro z
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hc0, ← ENNReal.rpow_mul, hsc,
      ENNReal.rpow_one]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hs0, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  calc x * y = ((x ^ s) ^ (1 / p) * (x ^ s) ^ c) * ((y ^ s) ^ (1 / p) * (y ^ s) ^ c) := by
        rw [key, key]
    _ = _ := by ring

/-- Young's inequality on the torus (Lebesgue measure) in the form needed for the tail moments. -/
theorem taylor_young (a : Torus d → ℝ≥0∞) (ha : Measurable a) {p : ℝ} (hp : 1 < p)
    (hA : ∫⁻ z, a z ^ (2 * p / (p + 1)) ≠ ∞) :
    ∫⁻ u, (∫⁻ w, a w * a (u - w)) ^ p ≤ (∫⁻ z, a z ^ (2 * p / (p + 1))) ^ (p + 1) := by
  have hp0 : 0 < p := by linarith
  set s : ℝ := 2 * p / (p + 1) with hs
  set c : ℝ := (p - 1) / (2 * p) with hc
  set A : ℝ≥0∞ := ∫⁻ z, a z ^ s with hAdef
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; apply div_nonneg <;> linarith
  have has : Measurable fun z => a z ^ s := ha.pow_const s
  have hshift : ∀ u, ∫⁻ w, a (u - w) ^ s = A := fun u =>
    KernelAux2.lintegral_sub_left_torus (fun z => a z ^ s) u
  -- the pointwise Hölder step
  have hpt : ∀ u, (∫⁻ w, a w * a (u - w)) ^ p ≤ (∫⁻ w, a w ^ s * a (u - w) ^ s) * A ^ (p - 1) := by
    intro u
    have hau : Measurable fun w => a (u - w) := ha.comp (measurable_const.sub measurable_id)
    have hg : Measurable fun w => (a w * a (u - w)) ^ s := (ha.mul hau).pow_const s
    have hH := ENNReal.lintegral_mul_prod_norm_pow_le (μ := (volume : Measure (Torus d)))
      (Finset.univ : Finset (Fin 2)) (g := fun w => (a w * a (u - w)) ^ s)
      (f := ![fun w => a w ^ s, fun w => a (u - w) ^ s]) hg.aemeasurable
      (by intro i _; fin_cases i <;> simp [has.aemeasurable, (hau.pow_const s).aemeasurable])
      (1 / p) (p := fun _ => c) (by simp [Fin.sum_univ_two]; rw [hc]; field_simp; ring)
      (by positivity) (fun _ _ => hc0)
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hH
    have hshift' : ∫⁻ w, a (u - w) ^ s = A := hshift u
    rw [hshift'] at hH
    have hJ : ∫⁻ w, a w * a (u - w) = ∫⁻ w, ((a w * a (u - w)) ^ s) ^ (1 / p) *
        ((a w ^ s) ^ c * (a (u - w) ^ s) ^ c) := lintegral_congr fun w => taylor_rpow_split _ _ hp
    rw [hJ]
    refine (ENNReal.rpow_le_rpow hH hp0.le).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have e1 : 1 / p * p = 1 := by field_simp
    have e2 : c * p = (p - 1) / 2 := by rw [hc]; field_simp
    rw [e1, ENNReal.rpow_one, e2, ← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith)]
    have : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by ring
    rw [this]
    simp only [mul_pow, ENNReal.mul_rpow_of_nonneg _ _ hs0]
    rfl
  have hAne : A ^ (p - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hA
  have hK : ∫⁻ u, ∫⁻ w, a w ^ s * a (u - w) ^ s = A * A := by
    rw [lintegral_lintegral_swap]
    · have : ∀ w, ∫⁻ u, a w ^ s * a (u - w) ^ s = a w ^ s * A := by
        intro w
        rw [lintegral_const_mul (f := fun u => a (u - w) ^ s) _
          (has.comp (measurable_id.sub measurable_const))]
        congr 1
        exact lintegral_sub_right_eq_self (fun z => a z ^ s) w
      simp_rw [this]
      rw [lintegral_mul_const _ has]
    · exact ((has.comp measurable_snd).mul (has.comp (measurable_fst.sub measurable_snd))).aemeasurable
  calc ∫⁻ u, (∫⁻ w, a w * a (u - w)) ^ p
      ≤ ∫⁻ u, (∫⁻ w, a w ^ s * a (u - w) ^ s) * A ^ (p - 1) := lintegral_mono hpt
    _ = (∫⁻ u, ∫⁻ w, a w ^ s * a (u - w) ^ s) * A ^ (p - 1) := by
        rw [lintegral_mul_const' _ _ hAne]
    _ = A ^ (p + 1) := by
        have h2 : A * A = A ^ (2 : ℝ) := by rw [ENNReal.rpow_two, sq]
        rw [hK, h2, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by linarith)]
        congr 1; ring

section Tail

variable {s : ℝ}

/-- `∫ (g_+)^σ < ∞` for `σ < 2` at the critical exponent. -/
theorem taylor_A_finite (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) {σ : ℝ} (hσ0 : 0 < σ) (hσ2 : σ < 2) :
    ∫⁻ z, (ENNReal.ofReal (gPlus d s c z)) ^ σ ≠ ∞ := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have hs0' : 0 < s := by rw [hcrit]; positivity
  obtain ⟨A0, hA01, hA0⟩ := PoleCavityAux.gPlus_envelope hd hs0' hsd c
  have hα : σ * (d : ℝ) / 2 < d := by nlinarith
  have hI : IntegrableOn (fun y : Fin d → ℝ => A0 ^ σ * ‖y‖ ^ (-(σ * (d : ℝ) / 2))) (Box d) :=
    (integrableOn_Box_rpow hd0 hα).const_mul _
  rw [lintegral_torus_box (fun z => (ENNReal.ofReal (gPlus d s c z)) ^ σ)]
  have hne : ∀ᵐ y ∂(volume.restrict (Box d)), y ≠ 0 := ae_restrict_of_ae (ae_ne_pi hd0)
  refine ne_of_lt (lt_of_le_of_lt ?_ (hI.lintegral_lt_top (f := fun y : Fin d → ℝ => A0 ^ σ * ‖y‖ ^ (-(σ * (d : ℝ) / 2)))))
  refine lintegral_mono_ae ?_
  filter_upwards [hne, ae_restrict_mem (measurableSet_Box d)] with y hy hyB
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hg0 : 0 ≤ gPlus d s c (boxPt y) := hc _
  have hgle := hA0 y hyB hy
  rw [ENNReal.ofReal_rpow_of_nonneg hg0 hσ0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hA0pos : 0 < A0 := by linarith
  calc gPlus d s c (boxPt y) ^ σ ≤ (A0 * ‖y‖ ^ (-s)) ^ σ := Real.rpow_le_rpow hg0 hgle hσ0.le
    _ = A0 ^ σ * ‖y‖ ^ (-(σ * (d : ℝ) / 2)) := by
        rw [Real.mul_rpow hA0pos.le (Real.rpow_nonneg hypos.le _), ← Real.rpow_mul hypos.le]
        congr 2
        rw [hcrit]; ring

end Tail

section TailMoments

variable {s : ℝ}

/-- The tail `g_+ - g_H` of the truncation. -/
def taylorG (d : ℕ) (s c H : ℝ) (w : Torus d) : ℝ := gPlus d s c w - gTrunc d s c H w

/-- The tail convolution `T_{H,x}`: `∫ φ(y) G(y - z) dμ(y)` as an extended nonnegative real
(`R:eq:tail-convolution`, source line 4343, with `φ = g_+(x - ·)` or `φ = 1`). -/
def taylorT (μ : Measure (Torus d)) (φ : Torus d → ℝ) (Gf : Torus d → ℝ) (z : Torus d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (φ y) * ENNReal.ofReal (Gf (y - z)) ∂μ

theorem taylorG_nonneg (c H : ℝ) (hH : 0 ≤ H) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (w : Torus d) : 0 ≤ taylorG d s c H w := by
  unfold taylorG gTrunc
  linarith [min_le_left (gPlus d s c w) H]

theorem taylorG_le (c H : ℝ) (hH : 0 ≤ H) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (w : Torus d) : taylorG d s c H w ≤ gPlus d s c w := by
  unfold taylorG gTrunc
  have h0 : 0 ≤ gPlus d s c w := hc w
  have : 0 ≤ min (gPlus d s c w) H := le_min h0 hH
  linarith

theorem taylorG_neg (c H : ℝ) (w : Torus d) : taylorG d s c H (-w) = taylorG d s c H w := by
  unfold taylorG gTrunc
  rw [PoleCavityAux.gPlus_neg]

theorem measurable_taylorG (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c H : ℝ) :
    Measurable (taylorG d s c H) := by
  have := PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)
  unfold taylorG gTrunc
  exact this.sub (this.min measurable_const)

/-- The `L^p` moment of the tail convolution is bounded uniformly (Young's inequality). -/
theorem taylor_T_pow (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, ∀ (x : Torus d) (Gf : Torus d → ℝ),
      (∀ w, ENNReal.ofReal (Gf w) ≤ ENNReal.ofReal (gPlus d s c w)) →
      ∫⁻ z, (taylorT (withDensityReal ρ) (fun y => gPlus d s c (x - y)) Gf z) ^ p
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hgm := PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)
  set a : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (gPlus d s c z) with ha
  have ham : Measurable a := ENNReal.measurable_ofReal.comp hgm
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hσ0 : 0 < 2 * (p : ℝ) / (p + 1) := by positivity
  have hσ2 : 2 * (p : ℝ) / (p + 1) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  set A : ℝ≥0∞ := ∫⁻ z, a z ^ (2 * (p : ℝ) / (p + 1)) with hA
  have hAfin : A ≠ ∞ := taylor_A_finite hd hcrit c hc hσ0 hσ2
  set B : ℝ≥0∞ := ENNReal.ofReal Λ ^ (p + 1) * A ^ ((p : ℝ) + 1) with hB
  have hBfin : B ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hAfin)
  refine ⟨B.toReal, fun x Gf hGf => ?_⟩
  set J : Torus d → ℝ≥0∞ := fun u => ∫⁻ w, a w * a (u - w) with hJ
  have hJm : Measurable J := by
    refine Measurable.lintegral_prod_right' (f := fun q : Torus d × Torus d => a q.2 * a (q.1 - q.2)) ?_
    exact (ham.comp measurable_snd).mul (ham.comp (measurable_fst.sub measurable_snd))
  have hJx : ∀ z, ∫⁻ y, a (x - y) * a (y - z) = J (x - z) := by
    intro z
    have := KernelAux2.lintegral_sub_left_torus (fun w => a w * a (x - z - w)) x
    simp only [hJ]
    rw [← this]
    refine lintegral_congr fun y => ?_
    show a (x - y) * a (y - z) = a (x - y) * a (x - z - (x - y))
    congr 2
    abel
  have hpt : ∀ z, taylorT (withDensityReal ρ) (fun y => gPlus d s c (x - y)) Gf z ≤
      ENNReal.ofReal Λ * J (x - z) := by
    intro z
    unfold taylorT
    calc ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) * ENNReal.ofReal (Gf (y - z)) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, a (x - y) * a (y - z) ∂(withDensityReal ρ) :=
          lintegral_mono fun y => mul_le_mul' le_rfl (hGf _)
      _ ≤ ENNReal.ofReal Λ * ∫⁻ y, a (x - y) * a (y - z) :=
          PoleCavityAux.lintegral_mu_le_vol hΛ (fun y => a (x - y) * a (y - z))
      _ = _ := by rw [hJx z]
  have hY := taylor_young a ham hpR (by simpa [hA] using hAfin)
  have hYp : ∫⁻ u, J u ^ p ≤ A ^ ((p : ℝ) + 1) := by
    refine le_of_eq_of_le ?_ hY
    refine lintegral_congr fun u => ?_
    simp only [hJ]
    rw [← ENNReal.rpow_natCast]
  calc ∫⁻ z, (taylorT (withDensityReal ρ) (fun y => gPlus d s c (x - y)) Gf z) ^ p ∂(withDensityReal ρ)
      ≤ ∫⁻ z, (ENNReal.ofReal Λ * J (x - z)) ^ p ∂(withDensityReal ρ) :=
        lintegral_mono fun z => pow_le_pow_left' (hpt z) p
    _ ≤ ENNReal.ofReal Λ * ∫⁻ z, (ENNReal.ofReal Λ * J (x - z)) ^ p :=
        PoleCavityAux.lintegral_mu_le_vol hΛ (fun z => (ENNReal.ofReal Λ * J (x - z)) ^ p)
    _ = ENNReal.ofReal Λ * (ENNReal.ofReal Λ ^ p * ∫⁻ z, J (x - z) ^ p) := by
        congr 1
        rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
        simp_rw [mul_pow]
    _ = ENNReal.ofReal Λ ^ (p + 1) * ∫⁻ u, J u ^ p := by
        rw [KernelAux2.lintegral_sub_left_torus (fun u => J u ^ p) x]; ring
    _ ≤ B := by
        rw [hB]; exact mul_le_mul' le_rfl hYp
    _ = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBfin).symm

end TailMoments

section TailBounds

variable {s : ℝ}

theorem taylor_lintegral_gPlus_lt_top (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∫⁻ z, ENNReal.ofReal (gPlus d s c z) ≠ ∞ := by
  have := taylor_A_finite hd hcrit c hc (σ := 1) one_pos one_lt_two
  simpa using this

/-- The interface for the tail convolutions: for `φ = 1` and `φ = g_+(x - ·)`, the mass of `φ`, the
`L^1` norm of the tail convolution (with decay `1/H`), and its `L^p` norm (uniform bound). -/
theorem taylor_tail_bounds (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
      ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
        ∫⁻ y, ENNReal.ofReal (φ y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal C ∧
        ∫⁻ z, taylorT (withDensityReal ρ) φ (taylorG d s c H) z ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C / H) ∧
        ∫⁻ z, (taylorT (withDensityReal ρ) φ (taylorG d s c H) z) ^ p ∂(withDensityReal ρ) ≤
          ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨C0, hC0⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc |>.imp fun _ h => h.1
  obtain ⟨C1, hC1⟩ := taylor_T_pow hd hcrit c hc ρ hρ p hp
  have hgm := PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)
  have hGm : ∀ H, Measurable (taylorG d s c H) := fun H => measurable_taylorG hd hs0 hsd c H
  set Im : ℝ≥0∞ := ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gPlus d s c z) with hIm
  have hImfin : Im ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (taylor_lintegral_gPlus_lt_top hd hcrit c hc)
  set C0' : ℝ := max C0 0 with hC0'def
  have hC0'0 : 0 ≤ C0' := le_max_right _ _
  have hC0le : C0 ≤ C0' := le_max_left _ _
  have hIm0 : 0 ≤ Im.toReal := ENNReal.toReal_nonneg
  have hpow0 : 0 ≤ C0' ^ p := pow_nonneg hC0'0 p
  set C : ℝ := 1 + C0' + |C1| + Im.toReal + C0' ^ p + C0' * Im.toReal with hCdef
  have hCC0 : C0' ≤ C := by nlinarith [abs_nonneg C1, mul_nonneg hC0'0 hIm0]
  have hCC1 : C1 ≤ C := by nlinarith [le_abs_self C1, mul_nonneg hC0'0 hIm0]
  have hCIm : Im.toReal ≤ C := by nlinarith [abs_nonneg C1, mul_nonneg hC0'0 hIm0]
  have hCone : 1 ≤ C := by nlinarith [abs_nonneg C1, mul_nonneg hC0'0 hIm0]
  have hCpow : C0' ^ p ≤ C := by nlinarith [abs_nonneg C1, mul_nonneg hC0'0 hIm0]
  have hCprod : C0' * Im.toReal ≤ C := by nlinarith [abs_nonneg C1]
  refine ⟨C, by linarith, fun H hH x φ hφ => ?_⟩
  have hH0 : 0 < H := by linarith
  have hGnn : ∀ w, ENNReal.ofReal (taylorG d s c H w) ≤ ENNReal.ofReal (gPlus d s c w) :=
    fun w => ENNReal.ofReal_le_ofReal (taylorG_le c H (by linarith) hc w)
  have hrow : ∀ y, ∫⁻ z, ENNReal.ofReal (taylorG d s c H (y - z)) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (C0' / H) := fun y =>
    (hC0 H hH y).2.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC0le hH0.le))
  -- general L^1 bound
  have hL1 : ∀ φ' : Torus d → ℝ, Measurable φ' →
      ∫⁻ z, taylorT (withDensityReal ρ) φ' (taylorG d s c H) z ∂(withDensityReal ρ) ≤
        (∫⁻ y, ENNReal.ofReal (φ' y) ∂(withDensityReal ρ)) * ENNReal.ofReal (C0' / H) := by
    intro φ' hφ'
    unfold taylorT
    rw [lintegral_lintegral_swap]
    · calc ∫⁻ y, ∫⁻ z, ENNReal.ofReal (φ' y) * ENNReal.ofReal (taylorG d s c H (y - z)) ∂(withDensityReal ρ) ∂(withDensityReal ρ)
          = ∫⁻ y, ENNReal.ofReal (φ' y) * ∫⁻ z, ENNReal.ofReal (taylorG d s c H (y - z)) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
            refine lintegral_congr fun y => ?_
            rw [lintegral_const_mul (f := fun z => ENNReal.ofReal (taylorG d s c H (y - z)))]
            exact ((hGm H).comp (measurable_const.sub measurable_id)).ennreal_ofReal
        _ ≤ ∫⁻ y, ENNReal.ofReal (φ' y) * ENNReal.ofReal (C0' / H) ∂(withDensityReal ρ) :=
            lintegral_mono fun y => mul_le_mul' le_rfl (hrow y)
        _ = _ := lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hφ')
    · refine Measurable.aemeasurable ?_
      exact ((hφ'.comp measurable_snd).ennreal_ofReal.mul
        (((hGm H).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal))
  have hdivC : C0' / H ≤ C / H := div_le_div_of_nonneg_right hCC0 hH0.le
  rcases hφ with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_one.symm.le.trans (ENNReal.ofReal_le_ofReal hCone)
    · refine (hL1 _ measurable_const).trans ?_
      simp only [ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one, one_mul]
      exact ENNReal.ofReal_le_ofReal hdivC
    · have hpt : ∀ z, taylorT (withDensityReal ρ) (fun _ => (1 : ℝ)) (taylorG d s c H) z ≤
          ENNReal.ofReal C0' := by
        intro z
        unfold taylorT
        simp only [ENNReal.ofReal_one, one_mul]
        calc ∫⁻ y, ENNReal.ofReal (taylorG d s c H (y - z)) ∂(withDensityReal ρ)
            = ∫⁻ y, ENNReal.ofReal (taylorG d s c H (z - y)) ∂(withDensityReal ρ) := by
              refine lintegral_congr fun y => ?_
              rw [← neg_sub, taylorG_neg]
          _ ≤ ENNReal.ofReal (C0' / H) := hrow z
          _ ≤ ENNReal.ofReal C0' := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [div_le_iff₀ hH0]
              nlinarith
      calc ∫⁻ z, (taylorT (withDensityReal ρ) (fun _ => (1 : ℝ)) (taylorG d s c H) z) ^ p ∂(withDensityReal ρ)
          ≤ ∫⁻ z, ENNReal.ofReal C0' ^ p ∂(withDensityReal ρ) :=
            lintegral_mono fun z => pow_le_pow_left' (hpt z) p
        _ = ENNReal.ofReal C0' ^ p := by simp
        _ = ENNReal.ofReal (C0' ^ p) := (ENNReal.ofReal_pow hC0'0 p).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hCpow
  · have hmass : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) ∂(withDensityReal ρ) ≤ Im :=
      KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (gPlus d s c z)) x
    have hIm' : Im ≤ ENNReal.ofReal C :=
      (ENNReal.ofReal_toReal hImfin).symm.le.trans (ENNReal.ofReal_le_ofReal hCIm)
    refine ⟨hmass.trans hIm', ?_, ?_⟩
    · refine (hL1 _ (hgm.comp (measurable_const.sub measurable_id))).trans ?_
      calc (∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y)) ∂(withDensityReal ρ)) * ENNReal.ofReal (C0' / H)
          ≤ ENNReal.ofReal Im.toReal * ENNReal.ofReal (C0' / H) := by
            gcongr
            exact hmass.trans (ENNReal.ofReal_toReal hImfin).symm.le
        _ = ENNReal.ofReal (Im.toReal * (C0' / H)) := (ENNReal.ofReal_mul hIm0).symm
        _ ≤ ENNReal.ofReal (C / H) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← mul_div_assoc]
            exact div_le_div_of_nonneg_right (by nlinarith) hH0.le
    · exact (hC1 x (taylorG d s c H) hGnn).trans (ENNReal.ofReal_le_ofReal hCC1)

end TailBounds

end HRS.TaylorAux
