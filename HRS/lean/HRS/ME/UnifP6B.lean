import HRS.ME.UnifP6A

/-!
# Uniform Lemma 4.7 (`integrated_taylor_remainder`), part B (packet P6): the Taylor-aux layer

Uniform forms (constants chosen before `β ∈ [βm, βp]` and before `ρ ∈ UFam d c₀ Λ`) of the `ρ`-dependent
`∃ C` lemmas of `HRS/Equilibrium/TaylorAux{2,3,6}.lean`: `taylor_T_pow`, `taylor_h_bound`,
`taylor_trunc_bounds`, `taylor_tail_bounds`, `taylor_field_moment`, `taylor_field_lower`.
The proofs are those of the originals; `exists_density_bound` is replaced by `Λ`, the constants of
`critical_integrals` by `critical_integrals_unif`, and `β` by `βp` in the explicit constants.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.TaylorAux
  HRS.KernelAux HRS.KernelAux2

variable {d : ℕ} {s : ℝ}

/-! ### `L^p` moment of the tail convolution -/

/-- Uniform `taylor_T_pow`: `C` depends on `d, s, c, Λ, p` only. -/
theorem taylor_T_pow_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) (hΛ0 : 0 ≤ Λ) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ (x : Torus d) (Gf : Torus d → ℝ),
      (∀ w, ENNReal.ofReal (Gf w) ≤ ENNReal.ofReal (gPlus d s c w)) →
      ∫⁻ z, (taylorT (withDensityReal ρ) (fun y => gPlus d s c (x - y)) Gf z) ^ p
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit

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
  refine ⟨B.toReal, fun ρ hF x Gf hGf => ?_⟩
  have hΛ := hF.up
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

/-- Uniform `taylor_h_bound`. -/
theorem taylor_h_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) (hΛ0 : 0 ≤ Λ) :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ y : Torus d,
      Integrable (fun a => gPlus d s c (y - a)) (withDensityReal ρ) ∧
      0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Ch := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have hgm := PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)
  set Im : ℝ≥0∞ := ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gPlus d s c z) with hIm
  have hImfin : Im ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (taylor_lintegral_gPlus_lt_top hd hcrit c hc)
  refine ⟨Im.toReal, ENNReal.toReal_nonneg, fun ρ hF y => ?_⟩
  have hΛ := hF.up
  have hm : Measurable fun a => gPlus d s c (y - a) := hgm.comp (measurable_const.sub measurable_id)
  have hle : ∫⁻ a, ENNReal.ofReal (gPlus d s c (y - a)) ∂(withDensityReal ρ) ≤ Im :=
    KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (gPlus d s c z)) y
  have hnn : 0 ≤ᵐ[withDensityReal ρ] fun a => gPlus d s c (y - a) :=
    Filter.Eventually.of_forall fun a => hc _
  refine ⟨?_, integral_nonneg fun a => hc _, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hnn).1
      (ne_top_of_le_ne_top hImfin hle)
  · exact taylor_real_integral_le (fun a => hc _) hm.aestronglyMeasurable ENNReal.toReal_nonneg
      (hle.trans (ENNReal.ofReal_toReal hImfin).symm.le)

/-- Uniform `taylor_trunc_bounds`. -/
theorem taylor_trunc_bounds_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ H : ℝ, 2 ≤ H → ∀ y : Torus d,
      ∫ a, taylorG d s c H (y - a) ∂(withDensityReal ρ) ≤ C2 / H ∧
      ∫ a, gTrunc d s c H (y - a) ^ 2 ∂(withDensityReal ρ) ≤ C2 * Real.log H := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨C0, hmain, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ
  refine ⟨max C0 0, le_max_right _ _, fun ρ hF H hH y => ?_⟩
  have hC0 := (hmain ρ hF.smooth hF.up).1
  refine ⟨?_, ?_⟩
  · have hH0 : 0 < H := by linarith
    refine taylor_real_integral_le (fun a => taylorG_nonneg c H (by linarith) hc _)
      ((measurable_taylorG hd hs0 hsd c H).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (div_nonneg (le_max_right _ _) hH0.le) ?_
    refine (hC0 H hH y).2.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (le_max_left _ _) hH0.le
  · have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    have hm : Measurable fun a => gTrunc d s c H (y - a) ^ 2 :=
      ((taylor_measurable_gTrunc hd hcrit c H).comp (measurable_const.sub measurable_id)).pow_const 2
    refine taylor_real_integral_le (fun a => sq_nonneg _) hm.aestronglyMeasurable
      (mul_nonneg (le_max_right _ _) hlog) ?_
    refine (hC0 H hH y).1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog

/-- Uniform `taylor_tail_bounds`: `C` depends on `d, s, c, Λ, p` only. -/
theorem taylor_tail_bounds_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) (hΛ1 : 1 ≤ Λ) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ H : ℝ, 2 ≤ H → ∀ x : Torus d,
      ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
        ∫⁻ y, ENNReal.ofReal (φ y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal C ∧
        ∫⁻ z, taylorT (withDensityReal ρ) φ (taylorG d s c H) z ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C / H) ∧
        ∫⁻ z, (taylorT (withDensityReal ρ) φ (taylorG d s c H) z) ^ p ∂(withDensityReal ρ) ≤
          ENNReal.ofReal C := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨C0, hmain, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ1
  obtain ⟨C1, hC1all⟩ := taylor_T_pow_unif hd hcrit c hc c₀ Λ hΛ0 p hp
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
  refine ⟨C, by linarith, fun ρ hF H hH x φ hφ => ?_⟩
  have hρ := hF.smooth
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hΛ := hF.up
  have hC0 := (hmain ρ hρ hΛ).1
  have hC1 := hC1all ρ hF
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

set_option maxHeartbeats 1600000 in
/-- Uniform `taylor_field_moment` (`R:eq:truncated-v-moment`). -/
theorem taylor_field_moment_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ H : ℝ, 2 ≤ H → ∀ i : Fin (N - 1), ∀ y : Torus d,
      ∫ Y, (taylorFieldH d s c β ρ N i H Y y) ^ (4 * q)
          ∂(Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) ≤
        C * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) ^ (2 * q) := by
  obtain ⟨Ch, hCh0, hCh_all⟩ := taylor_h_bound_unif hd hcrit c hc c₀ Λ (by linarith)
  obtain ⟨C2, hC20, hC2_all⟩ := taylor_trunc_bounds_unif hd hcrit c hc c₀ Λ hΛ
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  set c1' : ℝ := βp ^ 2 * (C2 + 1) with hc1'
  set c2' : ℝ := 8 * βp ^ 2 * (C2 ^ 2 + Ch ^ 2) with hc2'
  refine ⟨2 ^ (4 * q - 1) * (taylor_kb (2 * q) * c1' ^ (2 * q) + c2' ^ (2 * q)), by
    have := taylor_kb_one_le (2 * q); positivity, fun β hβI ρ hF N hN H hH i y => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hCh := hCh_all ρ hF
  have hC2 := hC2_all ρ hF
  set c1 : ℝ := β ^ 2 * (C2 + 1) with hc1
  set c2 : ℝ := 8 * β ^ 2 * (C2 ^ 2 + Ch ^ 2) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hPm
  set J : Finset (Fin (N - 1)) := Finset.univ.erase i with hJ
  have hJcard : (J.card : ℝ) = N - 2 := by
    rw [hJ, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have : 2 ≤ N := hN
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hJle : (J.card : ℝ) ≤ N := by rw [hJcard]; linarith
  have hJ0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
  -- the centered summand
  set mH : ℝ := ∫ a, gTrunc d s c H (y - a) ∂μ with hmH
  set f : Torus d → ℝ := fun a => gTrunc d s c H (y - a) - mH with hf
  have hgm : Measurable fun a => gTrunc d s c H (y - a) :=
    (taylor_measurable_gTrunc hd hcrit c H).comp (measurable_const.sub measurable_id)
  have hg0 : ∀ a, 0 ≤ gTrunc d s c H (y - a) := fun a => le_min (hc _) (by linarith)
  have hgH : ∀ a, gTrunc d s c H (y - a) ≤ H := fun a => min_le_right _ _
  have hgint : Integrable (fun a => gTrunc d s c H (y - a)) μ :=
    taylor_integrable_of_bdd hgm (B := H) fun a => by rw [abs_of_nonneg (hg0 a)]; exact hgH a
  have hmH0 : 0 ≤ mH := integral_nonneg hg0
  have hmHH : mH ≤ H := by
    calc mH ≤ ∫ a, H ∂μ := integral_mono hgint (integrable_const _) hgH
      _ = H := by simp
  have hfm : Measurable f := hgm.sub_const _
  have hfb : ∀ a, |f a| ≤ H := fun a => by
    rw [abs_le]; constructor <;> simp only [hf] <;> linarith [hg0 a, hgH a]
  have hf0 : ∫ a, f a ∂μ = 0 := by
    simp only [hf]
    rw [integral_sub hgint (integrable_const _)]; simp [hmH]
  have hfv : ∫ a, f a ^ 2 ∂μ ≤ C2 * Real.log H := by
    have h1 : ∫ a, f a ^ 2 ∂μ = ∫ a, gTrunc d s c H (y - a) ^ 2 ∂μ - mH ^ 2 := by
      have e : ∀ a, f a ^ 2 = gTrunc d s c H (y - a) ^ 2 - 2 * mH * gTrunc d s c H (y - a) + mH ^ 2 :=
        fun a => by simp only [hf]; ring
      have hsq : Integrable (fun a => gTrunc d s c H (y - a) ^ 2) μ :=
        taylor_integrable_of_bdd (hgm.pow_const 2) (B := H ^ 2) fun a => by
          rw [abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (hg0 a) (hgH a) 2
      have hlin : Integrable (fun a => 2 * mH * gTrunc d s c H (y - a)) μ := hgint.const_mul _
      have hsub : Integrable (fun a => gTrunc d s c H (y - a) ^ 2 -
          2 * mH * gTrunc d s c H (y - a)) μ := hsq.sub hlin
      simp_rw [e]
      rw [integral_add hsub (integrable_const _), integral_sub hsq hlin, integral_const_mul]
      simp [hmH]; ring
    rw [h1]
    exact (sub_le_self _ (sq_nonneg _)).trans (hC2 H hH y).2
  -- Bernstein
  have hbern := taylor_bernstein_pi μ (N - 1) f hfm (M := H) (σ2 := C2 * Real.log H) hH0
    (mul_nonneg hC20 hlog) hfb hf0 hfv (2 * q) J
  -- the field
  set S : Config d (N - 1) → ℝ := fun Y => ∑ j ∈ J, f (Y j) with hS
  set lam : ℝ := β / N with hlam
  set hy : ℝ := convMeasure (gPlus d s c) μ y with hhy
  set e : ℝ := lam * J.card * mH - β * hy with he
  have hfield : ∀ Y, taylorFieldH d s c β ρ N i H Y y = lam * S Y + e := by
    intro Y
    simp only [taylorFieldH, hS, hf, he]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← hJ]
    ring
  -- the deterministic part `e`
  have hhy_int : Integrable (fun a => gPlus d s c (y - a)) μ := (hCh y).1
  have hdH : hy - mH = ∫ a, taylorG d s c H (y - a) ∂μ := by
    simp only [hhy, hmH, convMeasure, taylorG]
    rw [integral_sub hhy_int hgint]
  have hdH0 : 0 ≤ hy - mH := by
    rw [hdH]; exact integral_nonneg fun a => taylorG_nonneg c H (by linarith) hc _
  have hdH1 : hy - mH ≤ C2 / H := by rw [hdH]; exact (hC2 H hH y).1
  have hhyCh : hy ≤ Ch := (hCh y).2.2
  have he_eq : e = -(β * (hy - mH)) - (2 * β / N) * mH := by
    simp only [he, hlam]
    have : (J.card : ℝ) = N - 2 := hJcard
    rw [this]; field_simp; ring
  have hebound : e ^ 2 ≤ c2 * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2) := by
    have h1 : |e| ≤ β * (C2 / H) + 2 * β / N * Ch := by
      rw [he_eq, abs_le]; constructor
      · have : β * (hy - mH) ≤ β * (C2 / H) := mul_le_mul_of_nonneg_left hdH1 hβ.le
        have : 2 * β / N * mH ≤ 2 * β / N * Ch :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have : 0 ≤ 2 * β / N * mH := by positivity
        have : 0 ≤ β * (hy - mH) := mul_nonneg hβ.le hdH0
        linarith
      · have : 0 ≤ β * (hy - mH) := mul_nonneg hβ.le hdH0
        have : 0 ≤ 2 * β / N * mH := by positivity
        have : 0 ≤ β * (C2 / H) := by positivity
        have : 0 ≤ 2 * β / N * Ch := by positivity
        linarith
    have h2 : e ^ 2 ≤ (β * (C2 / H) + 2 * β / N * Ch) ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    have h3 : (β * (C2 / H) + 2 * β / N * Ch) ^ 2 ≤ 2 * (β * (C2 / H)) ^ 2 + 2 * (2 * β / N * Ch) ^ 2 := by
      nlinarith [sq_nonneg (β * (C2 / H) - 2 * β / N * Ch)]
    refine h3.trans ?_
    have e1 : 2 * (β * (C2 / H)) ^ 2 = 2 * β ^ 2 * C2 ^ 2 * (1 / H ^ 2) := by field_simp
    have e2 : 2 * (2 * β / N * Ch) ^ 2 = 8 * β ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2) := by field_simp; ring
    rw [e1, e2, hc2]
    have a1 : 0 ≤ 1 / H ^ 2 := by positivity
    have a2 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    have b1 : 0 ≤ β ^ 2 * C2 ^ 2 := by positivity
    have b2 : 0 ≤ β ^ 2 * Ch ^ 2 := by positivity
    have key : 8 * β ^ 2 * (C2 ^ 2 + Ch ^ 2) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2) -
        (2 * β ^ 2 * C2 ^ 2 * (1 / H ^ 2) + 8 * β ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2)) =
        6 * (β ^ 2 * C2 ^ 2) * (1 / H ^ 2) + 8 * (β ^ 2 * C2 ^ 2) * (1 / (N : ℝ) ^ 2) +
          8 * (β ^ 2 * Ch ^ 2) * (1 / H ^ 2) := by ring
    have hk0 : 0 ≤ 6 * (β ^ 2 * C2 ^ 2) * (1 / H ^ 2) + 8 * (β ^ 2 * C2 ^ 2) * (1 / (N : ℝ) ^ 2) +
          8 * (β ^ 2 * Ch ^ 2) * (1 / H ^ 2) := by positivity
    linarith
  -- the random part
  have hlam2 : lam ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2) ≤
      c1 * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) := by
    have hl2 : lam ^ 2 = β ^ 2 / (N : ℝ) ^ 2 := by rw [hlam]; ring
    rw [hl2]
    have hCl : 0 ≤ C2 * Real.log H := mul_nonneg hC20 hlog
    have h1 : β ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H)) ≤
        β ^ 2 / (N : ℝ) ^ 2 * (N * (C2 * Real.log H)) := by gcongr
    have h2 : β ^ 2 / (N : ℝ) ^ 2 * (N * (C2 * Real.log H)) + β ^ 2 / (N : ℝ) ^ 2 * H ^ 2 =
        β ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by field_simp
    have a1 : 0 ≤ Real.log H / N := by positivity
    have a2 : 0 ≤ H ^ 2 / (N : ℝ) ^ 2 := by positivity
    have a3 : 0 ≤ 1 / H ^ 2 := by positivity
    have a4 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    calc β ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2)
        = β ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H)) + β ^ 2 / (N : ℝ) ^ 2 * H ^ 2 := by ring
      _ ≤ β ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by linarith
      _ ≤ _ := by
        rw [hc1]
        have key : β ^ 2 * (C2 + 1) * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) -
            β ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) =
            β ^ 2 * (Real.log H / N + C2 * (H ^ 2 / (N : ℝ) ^ 2) +
              (C2 + 1) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by ring
        have hk0 : 0 ≤ β ^ 2 * (Real.log H / N + C2 * (H ^ 2 / (N : ℝ) ^ 2) +
              (C2 + 1) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by positivity
        linarith
  -- assemble
  set Θ : ℝ := Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2 with hΘ
  have hΘ0 : 0 ≤ Θ := by positivity
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)
  have hSb : ∀ Y, |S Y| ≤ J.card * H := fun Y => by
    simp only [hS]
    calc |∑ j ∈ J, f (Y j)| ≤ ∑ j ∈ J, |f (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ J, H := Finset.sum_le_sum fun j _ => hfb _
      _ = _ := by simp
  have hSint : Integrable (fun Y => S Y ^ (4 * q)) Pm :=
    taylor_integrable_of_bdd (hSm.pow_const _) (B := (J.card * H) ^ (4 * q)) fun Y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb Y) _
  have hev : Even (4 * q) := ⟨2 * q, by ring⟩
  have hvm : Measurable fun Y : Config d (N - 1) => (taylorFieldH d s c β ρ N i H Y y) := by
    simp_rw [hfield]
    exact (hSm.const_mul _).add_const _
  have hRHS : Integrable (fun Y => 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q))) Pm := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_const _)) _
    simp_rw [mul_pow]
    exact hSint.const_mul _
  have hS4 : ∫ Y, S Y ^ (4 * q) ∂Pm ≤ taylor_kb (2 * q) * (J.card * (C2 * Real.log H) + H ^ 2) ^ (2 * q) := by
    have : 4 * q = 2 * (2 * q) := by ring
    rw [this]; exact hbern
  have he4 : e ^ (4 * q) ≤ (c2 * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) ^ (2 * q) := by
    have : e ^ (4 * q) = (e ^ 2) ^ (2 * q) := by rw [← pow_mul]; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (sq_nonneg _) hebound _
  have hstep1 : ∫ Y, (taylorFieldH d s c β ρ N i H Y y) ^ (4 * q) ∂Pm ≤
      ∫ Y, 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q)) ∂Pm := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun Y => hev.pow_nonneg _) hRHS
      (Filter.Eventually.of_forall fun Y => ?_)
    simp only [hfield]
    exact taylor_pow_sum _ _ q hq
  have hstep2 : ∫ Y, 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q)) ∂Pm =
      2 ^ (4 * q - 1) * (lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm + e ^ (4 * q)) := by
    rw [integral_const_mul]
    congr 1
    simp_rw [mul_pow]
    rw [integral_add (hSint.const_mul _) (integrable_const _), integral_const_mul]
    simp
  have hk := taylor_kb_one_le (2 * q)
  have hlamq : lam ^ (4 * q) * (taylor_kb (2 * q) * (J.card * (C2 * Real.log H) + H ^ 2) ^ (2 * q)) =
      taylor_kb (2 * q) * (lam ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2)) ^ (2 * q) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  have hstep3 : 2 ^ (4 * q - 1) * (lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm + e ^ (4 * q)) ≤
      2 ^ (4 * q - 1) * (taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) + (c2 * Θ) ^ (2 * q)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlam4 : 0 ≤ lam ^ (4 * q) := by positivity
    have h1 : lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm ≤ taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) := by
      refine (mul_le_mul_of_nonneg_left hS4 hlam4).trans ?_
      rw [hlamq]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlam2 _) (by linarith)
    have h2 : e ^ (4 * q) ≤ (c2 * Θ) ^ (2 * q) := by
      refine he4.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      refine mul_le_mul_of_nonneg_left ?_ hc20
      have : 0 ≤ Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 := by positivity
      rw [hΘ]; linarith
    linarith
  refine hstep1.trans (hstep2.le.trans (hstep3.trans ?_))
  have hb2 : β ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ.le hβI.2 2
  have hc1le : c1 ≤ c1' := mul_le_mul_of_nonneg_right hb2 (by linarith)
  have hc2le : c2 ≤ c2' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 (by norm_num)) (by positivity)
  have hΘ0' : 0 ≤ Θ := by rw [hΘ]; positivity
  have hk := taylor_kb_one_le (2 * q)
  calc 2 ^ (4 * q - 1) * (taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) + (c2 * Θ) ^ (2 * q))
      ≤ 2 ^ (4 * q - 1) * (taylor_kb (2 * q) * (c1' * Θ) ^ (2 * q) + (c2' * Θ) ^ (2 * q)) := by
        gcongr
    _ = _ := by
        rw [mul_pow, mul_pow]
        ring

end HRS.ME.Unif

end
