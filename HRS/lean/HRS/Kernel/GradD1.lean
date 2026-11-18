import HRS.Kernel.D1
import HRS.Kernel.GradConv

/-!
# The force convolution in dimension one

The `d = 1` versions of the theorems of `HRS/Kernel/GradConv.lean`.  Each of the six theorems
at the end of this file has exactly the statement of the theorem of the same name in
`HRS.KernelGrad` (`GradConv.lean`), except that the hypothesis `(hd : 2 ≤ d)` is replaced by
`(hd : d = 1)`.  `convGradConv_eq_plain` has no `d = 1` counterpart: its range
`0 ≤ s < d - 1` is empty when `d = 1`.

## Proof route

In `HRS/Kernel/Grad*.lean` the hypothesis `2 ≤ d` enters at exactly three places:

* the gradient bound `periodicRiesz_grad_bound` (used by `periodicRieszGrad_bound_tdist_aux`);
* the sign `0 ≤ subA d s` of the subordination constant (used by `heat_comp_bound`);
* the smoothness of `∇g` off the origin (`periodicRieszGrad_smoothOffZero'`).

Everything else only uses `0 < d` (the field `GoodKernel.pos`).  `HRS/Kernel/D1.lean` proves the
first two facts for `1 ≤ d` (`KernelD1Aux.grad_bound_d1`, `KernelD1Aux.subA_nonneg_d1`) and the
third for `d = 1` (`periodicRieszGrad_smoothOffZero_d1`).  The section below therefore repeats
the `d ≥ 2` chain of `GradBasic`, `GradFourier`, `GradReg` and `GradPairing` verbatim under
`1 ≤ d`, with those two inputs substituted; every lemma keeps its original name with the suffix
`_of_one_le`.  The final theorems specialise to `d = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.KernelGradD1

open HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

/-! ### The `d ≥ 2` chain of `Grad*.lean`, repeated under `1 ≤ d` -/

theorem periodicRieszGrad_bound_tdist_aux_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1) := by
  obtain ⟨C, hC⟩ := HRS.KernelD1Aux.grad_bound_d1 hd hs0 hsd
  refine ⟨C, fun z hz => ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_mk_box z
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hz
    funext i; simp [Torus.mk]
  rw [tdist_mk hy]
  exact hC y hy0 hy

open scoped Real in
theorem heat_comp_bound_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ ε : ℝ, 0 < ε → ∀ y : Euc d, (∀ i, |y i| ≤ 1 / 2) → y ≠ 0 →
      |heatRieszGrad d s ε (Torus.mk y) j| ≤ C1 * ‖y‖ ^ (-s - 1) + C2 := by
  obtain ⟨K, hK0, hK⟩ := HRS.KernelAux.psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := HRS.KernelAux.psiG_large_bound (d := d) j
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set n : ℝ := (d:ℝ) / 2 + 1 with hn_def
  have hn : 0 < n := by rw [hn_def]; positivity
  have han : a < n := by rw [ha_def, hn_def]; linarith
  set c : ℝ := n ^ n * Real.exp (-n) with hc_def
  have hc0 : 0 ≤ c := by positivity
  set P : ℝ := 2 * π ^ 2 * Real.sqrt π ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set A := HRS.KernelAux.subA d s with hA
  have hA0 : 0 ≤ A := HRS.KernelD1Aux.subA_nonneg_d1 hd hs0 hsd
  set C0 : ℝ := ∫ v in Ioi (0:ℝ), v ^ (a - 1) * min c (v ^ (-n)) with hC0
  have hC00 : 0 ≤ C0 := by
    refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
    have hv0 : (0:ℝ) < v := hv
    have := le_min hc0 (Real.rpow_nonneg hv0.le (-n))
    have := Real.rpow_pos_of_pos hv0 (a - 1)
    positivity
  set θ2 : ℝ := π ^ 2 / 8 with hθ2
  have hθ2p : 0 < θ2 := by positivity
  refine ⟨A * (P * C0 * π ^ (-(s + 2))), A * (P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a),
    by positivity, by have := (Real.Gamma_pos_of_pos ha).le; positivity,
    fun ε hε y hy hy0 => ?_⟩
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set θ1 : ℝ := π ^ 2 * ‖y‖ ^ 2 with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set m1 : ℝ → ℝ := fun u => min (c * θ1 ^ (-n)) (u ^ (-n)) with hm1
  set m2 : ℝ → ℝ := fun u => min (c * θ2 ^ (-n)) (u ^ (-n)) with hm2
  set Bm : ℝ → ℝ := fun t => P * ‖y‖ * m1 t + P * K * m2 t + M1 * Real.exp (-t) with hBm
  -- antitone majorants
  have hmono : ∀ (X : ℝ) {t u : ℝ}, 0 < t → t ≤ u → min X (u ^ (-n)) ≤ min X (t ^ (-n)) := by
    intro X t u ht htu
    exact min_le_min_left _ (Real.rpow_le_rpow_of_nonpos ht htu (by linarith))
  have hexpmin : ∀ (θ : ℝ), 0 < θ → ∀ u : ℝ, 0 < u →
      u ^ (-n) * Real.exp (-θ / u) ≤ min (c * θ ^ (-n)) (u ^ (-n)) := by
    intro θ hθ u hu
    refine le_min (HRS.KernelAux.t_pow_exp_bound hn hθ hu) ?_
    have : Real.exp (-θ / u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ θ / u := by positivity
      rw [neg_div]; linarith
    have hp := Real.rpow_nonneg hu.le (-n)
    nlinarith
  have hpsi : ∀ u : ℝ, 0 < u → |HRS.KernelAux.psiG j (Torus.mk y) u| ≤ Bm u := by
    intro u hu
    have h1 : 0 ≤ P * ‖y‖ * m1 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ1p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h2 : 0 ≤ P * K * m2 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ2p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h3 : 0 ≤ M1 * Real.exp (-u) := by positivity
    rcases le_or_gt u 1 with hu1 | hu1
    · have h := hK y hy u hu hu1
      have hpow : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) = P * u ^ (-n) := by
        rw [HRS.KernelAux.sqrt_div_pow_eq d hu, hP, div_eq_mul_inv (2 * π ^ 2), ← Real.rpow_neg_one u,
          hn_def]
        have : Real.sqrt π ^ d * u ^ (-(d:ℝ)/2) * (2 * π ^ 2 * u ^ (-1:ℝ)) =
            2 * π ^ 2 * Real.sqrt π ^ d * (u ^ (-(d:ℝ)/2) * u ^ (-1:ℝ)) := by ring
        rw [this, ← Real.rpow_add hu]
        congr 2; ring
      have e1 : Real.exp (-(π ^ 2 * ‖y‖ ^ 2 / u)) = Real.exp (-θ1 / u) := by rw [hθ1, neg_div]
      have e2 : Real.exp (-(π ^ 2 / (8 * u))) = Real.exp (-θ2 / u) := by
        rw [hθ2]; congr 1; field_simp
      rw [hpow, e1, e2] at h
      refine h.trans ?_
      have k1 := hexpmin θ1 hθ1p u hu
      have k2 := hexpmin θ2 hθ2p u hu
      have : P * u ^ (-n) * (‖y‖ * Real.exp (-θ1 / u) + K * Real.exp (-θ2 / u)) =
          P * ‖y‖ * (u ^ (-n) * Real.exp (-θ1 / u)) + P * K * (u ^ (-n) * Real.exp (-θ2 / u)) := by ring
      rw [this]
      simp only [hBm]
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hP0 hr.le)
      have := mul_le_mul_of_nonneg_left k2 (mul_nonneg hP0 hK0)
      simp only [hm1, hm2]
      linarith
    · have h := hM1 (Torus.mk y) u hu1.le
      refine h.trans ?_
      simp only [hBm]
      linarith [mul_comm M1 (Real.exp (-u))]
  have hBanti : ∀ t ε : ℝ, 0 < t → 0 ≤ ε → Bm (t + ε) ≤ Bm t := by
    intro t ε ht hε
    simp only [hBm, hm1, hm2]
    have e1 := hmono (c * θ1 ^ (-n)) ht (show t ≤ t + ε by linarith)
    have e2 := hmono (c * θ2 ^ (-n)) ht (show t ≤ t + ε by linarith)
    have e3 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have := mul_le_mul_of_nonneg_left e1 (mul_nonneg hP0 hr.le)
    have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hP0 hK0)
    have := mul_le_mul_of_nonneg_left e3 hM10
    linarith
  -- integrals
  obtain ⟨hi1, hv1⟩ := integral_min_rpow ha han hc0 hθ1p
  obtain ⟨hi2, hv2⟩ := integral_min_rpow ha han hc0 hθ2p
  have hGi := Real.GammaIntegral_convergent ha
  have heq : ∀ t : ℝ, t ^ (a - 1) * Bm t = P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1)) := by
    intro t; simp only [hBm, hm1, hm2]; ring
  have hBi : IntegrableOn (fun t => t ^ (a - 1) * Bm t) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) :=
      ((hi1.const_mul _).add (hi2.const_mul _)).add (hGi.const_mul _)
    exact h.congr_fun (fun t _ => (heq t).symm) measurableSet_Ioi
  have hBint : ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t =
      P * ‖y‖ * (θ1 ^ (a - n) * C0) + P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)]
    have f1 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi1.const_mul _
    have f2 : IntegrableOn (fun t : ℝ => P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi2.const_mul _
    have f3 : IntegrableOn (fun t : ℝ => M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) := hGi.const_mul _
    have f12 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
        P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) := f1.add f2
    rw [integral_add f12 f3, integral_add f1 f2, integral_const_mul, integral_const_mul,
      integral_const_mul, hv1, hv2, ← Real.Gamma_eq_integral ha]
  have hint : |∫ t in Ioi (0:ℝ), t ^ (a - 1) * HRS.KernelAux.psiG j (Torus.mk y) (t + ε)| ≤
      ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hBi ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))
    have ht0 : (0:ℝ) < t := ht
    have hp := Real.rpow_pos_of_pos ht0 (a - 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left ((hpsi (t + ε) (by linarith)).trans (hBanti t ε ht0 hε.le)) hp.le
  have hθ1pow : ‖y‖ * θ1 ^ (a - n) = π ^ (-(s + 2)) * ‖y‖ ^ (-s - 1) := by
    have hexp : a - n = -(s / 2 + 1) := by rw [ha_def, hn_def]; ring
    rw [hexp, hθ1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hr.le]
    have e3 : ‖y‖ * (π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) =
        π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * (‖y‖ ^ (1:ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) := by
      rw [Real.rpow_one]; ring
    rw [e3, ← Real.rpow_add hr]
    congr 2 <;> push_cast <;> ring
  rw [HRS.KernelAux.heatRieszGrad_eq_integral hsd hε (Torus.mk y) j]
  change |A * _| ≤ _
  rw [abs_mul, abs_of_nonneg hA0]
  calc A * |∫ t in Ioi (0:ℝ), t ^ (a - 1) * HRS.KernelAux.psiG j (Torus.mk y) (t + ε)|
      ≤ A * (P * ‖y‖ * (θ1 ^ (a - n) * C0) + P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a) := by
        gcongr
        exact hint.trans (le_of_eq hBint)
    _ = A * (P * C0 * (‖y‖ * θ1 ^ (a - n))) + A * (P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a) := by ring
    _ = _ := by rw [hθ1pow]; ring


theorem heatRieszGrad_bound_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ z : Torus d, z ≠ 0 →
      ‖heatRieszGrad d s ε z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1) := by
  choose C1 C2 hC1 hC2 hC using fun j => heat_comp_bound_of_one_le hd hs0 hsd j
  refine ⟨∑ j, (C1 j + C2 j), fun ε hε z hz => ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_mk_box z
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hz
    funext i; simp [Torus.mk]
  rw [tdist_mk hy]
  have h1 := HRS.KernelAux.norm_toLp_le_sum (WithLp.ofLp (heatRieszGrad d s ε (Torus.mk y)))
  rw [WithLp.toLp_ofLp] at h1
  refine h1.trans ?_
  have hr : 0 ≤ ‖y‖ ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (hC j ε hε y hy hy0).trans ?_
  have := hC1 j
  have := hC2 j
  nlinarith

theorem goodKernel_heat_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → GoodKernel d s C (heatRieszGrad d s ε) := by
  obtain ⟨C, hC⟩ := heatRieszGrad_bound_of_one_le hd hs0 hsd
  refine ⟨max C 0, le_max_right _ _, fun ε hε => ?_⟩
  refine ⟨by omega, hs0, hsd, le_max_right _ _, (continuous_heatRieszGrad hsd hε).measurable,
    heatRieszGrad_neg ε, fun z hz => (hC ε hε z hz).trans ?_⟩
  have : 0 ≤ tdist z 0 ^ (-s - 1) + 1 := by
    have := Real.rpow_nonneg (tdist_nonneg z 0) (-s - 1)
    linarith
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) this

/-- The Fourier coefficients of `∇g * h` (cancellation convention) for a Lipschitz function `h`. -/
theorem coeff_convGradConv_lip_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hcont : Continuous h) {B L : ℝ} (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) (k : Lattice d) (i : Fin d) :
    ∫ x, Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hGε⟩ := goodKernel_heat_of_one_le hd hs0 hsd
  set l : Filter ℝ := 𝓝[>] (0 : ℝ) with hl
  -- the left side converges
  have hLHS : Tendsto (fun ε : ℝ => ∫ x, Torus.mode (-k) x *
      ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ)) l
      (𝓝 (∫ x, Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_norm_le_const ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hc := (hGε ε hε).continuous_op hcont hB hL hL0 hB0
      have : Continuous fun x : Torus d => Torus.mode (-k) x *
          ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ) :=
        (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hc))
      exact this.aestronglyMeasurable
    · refine ⟨L * opM1 d s C + B * opM2 s C, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans ?_ ((hGε ε hε).bound_op h B L hcont.measurable hB hL hL0 hB0 x)
      have := PiLp.norm_apply_le (convGradConv (heatRieszGrad d s ε) h x) i
      simpa using this
    · refine Eventually.of_forall fun x => ?_
      have := tendsto_convGradConv_heat hsd hGε hcont hB hL hL0 hB0 x
      have h2 := ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp this
      exact (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp h2))
  set R : ℝ → ℂ := fun ε => (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
    ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) *
      ((rieszCoeff d s k * Real.exp (-ε * Lattice.enorm k ^ 2) : ℝ) : ℂ)) with hR
  have hRc : Continuous R := by
    simp only [hR]
    fun_prop
  have hRHS : Tendsto R l (𝓝 ((∫ y, Torus.mode (-k) y * (h y : ℂ)) *
      ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)))) := by
    have := (hRc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hR] using this
  have hEq : (fun ε : ℝ => ∫ x, Torus.mode (-k) x *
      ((convGradConv (heatRieszGrad d s ε) h x i : ℝ) : ℂ)) =ᶠ[l] R := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact coeff_convGradConv_heat hsd hε (hGε ε hε) hcont hB k i
  exact tendsto_nhds_unique (hLHS.congr' hEq) hRHS

/-- The Fourier coefficients of `∇g * h` (cancellation convention) for a `C¹` function `h`. -/
theorem coeff_convGradConv_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {h : Torus d → ℝ}
    (hh : Torus.IsCk 1 h) (k : Lattice d) (i : Fin d) :
    ∫ x, Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) h x i : ℝ) : ℂ) =
      (∫ y, Torus.mode (-k) y * (h y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) := by
  obtain ⟨B, hB0, hB⟩ := isCk_bounded hh
  obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh
  exact coeff_convGradConv_lip_of_one_le hd hs0 hsd (isCk_continuous hh) hB hL hL0 hB0 k i

theorem goodKernel_periodicRieszGrad_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, GoodKernel d s C (periodicRieszGrad d s) := by
  obtain ⟨C, hC⟩ := periodicRieszGrad_bound_tdist_aux_of_one_le hd hs0 hsd
  refine ⟨max C 0, ?_⟩
  refine ⟨by omega, hs0, hsd, le_max_right _ _, measurable_periodicRieszGrad hsd,
    periodicRieszGrad_neg_of_lt hsd, fun z hz => (hC z hz).trans ?_⟩
  have : 0 ≤ tdist z 0 ^ (-s - 1) + 1 := by
    have := Real.rpow_nonneg (tdist_nonneg z 0) (-s - 1)
    linarith
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) this


theorem continuous_convGradConv_apply_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hc : Continuous f) {B L : ℝ} (hB : ∀ x, |f x| ≤ B) (hL : IsLipschitz L f) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) : Continuous (convGradConv (periodicRieszGrad d s) f) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  exact hG.continuous_op hc hB hL hL0 hB0

theorem continuous_Phi_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d) {f : Torus d → ℝ}
    (hc : Continuous f) {B L : ℝ} (hB : ∀ x, |f x| ≤ B) (hL : IsLipschitz L f) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) : Continuous (Phi d s v f) :=
  continuous_const.inner (continuous_convGradConv_apply_of_one_le hd hs0 hsd hc hB hL hL0 hB0)

theorem coeffOf_Phi_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d) {f : Torus d → ℝ}
    (hc : Continuous f) {B L : ℝ} (hB : ∀ x, |f x| ≤ B) (hL : IsLipschitz L f) (hL0 : 0 ≤ L)
    (hB0 : 0 ≤ B) (k : Lattice d) :
    coeffOf (Phi d s v f) k =
      ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        coeffOf f k := by
  have hcont := continuous_convGradConv_apply_of_one_le hd hs0 hsd hc hB hL hL0 hB0
  have hci : ∀ i, Continuous fun x => ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ) := fun i =>
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp hcont)
  have hint : ∀ i, Integrable fun x => Torus.mode (-k) x *
      ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ) := fun i =>
    ((Torus.continuous_mode (-k)).mul (hci i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPhi : ∀ x, Torus.mode (-k) x * ((Phi d s v f x : ℝ) : ℂ) =
      ∑ i, (v i : ℂ) * (Torus.mode (-k) x * ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ)) := by
    intro x
    unfold Phi
    rw [inner_eq_sum]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [coeffOf_eq_integral]
  simp_rw [hPhi]
  rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
  have hi : ∀ i, ∫ x, (v i : ℂ) * (Torus.mode (-k) x *
      ((convGradConv (periodicRieszGrad d s) f x i : ℝ) : ℂ)) =
      (v i : ℂ) * ((∫ y, Torus.mode (-k) y * (f y : ℂ)) *
        ((2 * Real.pi * Complex.I * ((k i : ℤ) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ))) := by
    intro i
    rw [integral_const_mul, coeff_convGradConv_lip_of_one_le hd hs0 hsd hc hB hL hL0 hB0 k i]
  simp_rw [hi]
  rw [coeffOf_eq_integral f k, inner_eq_sum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Lattice.toEuc]
  ring

theorem fourier_side_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    {u w : Torus d → ℝ} (hu : Continuous u) {Bu Lu : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hLu : IsLipschitz Lu u) (hLu0 : 0 ≤ Lu) (hBu0 : 0 ≤ Bu)
    (hw : Continuous w) {Bw Lw : ℝ} (hBw : ∀ x, |w x| ≤ Bw)
    (hLw : IsLipschitz Lw w) (hLw0 : 0 ≤ Lw) (hBw0 : 0 ≤ Bw) {n : ℕ}
    (hwt : IsTrigPoly n (coeffOf w)) :
    (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        (coeffOf u k * conj (coeffOf w k))).re = ∫ x, Phi d s v u x * w x ∧
      ∫ x, u x * Phi d s v w x = -(∫ x, Phi d s v u x * w x) := by
  set c : Lattice d → ℂ := fun k =>
    (2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ) with hc
  have hcneg : ∀ k, c (-k) = - c k := by
    intro k
    simp only [hc]
    have h1 : (inner ℝ v (Lattice.toEuc (-k)) : ℝ) = -(inner ℝ v (Lattice.toEuc k)) := by
      have : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
      rw [this, inner_neg_right]
    rw [h1, HRS.rieszCoeff_neg]
    push_cast
    ring
  have hP1 := coeffOf_Phi_of_one_le hd hs0 hsd v hu hBu hLu hLu0 hBu0
  have hP0 := coeffOf_Phi_of_one_le hd hs0 hsd v hw hBw hLw hLw0 hBw0
  have hPhi1c := continuous_Phi_of_one_le hd hs0 hsd v hu hBu hLu hLu0 hBu0
  have hPhi0c := continuous_Phi_of_one_le hd hs0 hsd v hw hBw hLw hLw0 hBw0
  have hPt : IsTrigPoly n (coeffOf (Phi d s v w)) := by
    intro k hk
    apply hwt
    intro h0
    apply hk
    rw [hP0, h0, mul_zero]
  have hint1 : Integrable (Phi d s v u) :=
    hPhi1c.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_u : Integrable u := hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hE := integral_mul_trig hint1 hw hwt
  have hE' := integral_mul_trig hint_u hPhi0c hPt
  -- reindexing by `k ↦ -k`
  have hreidx : ∀ g : Lattice d → ℂ, ∑ k ∈ boxFinset d n, g (-k) = ∑ k ∈ boxFinset d n, g k := by
    intro g
    exact Finset.sum_equiv (Equiv.neg _) (fun k => by
      simp only [Equiv.neg_apply]
      exact ⟨neg_mem_boxFinset, fun h => by simpa using neg_mem_boxFinset h⟩) (fun k _ => rfl)
  have hP1' : ∀ k, coeffOf (Phi d s v u) k = c k * coeffOf u k := hP1
  have hP0' : ∀ k, coeffOf (Phi d s v w) k = c k * coeffOf w k := hP0
  set S : ℂ := ∑ k ∈ boxFinset d n, c k * (coeffOf u k * conj (coeffOf w k)) with hS
  have hE_S : ((∫ x, Phi d s v u x * w x : ℝ) : ℂ) = S := by
    rw [hE, ← hreidx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_neg, hP1', coeffOf_neg_conj w k]
    ring
  have hE'_S : ((∫ x, u x * Phi d s v w x : ℝ) : ℂ) = -S := by
    rw [hE', ← hreidx, hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_neg, hP0', hcneg, coeffOf_neg_conj w k]
    ring
  have hreal : ∀ x : ℝ, ((x : ℝ) : ℂ) = S → x = S.re := fun x hx => by rw [← hx]; simp
  have hsum_eq : (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) *
      ((rieszCoeff d s k : ℝ) : ℂ)) * (coeffOf u k * conj (coeffOf w k))) = S := by
    rw [hS]
    refine tsum_eq_sum fun k hk => ?_
    have : coeffOf w k = 0 := by
      by_contra h
      exact hk (mem_boxFinset.2 (hwt k h))
    simp [this]
  rw [hsum_eq]
  have h1 := hreal _ hE_S
  refine ⟨h1.symm, ?_⟩
  have h2 : ((∫ x, u x * Phi d s v w x : ℝ) : ℂ) = (((-(∫ x, Phi d s v u x * w x)) : ℝ) : ℂ) := by
    rw [hE'_S, ← hE_S]; push_cast; ring
  exact_mod_cast h2

/-! ### The real-space side -/

theorem Phi_comb_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    {a w : Torus d → ℝ} (ha : Continuous a) {A La : ℝ} (hA : ∀ x, |a x| ≤ A) (hLa : IsLipschitz La a)
    (hLa0 : 0 ≤ La) (hA0 : 0 ≤ A) (hw : Continuous w) {Bw Lw : ℝ} (hBw : ∀ x, |w x| ≤ Bw)
    (hLw : IsLipschitz Lw w) (hLw0 : 0 ≤ Lw) (hBw0 : 0 ≤ Bw) (x : Torus d) :
    Phi d s v (fun y => a y * w y) x - a x * Phi d s v w x =
      ∫ y, inner ℝ v (periodicRieszGrad d s (x - y)) * (w y * (a y - a x)) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  have hu : Continuous fun y => a y * w y := ha.mul hw
  obtain ⟨huB, huL⟩ := prod_data hA hLa hA0 hBw hLw hBw0
  have huL0 : 0 ≤ A * Lw + Bw * La := by positivity
  have huB0 : 0 ≤ A * Bw := by positivity
  have hk1 := integrable_kern hG (hu.measurable) huB huL huL0 huB0 x
  have hk2 := integrable_kern hG (hw.measurable) hBw hLw hLw0 hBw0 x
  have e1 : ∀ f : Torus d → ℝ, Integrable (kern (periodicRieszGrad d s) f x) →
      Phi d s v f x = ∫ z, inner ℝ v (kern (periodicRieszGrad d s) f x z) := by
    intro f hf
    unfold Phi
    rw [convGradConv_eq_integral_kern, integral_inner hf]
  have hI1 : Integrable fun z => inner ℝ v (kern (periodicRieszGrad d s) (fun y => a y * w y) x z) :=
    hk1.const_inner v
  have hI2 : Integrable fun z => inner ℝ v (kern (periodicRieszGrad d s) w x z) := hk2.const_inner v
  rw [e1 _ hk1, e1 _ hk2, ← integral_const_mul, ← integral_sub hI1 (hI2.const_mul _)]
  have hpt : ∀ z, inner ℝ v (kern (periodicRieszGrad d s) (fun y => a y * w y) x z) -
      a x * inner ℝ v (kern (periodicRieszGrad d s) w x z) =
      inner ℝ v (periodicRieszGrad d s z) * (w (x - z) * (a (x - z) - a x)) := by
    intro z
    have := congrArg (fun q => inner ℝ v q) (kern_comb (periodicRieszGrad d s) a w x z)
    simp only [inner_sub_right, inner_smul_right] at this
    rw [this]; ring
  simp_rw [hpt]
  rw [← integral_sub_left_eq_self (fun z => inner ℝ v (periodicRieszGrad d s z) * (w (x - z) * (a (x - z) - a x))) volume x]
  simp only [sub_sub_cancel]

theorem realspace_identity_of_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    {a w : Torus d → ℝ} (ha : Continuous a) {A La : ℝ} (hA : ∀ x, |a x| ≤ A) (hLa : IsLipschitz La a)
    (hLa0 : 0 ≤ La) (hA0 : 0 ≤ A) (hw : Continuous w) {Bw Lw : ℝ} (hBw : ∀ x, |w x| ≤ Bw)
    (hLw : IsLipschitz Lw w) (hLw0 : 0 ≤ Lw) (hBw0 : 0 ≤ Bw) :
    ∫ p : Torus d × Torus d,
        inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) =
      (∫ x, Phi d s v (fun y => a y * w y) x * w x) - ∫ x, a x * w x * Phi d s v w x := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad_of_one_le hd hs0 hsd
  have hu : Continuous fun y => a y * w y := ha.mul hw
  obtain ⟨huB, huL⟩ := prod_data hA hLa hA0 hBw hLw hBw0
  have huL0 : 0 ≤ A * Lw + Bw * La := by positivity
  have huB0 : 0 ≤ A * Bw := by positivity
  have hC0 := hG.hC0
  -- the dominating function
  set H : Torus d → ℝ := fun z => ‖v‖ * (Bw * Bw * La) * (C * (‖z‖ ^ (-s) + d)) with hH
  have hHint : Integrable H := by
    have h1 := integrable_norm_rpow_neg hG.pos hG.hsd
    exact ((h1.add (integrable_const (d : ℝ))).const_mul C).const_mul _
  have hconv := Integrable.convolution_integrand (μ := (volume : Measure (Torus d)))
    (ν := (volume : Measure (Torus d))) (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_const (1 : ℝ)) hHint
  set f : Torus d × Torus d → ℝ := fun p =>
    inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) with hf
  have hmeas : Measurable f := by
    have hGm := hG.meas
    have h1 : Measurable fun p : Torus d × Torus d => periodicRieszGrad d s (p.1 - p.2) :=
      hGm.comp (measurable_fst.sub measurable_snd)
    have h2 : Measurable fun p : Torus d × Torus d => inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) :=
      (continuous_const.inner continuous_id).measurable.comp h1
    exact ((h2.mul (hw.measurable.comp measurable_fst)).mul (hw.measurable.comp measurable_snd)).mul
      ((ha.measurable.comp measurable_snd).sub (ha.measurable.comp measurable_fst))
  have hbd : ∀ p : Torus d × Torus d, ‖f p‖ ≤ H (p.1 - p.2) := by
    intro p
    set z := p.1 - p.2 with hz
    have hHnn : 0 ≤ H z := by
      simp only [hH]
      have := Real.rpow_nonneg (norm_nonneg z) (-s)
      positivity
    by_cases hz0 : z = 0
    · have : p.1 = p.2 := sub_eq_zero.mp hz0
      have : f p = 0 := by simp [hf, this]
      rw [this, norm_zero]; exact hHnn
    · have hdist : |a p.2 - a p.1| ≤ La * tdist z 0 := by
        refine (hLa p.2 p.1).trans ?_
        rw [tdist_eq_sub_zero, hz, ← neg_sub, tdist_neg]
      have hC' := hG.norm_mul_tdist_le z hz0
      have hw1 := hBw p.1
      have hw2 := hBw p.2
      have hin : |inner ℝ v (periodicRieszGrad d s z)| ≤ ‖v‖ * ‖periodicRieszGrad d s z‖ := by
        have := abs_real_inner_le_norm v (periodicRieszGrad d s z)
        exact this
      rw [Real.norm_eq_abs]
      simp only [hf, abs_mul]
      have ht0 := tdist_nonneg z 0
      calc |inner ℝ v (periodicRieszGrad d s (p.1 - p.2))| * |w p.1| * |w p.2| * |a p.2 - a p.1|
          ≤ (‖v‖ * ‖periodicRieszGrad d s z‖) * Bw * Bw * (La * tdist z 0) := by gcongr
        _ = ‖v‖ * (Bw * Bw * La) * (tdist z 0 * ‖periodicRieszGrad d s z‖) := by ring
        _ ≤ ‖v‖ * (Bw * Bw * La) * (C * (‖z‖ ^ (-s) + d)) := by gcongr
  have hint : Integrable f := by
    refine (hconv.congr (Filter.Eventually.of_forall fun p => ?_)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
    simp [hH]
  have hfub : ∫ p, f p = ∫ x, ∫ y, f (x, y) := integral_prod f hint
  rw [hfub]
  have hin : ∀ x, ∫ y, f (x, y) = w x * (Phi d s v (fun y => a y * w y) x - a x * Phi d s v w x) := by
    intro x
    rw [Phi_comb_of_one_le hd hs0 hsd v ha hA hLa hLa0 hA0 hw hBw hLw hLw0 hBw0 x, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf]
    ring
  simp_rw [hin]
  have hP1 : Continuous (Phi d s v (fun y => a y * w y)) :=
    continuous_Phi_of_one_le hd hs0 hsd v hu huB huL huL0 huB0
  have hP2 : Continuous (Phi d s v w) := continuous_Phi_of_one_le hd hs0 hsd v hw hBw hLw hLw0 hBw0
  have i1 : Integrable fun x => Phi d s v (fun y => a y * w y) x * w x :=
    (hP1.mul hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable fun x => a x * w x * Phi d s v w x :=
    ((ha.mul hw).mul hP2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-! ### The `d = 1` statements (verbatim copies of `GradConv.lean` with `hd : d = 1`) -/

/-- `∇g` is smooth away from the origin. -/
theorem periodicRieszGrad_smoothOffZero (hd : d = 1) (hs0 : 0 ≤ s) (hsd : s < d) :
    IsSmoothOffZero (periodicRieszGrad d s) := by
  subst hd
  exact periodicRieszGrad_smoothOffZero_d1 hs0 (by exact_mod_cast hsd)

/-- Kernel bound in torus-distance form: `|∇g(z)| ≤ C(|z|^{-s-1} + 1)` for `z ≠ 0`
(KERN-01 `periodicRiesz_grad_bound` restated with `tdist`). -/
theorem periodicRieszGrad_bound_tdist (hd : d = 1) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1) :=
  periodicRieszGrad_bound_tdist_aux_of_one_le hd.ge hs0 hsd

/-- **Required kernel fact.** The convention "agrees with distributional convolution"
(lines 10099–10101): for `0 ≤ s < d` and `C¹` `h`, the Fourier coefficients of the `i`-th
component of `∇g * h` are `2πi k_i ĝ(k) ĥ(k)` (`gradRieszCoeff`).  Extends KERN-01's
`periodicRiesz_fourierCoeff`. -/
theorem convGradConv_coeff (hd : d = 1) (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hh : Torus.IsCk 1 h) (i : Fin d) :
    coeffOf (fun x => convGradConv (periodicRieszGrad d s) h x i) =
      gradRieszCoeff d s i (coeffOf h) := by
  funext k
  rw [coeffOf_eq_integral, coeff_convGradConv_of_one_le hd.ge hs0 hsd hh k i]
  unfold gradRieszCoeff derivCoeff rieszMult
  rw [coeffOf_eq_integral]
  ring

/-- **Required kernel fact.** For `C¹` `h` the convention yields a bounded continuous vector field
(lines 10097–10099). -/
theorem convGradConv_continuous (hd : d = 1) (hs0 : 0 ≤ s) (hsd : s < d) (h : Torus d → ℝ)
    (hh : Torus.IsCk 1 h) : Continuous (convGradConv (periodicRieszGrad d s) h) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad_of_one_le hd.ge hs0 hsd
  obtain ⟨B, hB0, hB⟩ := isCk_bounded hh
  obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh
  exact hG.continuous_op (isCk_continuous hh) hB hL hL0 hB0

/-- **Required kernel fact** (Lemma C.1 input, lines 12229–12233): for `h ∈ C^{m+1}`, `∇g * h` is
`C^m` with `‖∇g*h‖_{C^m} ≤ C ‖h‖_{C^{m+1}}` (the convention loses at most one derivative,
uniformly in `0 ≤ s < d`). -/
theorem convGradConv_cbNorm (hd : d = 1) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C : ℝ, ∀ h : Torus d → ℝ, Torus.IsCk (m + 1) h →
      Torus.IsCk m (convGradConv (periodicRieszGrad d s) h) ∧
        Torus.cbNorm m (convGradConv (periodicRieszGrad d s) h) ≤ C * Torus.cbNorm (m + 1) h := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad_of_one_le hd.ge hs0 hsd
  obtain ⟨K, _, hK⟩ := hG.regularity m
  exact ⟨K, fun h hh => hK h (by exact_mod_cast hh)⟩

/-- **Required kernel fact.**  The Fourier-side pairing of Lemma C.4 equals the symmetrized
real-space pairing for `κ = v·∇g`. -/
theorem rieszGrad_pairing_symmetrized (hd : d = 1) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (v : Euc d)
    (La : ℝ) (a : Torus d → ℝ) (ha : IsLipschitz La a) (n : ℕ) (w : Torus d → ℝ)
    (hw : Torus.IsCk 1 w) (hwtrig : IsTrigPoly n (coeffOf w)) :
    (∑' k, ((2 * Real.pi * Complex.I * (inner ℝ v (Lattice.toEuc k) : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
        (coeffOf (fun x => a x * w x) k * conj (coeffOf w k))).re =
      (1 / 2) * ∫ p : Torus d × Torus d,
        inner ℝ v (periodicRieszGrad d s (p.1 - p.2)) * w p.1 * w p.2 * (a p.2 - a p.1) := by
  have hd1 : 1 ≤ d := hd.ge
  have haL : IsLipschitz (max La 0) a := fun x y =>
    (ha x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tdist_nonneg x y))
  have haC : Continuous a := haL.continuous (le_max_right _ _)
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |a x| ≤ A := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn haC.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun x => by
      have := hB x (Set.mem_univ x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)⟩
  have hwC := isCk_continuous hw
  obtain ⟨Bw, hBw0, hBw⟩ := isCk_bounded hw
  obtain ⟨Lw, hLw0, hLw⟩ := isLipschitz_of_isCk hw
  obtain ⟨huB, huL⟩ := prod_data hA haL hA0 hBw hLw hBw0
  have huC : Continuous fun y => a y * w y := haC.mul hwC
  obtain ⟨h1, h2⟩ := fourier_side_of_one_le hd1 hs0 hsd v huC huB huL (by positivity) (by positivity)
    hwC hBw hLw hLw0 hBw0 hwtrig
  rw [h1, realspace_identity_of_one_le hd1 hs0 hsd v haC hA haL (le_max_right _ _) hA0 hwC hBw hLw
    hLw0 hBw0]
  have : ∫ x, a x * w x * Phi d s v w x = ∫ x, (fun y => a y * w y) x * Phi d s v w x := rfl
  rw [this, h2]
  ring

end HRS.KernelGradD1

/-!
## Correspondence

Each theorem of namespace `HRS.KernelGradD1` above is the theorem of the same name in
`HRS.KernelGrad` (`HRS/Kernel/GradConv.lean`) with `(hd : 2 ≤ d)` replaced by `(hd : d = 1)`:
`periodicRieszGrad_smoothOffZero`, `periodicRieszGrad_bound_tdist`, `convGradConv_coeff`,
`convGradConv_continuous`, `convGradConv_cbNorm`, `rieszGrad_pairing_symmetrized`.  Through the
verbatim definition copies of `GradBasic.lean` these are the `d = 1` cases of the `HRS.PDE`
declarations of `HRS/PDE/Convention.lean` and `HRS/PDE/Toolbox.lean` listed at the end of
`GradConv.lean`.
-/

end
