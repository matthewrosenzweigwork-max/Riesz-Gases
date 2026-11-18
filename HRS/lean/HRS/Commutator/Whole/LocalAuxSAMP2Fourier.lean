import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.RieszAux
import HRS.Commutator.Whole.LocalAuxKR

/-!
# CMX-SAMP (`potentialSobolev`), part 1: the Fourier transform of `∇g` against every Schwartz function

`HRS.Commutator.Whole.cmxMY_kernGrad_fourier` (CMX-KR) gives `∫ ∇g_i 𝓕Φ = c ∫ ξ_i|ξ|^{-(d-s)} Φ` for
`Φ` vanishing near `0`.  Here the same identity is proved for *all* Schwartz `Φ`: the only change is
the integration by parts against the singular weight `|ξ|^{p}` (`p = s+2-d`, `p - 1 > -d`), which is
done with the regularisation `(η²+|ξ|²)^{p/2}` and dominated convergence as `η → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.SAMP2

open HRS HRS.Whole

variable {d : ℕ}

lemma norm_sq_rpow (ξ : Euc d) (p : ℝ) : (‖ξ‖ ^ 2) ^ (p / 2) = ‖ξ‖ ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
  norm_num
  congr 1; ring

lemma hasFDerivAt_reg (η p : ℝ) (hη : 0 < η) (x : Euc d) :
    HasFDerivAt (fun ξ : Euc d => (η ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2))
      ((p * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1)) • innerSL ℝ x) x := by
  have h1 : HasFDerivAt (fun ξ : Euc d => η ^ 2 + ‖ξ‖ ^ 2) ((2 : ℕ) • innerSL ℝ x) x :=
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add (η ^ 2)
  have hpos : η ^ 2 + ‖x‖ ^ 2 ≠ 0 := by positivity
  have h2 := h1.rpow_const (p := p / 2) (Or.inl hpos)
  convert h2 using 1
  ext y
  simp
  ring

lemma reg_le_zero {p : ℝ} (hp0 : p ≤ 0) {η : ℝ} (hη : 0 < η) (x : Euc d) :
    (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2) ≤ (η ^ 2) ^ (p / 2) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖x‖]) (by linarith)

lemma reg_le_norm {p : ℝ} (hp0 : p ≤ 0) (η : ℝ) {x : Euc d} (hx : x ≠ 0) :
    (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2) ≤ ‖x‖ ^ p := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [← norm_sq_rpow x p]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg η]) (by linarith)

lemma reg_deriv_bound {p : ℝ} (hp0 : p ≤ 0) {η : ℝ} (hη : 0 < η) (x : Euc d) (i : Fin d) :
    |p * x i * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1)| ≤ |p| * (η ^ 2) ^ ((p - 1) / 2) := by
  set B := η ^ 2 + ‖x‖ ^ 2 with hB
  have hBpos : 0 < B := by positivity
  have hxi : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  have hxB : ‖x‖ ≤ B ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by rw [hB]; nlinarith [sq_nonneg η])
  have hpos2 : 0 < B ^ (p / 2 - 1) := Real.rpow_pos_of_pos hBpos _
  have h1 : B ^ ((1 : ℝ) / 2) * B ^ (p / 2 - 1) = B ^ ((p - 1) / 2) := by
    rw [← Real.rpow_add hBpos]
    congr 1; ring
  have h2 : B ^ ((p - 1) / 2) ≤ (η ^ 2) ^ ((p - 1) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖x‖]) (by linarith)
  rw [abs_mul, abs_mul, abs_of_pos hpos2]
  calc |p| * |x i| * B ^ (p / 2 - 1) ≤ |p| * B ^ ((1 : ℝ) / 2) * B ^ (p / 2 - 1) := by
        gcongr
        exact hxi.trans hxB
    _ = |p| * B ^ ((p - 1) / 2) := by rw [mul_assoc, h1]
    _ ≤ |p| * (η ^ 2) ^ ((p - 1) / 2) := by gcongr

lemma reg_deriv_dom {p : ℝ} (hp0 : p ≤ 0) (η : ℝ) {x : Euc d} (hx : x ≠ 0) (i : Fin d) :
    |p * x i * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1)| ≤ |p| * ‖x‖ ^ (p - 1) := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxi : |x i| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  have h1 : (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1) ≤ ‖x‖ ^ (p - 2) := by
    have : ‖x‖ ^ (p - 2) = (‖x‖ ^ 2) ^ (p / 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
      congr 1; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg η]) (by linarith)
  have hpos : 0 < (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1) := Real.rpow_pos_of_pos (by positivity) _
  have h3 : ‖x‖ * ‖x‖ ^ (p - 2) = ‖x‖ ^ (p - 1) := by
    rw [← Real.rpow_one_add' (norm_nonneg x) (by linarith)]
    · congr 1; ring
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  calc |p| * |x i| * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1) ≤ |p| * ‖x‖ * ‖x‖ ^ (p - 2) := by
        gcongr
    _ = |p| * ‖x‖ ^ (p - 1) := by rw [mul_assoc, h3]

lemma ibp_singular (hd : 1 ≤ d) {p : ℝ} (hp0 : p ≤ 0) (hp1 : -(d : ℝ) < p - 1)
    (Φ : SchwartzMap (Euc d) ℂ) (i : Fin d) :
    ∫ ξ : Euc d, ((‖ξ‖ ^ p : ℝ) : ℂ) * fderiv ℝ Φ ξ (EuclideanSpace.single i (1 : ℝ)) =
      -∫ ξ : Euc d, ((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ := by
  set m : Euc d := EuclideanSpace.single i (1 : ℝ) with hm
  have hΦd : Differentiable ℝ Φ := (Φ.smooth 1).differentiable (by simp)
  have hΨf : (⇑(LineDeriv.lineDerivOp m Φ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) =
      fun ξ => fderiv ℝ Φ ξ m := funext (SchwartzMap.lineDerivOp_apply_eq_fderiv m Φ)
  have hdΦ : Integrable (fun ξ : Euc d => fderiv ℝ Φ ξ m) := by
    have := SchwartzMap.integrable (μ := (volume : Measure (Euc d)))
      (LineDeriv.lineDerivOp m Φ : SchwartzMap (Euc d) ℂ)
    rwa [hΨf] at this
  -- the regularised identity
  have hreg : ∀ η : ℝ, 0 < η →
      ∫ ξ : Euc d, (((η ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2) : ℝ) : ℂ) * fderiv ℝ Φ ξ m =
        -∫ ξ : Euc d, ((p * ξ i * (η ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2 - 1) : ℝ) : ℂ) * Φ ξ := by
    intro η hη
    set f : Euc d → ℂ := fun ξ => (((η ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2) : ℝ) : ℂ) with hf
    have hfd : ∀ x : Euc d, HasFDerivAt f
        (Complex.ofRealCLM.comp ((p * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1)) • innerSL ℝ x)) x :=
      fun x => Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_reg η p hη x)
    have hfm : ∀ x : Euc d, fderiv ℝ f x m =
        ((p * x i * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1) : ℝ) : ℂ) := by
      intro x
      rw [(hfd x).fderiv]
      simp [hm, EuclideanSpace.inner_single_right]
      ring
    have hfc : Continuous f := Complex.continuous_ofReal.comp
      (Continuous.rpow_const (by fun_prop) fun ξ => Or.inl (by positivity))
    have hfb : ∀ x : Euc d, ‖f x‖ ≤ (η ^ 2) ^ (p / 2) := by
      intro x
      simp only [hf, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact reg_le_zero hp0 hη x
    have hg1 : Continuous fun x : Euc d => ((p * x i * (η ^ 2 + ‖x‖ ^ 2) ^ (p / 2 - 1) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (by
        refine Continuous.mul (Continuous.mul continuous_const
          ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous)) ?_
        exact Continuous.rpow_const (by fun_prop) fun ξ => Or.inl (by positivity))
    have hI1 : Integrable (fun ξ : Euc d => fderiv ℝ f ξ m * Φ ξ) := by
      simp_rw [hfm]
      refine Φ.integrable.bdd_mul (c := |p| * (η ^ 2) ^ ((p - 1) / 2)) hg1.aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact reg_deriv_bound hp0 hη x i
    have hI2 : Integrable (fun ξ : Euc d => f ξ * fderiv ℝ Φ ξ m) :=
      hdΦ.bdd_mul hfc.aestronglyMeasurable (Eventually.of_forall hfb)
    have hI3 : Integrable (fun ξ : Euc d => f ξ * Φ ξ) :=
      Φ.integrable.bdd_mul hfc.aestronglyMeasurable (Eventually.of_forall hfb)
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := f) (g := ⇑Φ) (v := m) hI1 hI2 hI3 (fun x _ => (hfd x).differentiableAt)
      (fun x _ => hΦd x)
    rw [key]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [hfm ξ]
  -- passage to the limit `η → 0`
  set η : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hηdef
  have hηpos : ∀ n, 0 < η n := fun n => by simp only [hηdef]; positivity
  have hηlim : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim_base : ∀ ξ : Euc d, ξ ≠ 0 → ∀ q : ℝ,
      Tendsto (fun n => (η n ^ 2 + ‖ξ‖ ^ 2) ^ q) atTop (𝓝 ((‖ξ‖ ^ 2) ^ q)) := by
    intro ξ hξ q
    have hxn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have h1 : Tendsto (fun n => η n ^ 2 + ‖ξ‖ ^ 2) atTop (𝓝 (‖ξ‖ ^ 2)) := by
      simpa using (hηlim.pow 2).add_const (‖ξ‖ ^ 2)
    exact h1.rpow_const (Or.inl (by positivity))
  have hpd : -(d : ℝ) < p := by linarith
  have hL : Tendsto (fun n => ∫ ξ : Euc d, (((η n ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2) : ℝ) : ℂ) *
        fderiv ℝ Φ ξ m) atTop (𝓝 (∫ ξ : Euc d, ((‖ξ‖ ^ p : ℝ) : ℂ) * fderiv ℝ Φ ξ m)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ξ : Euc d => ‖ξ‖ ^ p * ‖fderiv ℝ Φ ξ m‖) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (Complex.continuous_ofReal.comp
        (Continuous.rpow_const (by fun_prop) fun ξ => Or.inl (by
          have := hηpos n; positivity))).aestronglyMeasurable.mul hdΦ.aestronglyMeasurable
    · have := integrable_norm_rpow_mul_schwartz hd hpd hp0
        (LineDeriv.lineDerivOp m Φ : SchwartzMap (Euc d) ℂ)
      simpa [hΨf] using this
    · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
        have := hηpos n; positivity)]
      exact mul_le_mul_of_nonneg_right (reg_le_norm hp0 (η n) hξ) (norm_nonneg _)
    · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
      have h1 := hlim_base ξ hξ (p / 2)
      rw [norm_sq_rpow] at h1
      exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const _
  have hR : Tendsto (fun n => ∫ ξ : Euc d, ((p * ξ i * (η n ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2 - 1) : ℝ) : ℂ) *
        Φ ξ) atTop (𝓝 (∫ ξ : Euc d, ((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ξ : Euc d => |p| * (‖ξ‖ ^ (p - 1) * ‖Φ ξ‖)) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (Complex.continuous_ofReal.comp (by
        refine Continuous.mul (Continuous.mul continuous_const
          ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous)) ?_
        exact Continuous.rpow_const (by fun_prop) fun ξ => Or.inl (by
          have := hηpos n; positivity))).aestronglyMeasurable.mul Φ.continuous.aestronglyMeasurable
    · exact (integrable_norm_rpow_mul_schwartz hd hp1 (by linarith) Φ).const_mul |p|
    · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (reg_deriv_dom hp0 (η n) hξ i) (norm_nonneg _)
    · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
      have h1 := hlim_base ξ hξ (p / 2 - 1)
      have h2 : (‖ξ‖ ^ 2) ^ (p / 2 - 1) = ‖ξ‖ ^ (p - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
        congr 1; push_cast; ring
      rw [h2] at h1
      have h3 : Tendsto (fun n => p * ξ i * (η n ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2 - 1)) atTop
          (𝓝 (p * ξ i * ‖ξ‖ ^ (p - 2))) := h1.const_mul (p * ξ i)
      have h4 : p * ξ i * ‖ξ‖ ^ (p - 2) = p * ‖ξ‖ ^ (p - 2) * ξ i := by ring
      rw [h4] at h3
      exact ((Complex.continuous_ofReal.tendsto _).comp h3).mul_const _
  have hLR : ∀ n, ∫ ξ : Euc d, (((η n ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2) : ℝ) : ℂ) * fderiv ℝ Φ ξ m =
      -∫ ξ : Euc d, ((p * ξ i * (η n ^ 2 + ‖ξ‖ ^ 2) ^ (p / 2 - 1) : ℝ) : ℂ) * Φ ξ :=
    fun n => hreg (η n) (hηpos n)
  have hR' := hR.neg
  simp_rw [← hLR] at hR'
  exact tendsto_nhds_unique hL hR'

/-- `∫ ∇g_i 𝓕Φ = c ∫ ξ_i |ξ|^{-(d-s)} Φ` for every Schwartz `Φ` (no vanishing near `0` needed). -/
theorem kernGrad_fourier_full (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℂ, ∀ (i : Fin d) (Φ : SchwartzMap (Euc d) ℂ),
      ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
        c * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ := by
  have hd1 : 1 ≤ d := by omega
  set γ : ℝ := s + 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hγd : γ < d := by rw [hγ]; linarith
  set P : ℝ := Real.pi ^ (-γ / 2) * Real.Gamma (γ / 2) with hP
  set Q : ℝ := Real.pi ^ (-((d : ℝ) - γ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2) with hQ
  have hPpos : 0 < P := by
    rw [hP]; exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  set p : ℝ := γ - d with hp
  have hp0 : p ≤ 0 := by rw [hp]; linarith
  have hp1 : -(d : ℝ) < p - 1 := by rw [hp, hγ]; linarith
  refine ⟨((Q * p : ℝ) : ℂ) / (2 * Real.pi * Complex.I * (P : ℂ)), fun i Φ => ?_⟩
  set m : Euc d := EuclideanSpace.single i (1 : ℝ) with hm
  set Ψ : SchwartzMap (Euc d) ℂ := LineDeriv.lineDerivOp m Φ with hΨ
  have hΨf : (⇑Ψ : Euc d → ℂ) = fun ξ => fderiv ℝ Φ ξ m :=
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv m Φ)
  have hR := riesz_potential_aux hd1 γ hγ0 hγd Ψ
  rw [hΨf] at hR
  have hF : ∀ x : Euc d, 𝓕 (fun ξ : Euc d => fderiv ℝ Φ ξ m) x =
      (2 * Real.pi * Complex.I * (x i : ℂ)) * 𝓕 (⇑Φ) x :=
    fun x => cmxMY_fourier_partial Φ i x
  simp_rw [hF] at hR
  have hibp := ibp_singular hd1 hp0 hp1 Φ i
  have e1 : ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * ((2 * Real.pi * Complex.I * (x i : ℂ)) * 𝓕 (⇑Φ) x) =
      (2 * Real.pi * Complex.I) * ∫ x : Euc d, (((‖x‖ ^ (-γ) * x i : ℝ)) : ℂ) * 𝓕 (⇑Φ) x := by
    rw [← integral_const_mul]
    congr 1; ext x; push_cast; ring
  have e2 : ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
      -∫ x : Euc d, (((‖x‖ ^ (-γ) * x i : ℝ)) : ℂ) * 𝓕 (⇑Φ) x := by
    rw [← integral_neg]
    congr 1; ext x
    have : kernGrad s x i = -(‖x‖ ^ (-γ) * x i) := by
      simp [kernGrad, hγ]
    rw [this]; push_cast; ring
  have e3 : ∫ ξ : Euc d, ((p * ‖ξ‖ ^ (p - 2) * ξ i : ℝ) : ℂ) * Φ ξ =
      (p : ℂ) * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ := by
    rw [← integral_const_mul]
    congr 1; ext ξ
    have : p - 2 = -((d : ℝ) - s) := by rw [hp, hγ]; ring
    rw [this]; push_cast; ring
  rw [e1, hibp, e3] at hR
  rw [e2]
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 * Real.pi * Complex.I * (P : ℂ)) ≠ 0 := by
    simp [hPc, hpi, Complex.I_ne_zero]
  set I₁ : ℂ := ∫ x : Euc d, (((‖x‖ ^ (-γ) * x i : ℝ)) : ℂ) * 𝓕 (⇑Φ) x
  set J : ℂ := ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ
  rw [div_mul_eq_mul_div, eq_div_iff h2]
  push_cast
  linear_combination (-1 : ℂ) * hR

end HRS.Commutator.Whole.SAMP2
