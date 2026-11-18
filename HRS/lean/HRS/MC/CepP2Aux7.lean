import HRS.MC.CepP2Aux6

/-!
# Packet CEPP2 (aux 7): local smooth density of `χρ` from the bootstrap
-/

open MeasureTheory
noncomputable section
namespace HRS.MC.CepP2
variable {n : ℕ} {O : Set (XS n)}

lemma norm_le_wt (ζ : XS n) : ‖ζ‖ ≤ wt ζ := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs]; unfold wt; nlinarith [sq_nonneg ‖ζ.2‖]
  · unfold wt; nlinarith [sq_nonneg (‖ζ.2‖ - 1), abs_nonneg ζ.1]

/-- Moments of `√N_χ` are integrable once all `S(s)` hold. -/
lemma moment_integrable {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    (hS : ∀ s : ℤ, SobFin O ρ s) {χ : XS n → ℝ} (hχ : IsTest O χ) (m : ℕ) :
    Integrable (fun ζ : XS n => ‖ζ‖ ^ m * Real.sqrt (Nf ρ χ ζ)) := by
  set k : ℕ := m + (n + 2) with hk
  have hI1 := hS (2 * (k : ℤ)) χ hχ
  have hI2 := integrable_wt_inv n
  have hB := (hI1.add hI2).const_mul (1 / 2 : ℝ)
  refine hB.mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have : Continuous (Nf ρ χ) := continuous_Nf hρ hχ
    fun_prop
  · have hw := wt_pos ζ
    have hw1 := one_le_wt ζ
    set W := wt ζ with hW
    set u : ℝ := W ^ k with hu
    have hu0 : 0 < u := by positivity
    have hN := Nf_nonneg ρ χ ζ
    set y := Real.sqrt (Nf ρ χ ζ) with hy
    have hy2 : y ^ 2 = Nf ρ χ ζ := Real.sq_sqrt hN
    set x := ‖ζ‖ ^ m with hx
    have hx0 : 0 ≤ x := by positivity
    have hxW : x ≤ W ^ m := pow_le_pow_left₀ (norm_nonneg _) (norm_le_wt ζ) m
    have hzp : W ^ (2 * (k : ℤ)) = u ^ 2 := by
      rw [hu, ← pow_mul, ← zpow_natCast, mul_comm]; push_cast; rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    show x * y ≤ 1 / 2 * (W ^ (2 * (k : ℤ)) * Nf ρ χ ζ + (W ^ (2 * (n + 2)))⁻¹)
    rw [hzp, ← hy2]
    have h1 : x * y = (x / u) * (u * y) := by field_simp
    have h2 : (x / u) ^ 2 ≤ (W ^ (2 * (n + 2)))⁻¹ := by
      have hu2 : u ^ 2 = W ^ (2 * m) * W ^ (2 * (n + 2)) := by
        rw [hu, ← pow_mul, hk, ← pow_add]; congr 1; ring
      have hx2 : x ^ 2 ≤ W ^ (2 * m) := by
        calc x ^ 2 ≤ (W ^ m) ^ 2 := pow_le_pow_left₀ hx0 hxW 2
          _ = W ^ (2 * m) := by rw [← pow_mul, mul_comm]
      rw [div_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, hu2]
      exact mul_le_mul_of_nonneg_right hx2 (by positivity)
    nlinarith [sq_nonneg ((x / u) - (u * y)), sq_nonneg (x / u), sq_nonneg (u * y)]


section dens

variable {invβ : ℝ} {b : XS n → EuclideanSpace ℝ (Fin n)} {ρ : Measure (XS n)} {χ : XS n → ℝ}

lemma Gf_withDensity (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hχ : IsTest O χ)
    (hχ0 : ∀ p, 0 ≤ χ p) (ζ : XS n) :
    Gf (ρ.withDensity fun p => ENNReal.ofReal (χ p)) ζ = ⟨Cf ρ χ ζ, Sf ρ χ ζ⟩ := by
  unfold Gf
  rw [integral_withDensity_eq_integral_toReal_smul hχ.1.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  have hrw : (fun x : XS n => (ENNReal.ofReal (χ x)).toReal • Complex.exp (↑(ell ζ x) * Complex.I)) =
      fun x => (χ x : ℂ) * Complex.exp (↑(ell ζ x) * Complex.I) := by
    funext x; rw [ENNReal.toReal_ofReal (hχ0 x), Complex.real_smul]
  rw [hrw]
  have hint : Integrable (fun x : XS n => (χ x : ℂ) * Complex.exp (↑(ell ζ x) * Complex.I)) ρ := by
    refine (hχ.integrable hρ).norm.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp hχ.1.continuous |>.mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (ell ζ).continuous).mul
          continuous_const))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
  apply Complex.ext
  · have e := integral_re hint
    simp only [RCLike.re_to_complex] at e
    rw [← e]
    simp [Cf, Complex.exp_ofReal_mul_I_re]
  · have e := integral_im hint
    simp only [RCLike.im_to_complex] at e
    rw [← e]
    simp [Sf, Complex.exp_ofReal_mul_I_im]

lemma norm_Gf_withDensity (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hχ : IsTest O χ)
    (hχ0 : ∀ p, 0 ≤ χ p) (ζ : XS n) :
    ‖Gf (ρ.withDensity fun p => ENNReal.ofReal (χ p)) ζ‖ = Real.sqrt (Nf ρ χ ζ) := by
  rw [Gf_withDensity hρ hχ hχ0, Complex.norm_def, Complex.normSq_apply]
  unfold Nf
  congr 1
  simp only
  ring


theorem exists_local_density (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ) (hβ : 0 < invβ)
    (hχ : IsTest O χ) (hχ0 : ∀ p, 0 ≤ χ p)
    {χt : XS n → ℝ} (hχt : ContDiff ℝ smTop χt) (hχtc : HasCompactSupport χt)
    (hχt1 : ∀ p ∈ tsupport χ, χt p = 1) :
    ∃ h : XS n → ℝ, ContDiff ℝ smTop h ∧ (∀ p, 0 ≤ h p) ∧
      ρ.withDensity (fun p => ENNReal.ofReal (χ p)) =
        (volume : Measure (XS n)).withDensity (fun p => ENNReal.ofReal (h p)) := by
  have hint := hχ.integrable hρ
  have : IsFiniteMeasure (ρ.withDensity fun p => ENNReal.ofReal (χ p)) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  have hmom : ∀ m : ℕ, Integrable (fun ζ : XS n =>
      ‖ζ‖ ^ m * ‖Gf (ρ.withDensity fun p => ENNReal.ofReal (χ p)) ζ‖) := by
    intro m
    have := moment_integrable hρ (sobFin_all hO hb hρ hW hβ) hχ m
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [norm_Gf_withDensity hρ hχ hχ0]
  have hνK : (ρ.withDensity fun p => ENNReal.ofReal (χ p)) (tsupport χ)ᶜ = 0 := by
    rw [withDensity_apply _ (isClosed_tsupport χ).measurableSet.compl]
    rw [setLIntegral_congr_fun (isClosed_tsupport χ).measurableSet.compl (g := fun _ => 0) (fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx])]
    simp
  exact local_density _ hmom hχ.2.1 hνK hχt hχtc hχt1

end dens

end HRS.MC.CepP2
