import HRS.MS.CzSymAux2
import HRS.Commutator.Whole.XLIAux2
import HRS.MS.CzMikAux4

/-!
# SYM-LIN, part 3: the Fourier transform of `pvOdd d θ (fun u => u i) Z`
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Sym

open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.CZ.Mik

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- complexification of a real Schwartz function -/
def symlin_Cx (Z : 𝓢(𝔼, ℝ)) : 𝓢(𝔼, ℂ) := Z.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

lemma symlin_Cx_apply (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) : symlin_Cx Z x = ((Z x : ℝ) : ℂ) := rfl

/-- `z ↦ Z(x - z)` -/
def symlin_W (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) : 𝓢(𝔼, ℂ) :=
  SchwartzMap.compCLM ℝ (g := fun z : 𝔼 => x - z) (by fun_prop)
    ⟨1, 1 + ‖x‖, fun z => by
      have : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
        calc ‖z‖ = ‖x - (x - z)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - z‖ := norm_sub_le _ _
          _ = _ := by ring
      nlinarith [norm_nonneg x, norm_nonneg (x - z)]⟩ (symlin_Cx Z)

lemma symlin_W_apply (Z : 𝓢(𝔼, ℝ)) (x z : 𝔼) : symlin_W Z x z = ((Z (x - z) : ℝ) : ℂ) := rfl

/-- `G_x = 𝓕⁻ W_x`, so that `𝓕 G_x = W_x` -/
def symlin_G (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) : 𝓢(𝔼, ℂ) := 𝓕⁻ (symlin_W Z x)

lemma fourier_symlin_G (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    (𝓕 (⇑(symlin_G Z x)) : 𝔼 → ℂ) = ⇑(symlin_W Z x) := by
  have h : (𝓕 (symlin_G Z x) : 𝓢(𝔼, ℂ)) = symlin_W Z x :=
    FourierInvPair.fourier_fourierInv_eq _
  rw [← SchwartzMap.fourier_coe, h]

lemma symlin_G_apply (Z : 𝓢(𝔼, ℝ)) (x ξ : 𝔼) :
    symlin_G Z x ξ = Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) *
      𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ := by
  have h1 : (⇑(symlin_G Z x) : 𝔼 → ℂ) = 𝓕⁻ (⇑(symlin_W Z x)) := SchwartzMap.fourierInv_coe _
  rw [h1, Real.fourierInv_eq', Real.fourier_eq']
  have key : ∀ v : 𝔼, Complex.exp (↑(2 * Real.pi * inner ℝ v ξ) * Complex.I) • (symlin_W Z x) v =
      (fun z : 𝔼 => (Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) *
        Complex.exp (↑(-2 * Real.pi * inner ℝ z ξ) * Complex.I)) • ((Z z : ℝ) : ℂ)) (x - v) := by
    intro v
    simp only [symlin_W_apply, smul_eq_mul]
    rw [mul_assoc]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    push_cast
    ring
  have := integral_sub_left_eq_self
    (fun z : 𝔼 => (Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) *
        Complex.exp (↑(-2 * Real.pi * inner ℝ z ξ) * Complex.I)) • ((Z z : ℝ) : ℂ)) volume x
  simp_rw [key]
  rw [this]
  simp only [smul_eq_mul, mul_assoc]
  rw [integral_const_mul]

/-- the explicit constant `c_θ = π^{d/2} 2^{1-θ} Γ(1-θ/2) / Γ((d+θ)/2)` -/
def symlin_c (d : ℕ) (θ : ℝ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) * 2 ^ (1 - θ) * Real.Gamma (1 - θ / 2) / Real.Gamma (((d : ℝ) + θ) / 2)

/-- the multiplier `c_θ · (-(2π i) ξ_i) · |2π ξ|^{θ-2}` of the odd linear operator -/
def symlin_mult (d : ℕ) (θ : ℝ) (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((symlin_c d θ : ℝ) : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I) * ((ξ i : ℝ) : ℂ)) *
    (((2 * Real.pi * ‖ξ‖) ^ (θ - 2) : ℝ) : ℂ)

lemma symlin_mult_eq_m0 (d : ℕ) (θ : ℝ) (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) :
    symlin_mult d θ i ξ = symlin_m0 d θ i ξ := by
  have hπ := Real.pi_pos
  have hn := norm_nonneg ξ
  have h1 : (2 * Real.pi * ‖ξ‖) ^ (θ - 2) = (2 * Real.pi) ^ (θ - 2) * ‖ξ‖ ^ (θ - 2) :=
    Real.mul_rpow (by positivity) hn
  have h2 : symlin_c d θ * (2 * Real.pi) ^ (θ - 1) = symlin_C0 d θ := by
    unfold symlin_c symlin_C0
    have h3 : (2 * Real.pi) ^ (θ - 1) = 2 ^ (θ - 1) * Real.pi ^ (θ - 1) :=
      Real.mul_rpow (by norm_num) hπ.le
    have h4 : (2 : ℝ) ^ (1 - θ) * 2 ^ (θ - 1) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have h5 : Real.pi ^ ((d : ℝ) / 2 + θ - 1) = Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (θ - 1) := by
      rw [← Real.rpow_add hπ]; congr 1; ring
    rw [h3, h5]
    calc Real.pi ^ ((d : ℝ) / 2) * 2 ^ (1 - θ) * Real.Gamma (1 - θ / 2) / Real.Gamma (((d : ℝ) + θ) / 2) *
          (2 ^ (θ - 1) * Real.pi ^ (θ - 1))
        = (Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (θ - 1)) * Real.Gamma (1 - θ / 2) /
            Real.Gamma (((d : ℝ) + θ) / 2) * ((2 : ℝ) ^ (1 - θ) * 2 ^ (θ - 1)) := by ring
      _ = _ := by rw [h4]; ring
  have h6 : (2 * Real.pi) ^ (θ - 2) * (2 * Real.pi) = (2 * Real.pi) ^ (θ - 1) := by
    have : θ - 1 = (θ - 2) + 1 := by ring
    rw [this, Real.rpow_add (by positivity), Real.rpow_one]
  unfold symlin_mult symlin_m0
  rw [h1, ← h2, ← h6]
  push_cast
  ring

/-- pointwise formula: `pvOdd d θ (u_i) Z (x) = ∫ m(ξ) e^{2πi⟨x,ξ⟩} 𝓕Z(ξ) dξ` -/
theorem symlin_pvOdd_pointwise (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) =
      ∫ ξ : 𝔼, symlin_mult d θ i ξ * (Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) *
        𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ) := by
  rw [symlin_pvOdd_eq hd hθ0 hθ2 i Z x, ← integral_complex_ofReal]
  have hA := symlin_lemmaA hd hθ0 hθ2 i (symlin_G Z x)
  rw [fourier_symlin_G] at hA
  simp only [symlin_W_apply, sub_neg_eq_add] at hA
  have h1 : ∫ z : 𝔼, (((symlin_K d θ i z * ((Z (x - z) - Z (x + z)) / 2) : ℝ)) : ℂ) =
      ∫ z : 𝔼, ((symlin_K d θ i z : ℝ) : ℂ) * ((((Z (x - z) : ℝ) : ℂ) - ((Z (x + z) : ℝ) : ℂ)) / 2) := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    push_cast
    ring
  rw [h1, hA]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [symlin_G_apply, symlin_mult_eq_m0]

/-- `𝓕 Z` as a (complex) Schwartz function -/
def symlin_Zhat (Z : 𝓢(𝔼, ℝ)) : 𝓢(𝔼, ℂ) := 𝓕 (symlin_Cx Z)

/-- the transformed function `g = m 𝓕Z` -/
def symlin_g (d : ℕ) (θ : ℝ) (i : Fin d) (Z : 𝓢(EuclideanSpace ℝ (Fin d), ℝ))
    (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  symlin_mult d θ i ξ * 𝓕 (fun y : EuclideanSpace ℝ (Fin d) => ((Z y : ℝ) : ℂ)) ξ

lemma symlin_fourier_Z (Z : 𝓢(𝔼, ℝ)) :
    (𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) : 𝔼 → ℂ) = ⇑(symlin_Zhat Z) := by
  unfold symlin_Zhat
  rw [SchwartzMap.fourier_coe]
  rfl

lemma symlin_C0_nonneg (d : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) : 0 ≤ symlin_C0 d θ := by
  unfold symlin_C0
  have h1 : 0 < Real.Gamma (1 - θ / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (((d : ℝ) + θ) / 2) := Real.Gamma_pos_of_pos (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  positivity

lemma symlin_mult_norm_le {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d) (ξ : 𝔼) :
    ‖symlin_mult d θ i ξ‖ ≤ symlin_C0 d θ * ‖ξ‖ ^ (θ - 1) := by
  rw [symlin_mult_eq_m0]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [symlin_m0]
    exact mul_nonneg (symlin_C0_nonneg d hθ0 hθ2) (Real.rpow_nonneg le_rfl _)
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hC := symlin_C0_nonneg d hθ0 hθ2
    have hxi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
    unfold symlin_m0
    rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hC, abs_of_nonneg (Real.rpow_nonneg hn.le _)]
    calc symlin_C0 d θ * |ξ i| * ‖ξ‖ ^ (θ - 2) ≤ symlin_C0 d θ * ‖ξ‖ * ‖ξ‖ ^ (θ - 2) := by gcongr
      _ = symlin_C0 d θ * ‖ξ‖ ^ (θ - 1) := by
        have : θ - 1 = (θ - 2) + 1 := by ring
        rw [this, Real.rpow_add hn, Real.rpow_one]; ring

lemma symlin_g_measurable (θ : ℝ) (i : Fin d) (Z : 𝓢(𝔼, ℝ)) :
    AEStronglyMeasurable (symlin_g d θ i Z) volume := by
  have hm : Measurable (symlin_mult d θ i) := by
    unfold symlin_mult
    refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
    · exact measurable_const.mul (Complex.measurable_ofReal.comp
        ((EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous.measurable))
    · exact Complex.measurable_ofReal.comp ((measurable_const.mul measurable_norm).pow_const _)
  have hc : Continuous (𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ))) := by
    rw [symlin_fourier_Z]; exact (symlin_Zhat Z).continuous
  exact (hm.aestronglyMeasurable).mul hc.aestronglyMeasurable

lemma symlin_g_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) : Integrable (symlin_g d θ i Z) := by
  have hs : -(d : ℝ) < θ - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hI := symlin_integrable_rpow_mul hd hs 1 (by norm_num; linarith) (symlin_Zhat Z)
  refine (hI.const_mul (symlin_C0 d θ)).mono' (symlin_g_measurable θ i Z) (Eventually.of_forall fun ξ => ?_)
  unfold symlin_g
  rw [norm_mul, symlin_fourier_Z]
  calc ‖symlin_mult d θ i ξ‖ * ‖symlin_Zhat Z ξ‖
      ≤ (symlin_C0 d θ * ‖ξ‖ ^ (θ - 1)) * ‖symlin_Zhat Z ξ‖ := by
        gcongr; exact symlin_mult_norm_le hθ0 hθ2 i ξ
    _ = symlin_C0 d θ * (‖ξ‖ ^ (θ - 1) * ‖symlin_Zhat Z ξ‖) := by ring

lemma symlin_g_memLp (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (hθd : 2 < (d : ℝ) + 2 * θ)
    (i : Fin d) (Z : 𝓢(𝔼, ℝ)) : MemLp (symlin_g d θ i Z) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (symlin_g_measurable θ i Z)]
  have hs : -(d : ℝ) < 2 * θ - 2 := by linarith
  have hI := symlin_integrable_rpow_mul hd hs 2 (by push_cast; linarith) (symlin_Zhat Z)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x : 𝔼, ‖symlin_Zhat Z x‖ ≤ M :=
    ⟨(SchwartzMap.seminorm ℝ 0 0 (symlin_Zhat Z) : ℝ), fun x =>
      SchwartzMap.norm_le_seminorm ℝ (symlin_Zhat Z) x⟩
  have hC := symlin_C0_nonneg d hθ0 hθ2
  refine (hI.const_mul (symlin_C0 d θ ^ 2 * M)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (continuous_pow 2).comp_aestronglyMeasurable (symlin_g_measurable θ i Z).norm
  · rw [Real.norm_of_nonneg (by positivity)]
    unfold symlin_g
    rw [norm_mul, symlin_fourier_Z, mul_pow]
    have h1 : ‖symlin_mult d θ i ξ‖ ^ 2 ≤ (symlin_C0 d θ * ‖ξ‖ ^ (θ - 1)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (symlin_mult_norm_le hθ0 hθ2 i ξ) 2
    have h2 : ‖symlin_Zhat Z ξ‖ ^ 2 ≤ M * ‖symlin_Zhat Z ξ‖ := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (hM ξ) (norm_nonneg _)
    have h4 : (‖ξ‖ ^ (θ - 1)) ^ 2 = ‖ξ‖ ^ (2 * θ - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg ξ)]
      congr 1
      push_cast; ring
    have h3 : (symlin_C0 d θ * ‖ξ‖ ^ (θ - 1)) ^ 2 = symlin_C0 d θ ^ 2 * ‖ξ‖ ^ (2 * θ - 2) := by
      rw [mul_pow, h4]
    calc ‖symlin_mult d θ i ξ‖ ^ 2 * ‖symlin_Zhat Z ξ‖ ^ 2
        ≤ (symlin_C0 d θ ^ 2 * ‖ξ‖ ^ (2 * θ - 2)) * (M * ‖symlin_Zhat Z ξ‖) := by
          rw [← h3]; gcongr
      _ = symlin_C0 d θ ^ 2 * M * (‖ξ‖ ^ (2 * θ - 2) * ‖symlin_Zhat Z ξ‖) := by ring

lemma symlin_pvOdd_fourierInv (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) = 𝓕⁻ (symlin_g d θ i Z) x := by
  rw [symlin_pvOdd_pointwise hd hθ0 hθ2 i Z x, Real.fourierInv_eq']
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  simp only [symlin_g, smul_eq_mul]
  rw [real_inner_comm ξ x]
  have : Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℝ)) =
      Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) := by
    congr 1; push_cast; ring
  rw [this]
  ring

lemma symlin_fourierInv_continuous {g : 𝔼 → ℂ} (hg : Integrable g) : Continuous (𝓕⁻ g) := by
  have h : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hg
  have : (𝓕⁻ g : 𝔼 → ℂ) = fun x => 𝓕 g (-x) := funext fun x => Real.fourierInv_eq_fourier_neg g x
  rw [this]
  exact h.comp continuous_neg

lemma symlin_fourierInv_bdd {g : 𝔼 → ℂ} (hg : Integrable g) (x : 𝔼) : ‖𝓕⁻ g x‖ ≤ ∫ v, ‖g v‖ := by
  rw [Real.fourierInv_eq_fourier_neg]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- multiplication formula for the inverse transform -/
lemma symlin_integral_mul_fourierInv {g ψ : 𝔼 → ℂ} (hg : Integrable g) (hψ : Integrable ψ) :
    ∫ x, 𝓕⁻ g x * ψ x = ∫ ξ, g ξ * 𝓕⁻ ψ ξ := by
  have h1 : (𝓕⁻ ψ : 𝔼 → ℂ) = 𝓕 (fun x => ψ (-x)) := Real.fourierInv_eq_fourier_comp_neg ψ
  rw [h1]
  have h2 := integral_mul_fourier_eq g (fun x => ψ (-x)) hg hψ.comp_neg
  rw [h2]
  have h3 := integral_neg_eq_self (fun x : 𝔼 => 𝓕 g x * ψ (-x)) (volume : Measure 𝔼)
  rw [← h3]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [neg_neg]
  rw [Real.fourierInv_eq_fourier_neg]

theorem symlin_pairing (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) (ψ : 𝓢(𝔼, ℂ)) :
    Integrable (fun x : 𝔼 => ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) * ψ x) ∧
      ∫ x : 𝔼, ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) * ψ x =
        ∫ ξ : 𝔼, symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ * 𝓕⁻ (⇑ψ) ξ := by
  have hg := symlin_g_integrable hd hθ0 hθ2 i Z
  simp_rw [symlin_pvOdd_fourierInv hd hθ0 hθ2 i Z]
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' (g := fun x : 𝔼 => (∫ v, ‖symlin_g d θ i Z v‖) * ‖ψ x‖)
      (ψ.integrable.norm.const_mul _) ?_ (Eventually.of_forall fun x => ?_)
    · exact (symlin_fourierInv_continuous hg).aestronglyMeasurable.mul ψ.continuous.aestronglyMeasurable
    · rw [norm_mul]
      gcongr
      exact symlin_fourierInv_bdd hg x
  · rw [symlin_integral_mul_fourierInv hg ψ.integrable]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp [symlin_g]

theorem symlin_memLp (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (hθd : 2 < (d : ℝ) + 2 * θ)
    (i : Fin d) (Z : 𝓢(𝔼, ℝ)) :
    MemLp (HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z)) 2 volume ∧
      ∫⁻ x : 𝔼, ‖HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x‖ₑ ^ 2 =
        ∫⁻ ξ : 𝔼, ‖symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ‖ₑ ^ 2 := by
  have hg1 := symlin_g_integrable hd hθ0 hθ2 i Z
  have hg2 := symlin_g_memLp hd hθ0 hθ2 hθd i Z
  set f : 𝔼 → ℝ := HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) with hf
  have hfg : ∀ x, ((f x : ℝ) : ℂ) = 𝓕⁻ (symlin_g d θ i Z) x := fun x =>
    symlin_pvOdd_fourierInv hd hθ0 hθ2 i Z x
  -- Plancherel
  have hu1 : Integrable (fun ξ : 𝔼 => symlin_g d θ i Z (-ξ)) := hg1.comp_neg
  have hu2 : MemLp (fun ξ : 𝔼 => symlin_g d θ i Z (-ξ)) 2 volume :=
    hg2.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure 𝔼))
  have hP := plancherel_L1L2 hu1 hu2
  have hF : (𝓕 (fun ξ : 𝔼 => symlin_g d θ i Z (-ξ)) : 𝔼 → ℂ) = 𝓕⁻ (symlin_g d θ i Z) :=
    (Real.fourierInv_eq_fourier_comp_neg _).symm
  rw [hF] at hP
  have hneg : ∫⁻ ξ : 𝔼, ‖symlin_g d θ i Z (-ξ)‖ₑ ^ 2 = ∫⁻ ξ : 𝔼, ‖symlin_g d θ i Z ξ‖ₑ ^ 2 :=
    (Measure.measurePreserving_neg (volume : Measure 𝔼)).lintegral_comp_emb
      (MeasurableEquiv.neg 𝔼).measurableEmbedding (fun ξ => ‖symlin_g d θ i Z ξ‖ₑ ^ 2)
  have hlint : ∫⁻ x : 𝔼, ‖f x‖ₑ ^ 2 = ∫⁻ ξ : 𝔼, ‖symlin_g d θ i Z ξ‖ₑ ^ 2 := by
    rw [← hneg, ← hP]
    refine lintegral_congr fun x => ?_
    rw [← hfg x, ← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  refine ⟨?_, hlint⟩
  have hcont : Continuous f := by
    have : f = fun x => (𝓕⁻ (symlin_g d θ i Z) x).re := by
      funext x; rw [← hfg x, Complex.ofReal_re]
    rw [this]
    exact Complex.continuous_re.comp (symlin_fourierInv_continuous hg1)
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have h1 : ∫⁻ x : 𝔼, ‖‖f x‖ ^ 2‖ₑ = ∫⁻ x : 𝔼, ‖f x‖ₑ ^ 2 := by
    refine lintegral_congr fun x => ?_
    rw [enorm_pow, enorm_norm]
  rw [h1, hlint]
  have hI := ((memLp_two_iff_integrable_sq_norm (symlin_g_measurable θ i Z)).1 hg2).hasFiniteIntegral
  unfold HasFiniteIntegral at hI
  refine lt_of_le_of_lt (le_of_eq ?_) hI
  refine lintegral_congr fun x => ?_
  rw [enorm_pow, enorm_norm]

/-- **SYM-LIN, statement 1** (`pvOdd_linear_fourier`).  For `d ≥ 1`, `0 < θ < 2`, `i : Fin d` and a real
Schwartz function `Z`, the frozen `pvOdd d θ (fun u => u i) Z` (the p.v. of the odd kernel
`z_i/|z|^{d+θ}`) has the Fourier representation with multiplier
`m(ξ) = c_θ · (-(2π i) ξ_i) · |2πξ|^{θ-2}`, `c_θ = π^{d/2} 2^{1-θ} Γ(1-θ/2)/Γ((d+θ)/2)` (`symlin_mult`):

* `(a)` pointwise, for every `x`: `pvOdd Z x = 𝓕⁻(m 𝓕Z)(x)` (the limit defining `pvOdd` exists);
* `(b)` `m 𝓕Z` is integrable;
* `(c)` for every complex Schwartz `ψ`: `pvOdd Z · ψ` is integrable and
  `∫ pvOdd Z · ψ = ∫ m 𝓕Z · 𝓕⁻ψ` (pairing identity, the repo style of `IsFracDerivRep`);
* `(d)` if `2 < d + 2θ` (automatic for `d ≥ 2`, and for `d = 1` exactly `θ > 1/2`): `pvOdd Z ∈ L²` and
  `‖pvOdd Z‖_2² = ‖m 𝓕Z‖_2²` (Plancherel).

**Adjustment of the frozen sketch** (documented as required): the sketch claimed `MemLp 2` for all
`0 < θ < 2`, `d ≥ 1`.  This is false for `d = 1`, `θ ≤ 1/2` (e.g. `Z` with `𝓕Z(0) ≠ 0`: `m 𝓕Z ~ |ξ|^{θ-1}` is
not in `L²` near `0`, equivalently `pvOdd Z(x) ~ c |x|^{-θ} ∉ L²(ℝ)`); hence `(d)` carries the hypothesis
`2 < d + 2θ`.  Parts `(a)`-`(c)` hold for all `0 < θ < 2`, `d ≥ 1`. -/
theorem pvOdd_linear_fourier (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (Z : 𝓢(𝔼, ℝ)) :
    (∀ x : 𝔼, ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) =
      𝓕⁻ (fun ξ : 𝔼 => symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ) x) ∧
    Integrable (fun ξ : 𝔼 => symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ) ∧
    (∀ ψ : 𝓢(𝔼, ℂ),
      Integrable (fun x : 𝔼 => ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) * ψ x) ∧
      ∫ x : 𝔼, ((HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x : ℝ) : ℂ) * ψ x =
        ∫ ξ : 𝔼, symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ * 𝓕⁻ (⇑ψ) ξ) ∧
    (2 < (d : ℝ) + 2 * θ →
      MemLp (HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z)) 2 volume ∧
      ∫⁻ x : 𝔼, ‖HRS.Whole.AppendixA.pvOdd d θ (fun u => u i) (⇑Z) x‖ₑ ^ 2 =
        ∫⁻ ξ : 𝔼, ‖symlin_mult d θ i ξ * 𝓕 (fun y : 𝔼 => ((Z y : ℝ) : ℂ)) ξ‖ₑ ^ 2) :=
  ⟨fun x => symlin_pvOdd_fourierInv hd hθ0 hθ2 i Z x, symlin_g_integrable hd hθ0 hθ2 i Z,
    fun ψ => symlin_pairing hd hθ0 hθ2 i Z ψ, fun h => symlin_memLp hd hθ0 hθ2 h i Z⟩

/-- `c_θ` at `d = 1`, `θ = 1` is `π` -/
lemma symlin_c_hilbert : symlin_c 1 1 = Real.pi := by
  unfold symlin_c
  have h1 : Real.pi ^ (((1 : ℕ) : ℝ) / 2) = Real.sqrt Real.pi := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have h2 : Real.Gamma (1 - (1 : ℝ) / 2) = Real.sqrt Real.pi := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.Gamma_one_half_eq]
  have h3 : Real.Gamma ((((1 : ℕ) : ℝ) + 1) / 2) = 1 := by
    rw [show (((1 : ℕ) : ℝ) + 1) / 2 = 1 by norm_num, Real.Gamma_one]
  rw [h1, h2, h3]
  simp [Real.mul_self_sqrt Real.pi_pos.le]

/-- The Hilbert-transform symbol: for `d = 1`, `θ = 1` the multiplier is `-iπ sgn(ξ)`. -/
lemma symlin_mult_hilbert (ξ : EuclideanSpace ℝ (Fin 1)) :
    symlin_mult 1 1 0 ξ = -((Real.pi : ℂ) * Complex.I * ((SignType.sign (ξ 0) : ℝ) : ℂ)) := by
  have hn : ‖ξ‖ = |ξ 0| := by
    simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  unfold symlin_mult
  rw [symlin_c_hilbert, hn]
  by_cases h0 : ξ 0 = 0
  · simp [h0]
  · have ha : 0 < |ξ 0| := abs_pos.2 h0
    have hp := Real.pi_pos
    have e : (2 * Real.pi * |ξ 0|) ^ (1 - 2 : ℝ) = (2 * Real.pi * |ξ 0|)⁻¹ := by
      rw [show (1 - 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    rw [e]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have : |ξ 0| = -ξ 0 := abs_of_neg hneg
      rw [this]
      have hs : (SignType.sign (ξ 0) : ℝ) = -1 := by simp [sign_neg hneg]
      rw [hs]
      have : (ξ 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
      push_cast
      field_simp
    · rw [abs_of_pos hpos]
      have hs : (SignType.sign (ξ 0) : ℝ) = 1 := by simp [sign_pos hpos]
      rw [hs]
      have : (ξ 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
      push_cast
      field_simp

/-- **SYM-LIN, corollary** (`pvOdd_hilbert`, feeds ROT): the p.v. `∫ Z(x-z)/z dz` (frozen `pvOdd 1 1 (u ↦ u_0)`)
is the Hilbert transform `Z ↦ 𝓕⁻(-iπ sgn(ξ) 𝓕Z)`, in `L²`, with the pairing identity. -/
theorem pvOdd_hilbert (Z : 𝓢(EuclideanSpace ℝ (Fin 1), ℝ)) :
    (∀ x : EuclideanSpace ℝ (Fin 1),
      ((HRS.Whole.AppendixA.pvOdd 1 1 (fun u => u 0) (⇑Z) x : ℝ) : ℂ) =
        𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin 1) =>
          (-((Real.pi : ℂ) * Complex.I * ((SignType.sign (ξ 0) : ℝ) : ℂ))) *
            𝓕 (fun y : EuclideanSpace ℝ (Fin 1) => ((Z y : ℝ) : ℂ)) ξ) x) ∧
    (∀ ψ : 𝓢(EuclideanSpace ℝ (Fin 1), ℂ),
      ∫ x : EuclideanSpace ℝ (Fin 1), ((HRS.Whole.AppendixA.pvOdd 1 1 (fun u => u 0) (⇑Z) x : ℝ) : ℂ) * ψ x =
        ∫ ξ : EuclideanSpace ℝ (Fin 1), (-((Real.pi : ℂ) * Complex.I * ((SignType.sign (ξ 0) : ℝ) : ℂ))) *
          𝓕 (fun y : EuclideanSpace ℝ (Fin 1) => ((Z y : ℝ) : ℂ)) ξ * 𝓕⁻ (⇑ψ) ξ) ∧
    MemLp (HRS.Whole.AppendixA.pvOdd 1 1 (fun u => u 0) (⇑Z)) 2 volume := by
  obtain ⟨ha, -, hc, hd⟩ := pvOdd_linear_fourier (d := 1) le_rfl (θ := 1) one_pos one_lt_two 0 Z
  refine ⟨fun x => ?_, fun ψ => ?_, (hd (by norm_num)).1⟩
  · rw [ha x]
    simp only [symlin_mult_hilbert]
  · rw [(hc ψ).2]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [symlin_mult_hilbert]

/-! ### Statement 2: Mikhlin bounds of the symbols (`mik1_IsMikhlin`, order `d+1`)

`isMikhlin_riesz` (`ξ_i/|ξ|`), `isMikhlin_riesz2` (`ξ_i ξ_j/|ξ|²`), `isMikhlin_fracBessel`
(`|ξ|^r (1+4π²|ξ|²)^{-r/2}`, `r > 0`) and `isMikhlin_pvOdd_bessel`
(`ξ_i |ξ|^{β-1} (1+4π²|ξ|²)^{-β/2}`, `0 < β < 1`).  The constant `A` depends on `d` (and `β`, `r`) only, and is
uniform in the indices.  The class is `HRS.CZ.Mik.mik1_IsMikhlin` of the merged MIK-1 (smoothness off `0` and
`‖D^i m(ξ)‖ ≤ A |ξ|^{-i}` for `i ≤ d+1`).  Homogeneous symbols: `mik1_isMikhlin_of_homog`.  The Bessel factor:
scaling to the unit sphere; for `|ξ| ≤ 1` the Leibniz formula for `|ξ|^r · (1+4π²|ξ|²)^{-r/2}` (the second factor
is globally smooth), for `|ξ| ≥ 1` the composition `Φ(|ξ|^{-2})`, `Φ(t) = (4π² + t)^{-r/2}`. -/

lemma symlin_mikhlin_mono {A B : ℝ} {m : 𝔼 → ℂ} (hAB : A ≤ B) (hm : mik1_IsMikhlin d A m) :
    mik1_IsMikhlin d B m := by
  refine ⟨hm.1, fun i hi ξ hξ => ?_⟩
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  exact (hm.2 i hi ξ hξ).trans (by gcongr)

lemma symlin_mikhlin_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {f g : 𝔼 → ℂ}
    (hf : mik1_IsMikhlin d A f) (hg : mik1_IsMikhlin d B g) :
    mik1_IsMikhlin d (2 ^ (d + 1) * A * B) (fun ξ => f ξ * g ξ) := by
  refine ⟨fun ξ hξ => (hf.1 ξ hξ).mul (hg.1 ξ hξ), fun n hn ξ hξ => ?_⟩
  have hs : IsOpen ({0} : Set 𝔼)ᶜ := isOpen_compl_singleton
  have hfs : ContDiffOn ℝ ∞ f ({0} : Set 𝔼)ᶜ := fun x hx => (hf.1 x hx).contDiffWithinAt
  have hgs : ContDiffOn ℝ ∞ g ({0} : Set 𝔼)ᶜ := fun x hx => (hg.1 x hx).contDiffWithinAt
  have hle : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have h1 := norm_iteratedFDerivWithin_mul_le hfs hgs hs.uniqueDiffOn hξ hle
  have e : (fun ξ => f ξ * g ξ) = (fun y : 𝔼 => f y * g y) := rfl
  rw [iteratedFDerivWithin_of_isOpen n hs hξ] at h1
  have h2 : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
      ‖iteratedFDerivWithin ℝ j f ({0}ᶜ : Set 𝔼) ξ‖ *
      ‖iteratedFDerivWithin ℝ (n - j) g ({0}ᶜ : Set 𝔼) ξ‖ ≤
      (n.choose j : ℝ) * (A * ‖ξ‖ ^ (-(j : ℝ))) * (B * ‖ξ‖ ^ (-((n - j : ℕ) : ℝ))) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [iteratedFDerivWithin_of_isOpen j hs hξ, iteratedFDerivWithin_of_isOpen (n - j) hs hξ]
    have hb1 := hf.2 j (by omega) ξ hξ
    have hb2 := hg.2 (n - j) (by omega) ξ hξ
    gcongr
  have h3 : ∀ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (A * ‖ξ‖ ^ (-(j : ℝ))) *
      (B * ‖ξ‖ ^ (-((n - j : ℕ) : ℝ))) = (n.choose j : ℝ) * (A * B) * ‖ξ‖ ^ (-(n : ℝ)) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have : ‖ξ‖ ^ (-(j : ℝ)) * ‖ξ‖ ^ (-((n - j : ℕ) : ℝ)) = ‖ξ‖ ^ (-(n : ℝ)) := by
      rw [← Real.rpow_add hξn]
      congr 1
      rw [Nat.cast_sub hj']
      ring
    calc (n.choose j : ℝ) * (A * ‖ξ‖ ^ (-(j : ℝ))) * (B * ‖ξ‖ ^ (-((n - j : ℕ) : ℝ)))
        = (n.choose j : ℝ) * (A * B) * (‖ξ‖ ^ (-(j : ℝ)) * ‖ξ‖ ^ (-((n - j : ℕ) : ℝ))) := by ring
      _ = _ := by rw [this]
  calc ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖
      = ‖iteratedFDeriv ℝ n (fun y : 𝔼 => f y * g y) ξ‖ := rfl
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (A * ‖ξ‖ ^ (-(j : ℝ))) *
          (B * ‖ξ‖ ^ (-((n - j : ℕ) : ℝ))) :=
        h1.trans (Finset.sum_le_sum h2)
    _ = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)) * (A * B) * ‖ξ‖ ^ (-(n : ℝ)) := by
        rw [Finset.sum_congr rfl h3, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ 2 ^ (d + 1) * A * B * ‖ξ‖ ^ (-(n : ℝ)) := by
        have hsum : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [hsum]
        have h2n : (2 : ℝ) ^ n ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hpos : 0 ≤ ‖ξ‖ ^ (-(n : ℝ)) := Real.rpow_nonneg hξn.le _
        calc (2 : ℝ) ^ n * (A * B) * ‖ξ‖ ^ (-(n : ℝ)) ≤ 2 ^ (d + 1) * (A * B) * ‖ξ‖ ^ (-(n : ℝ)) := by
              gcongr
          _ = _ := by ring

lemma symlin_mikhlin_uniform {ι : Type*} [Fintype ι] {m : ι → 𝔼 → ℂ}
    (h : ∀ a, ∃ A : ℝ, 0 ≤ A ∧ mik1_IsMikhlin d A (m a)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a, mik1_IsMikhlin d A (m a) := by
  choose A hA0 hA using h
  refine ⟨∑ a, A a, Finset.sum_nonneg fun a _ => hA0 a, fun a => ?_⟩
  exact symlin_mikhlin_mono (Finset.single_le_sum (f := A) (fun b _ => hA0 b) (Finset.mem_univ a)) (hA a)

/-- Riesz symbols `ξ_i/|ξ|` are Mikhlin (constant depends on `d` only) -/
theorem isMikhlin_riesz (d : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i : Fin d,
      mik1_IsMikhlin d A (fun ξ : EuclideanSpace ℝ (Fin d) => ((ξ i / ‖ξ‖ : ℝ) : ℂ)) := by
  refine symlin_mikhlin_uniform (fun i => ?_)
  refine mik1_isMikhlin_of_homog (fun η hη => ?_) (fun c hc y => ?_)
  · have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have h1 : ContDiffAt ℝ ∞ (fun η : EuclideanSpace ℝ (Fin d) => (η i : ℝ)) η :=
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun η : EuclideanSpace ℝ (Fin d) => ‖η‖) η := contDiffAt_norm ℝ hη
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp η (h1.div h2 hn.ne')
  · have hc0 : c ≠ 0 := hc.ne'
    simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg hc.le]
    congr 1
    rw [mul_div_mul_left _ _ hc0]

/-- the double Riesz symbols `ξ_i ξ_j/|ξ|²` are Mikhlin -/
theorem isMikhlin_riesz2 (d : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i j : Fin d,
      mik1_IsMikhlin d A (fun ξ : EuclideanSpace ℝ (Fin d) => ((ξ i * ξ j / ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
  refine symlin_mikhlin_uniform (m := fun (p : Fin d × Fin d) (ξ : EuclideanSpace ℝ (Fin d)) =>
    ((ξ p.1 * ξ p.2 / ‖ξ‖ ^ 2 : ℝ) : ℂ)) (fun p => ?_) |>.imp fun A hA => ⟨hA.1, fun i j => hA.2 (i, j)⟩
  refine mik1_isMikhlin_of_homog (fun η hη => ?_) (fun c hc y => ?_)
  · have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
    have h1 : ContDiffAt ℝ ∞ (fun η : EuclideanSpace ℝ (Fin d) => (η p.1 : ℝ)) η :=
      ((EuclideanSpace.proj p.1 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff).contDiffAt
    have h1' : ContDiffAt ℝ ∞ (fun η : EuclideanSpace ℝ (Fin d) => (η p.2 : ℝ)) η :=
      ((EuclideanSpace.proj p.2 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun η : EuclideanSpace ℝ (Fin d) => ‖η‖ ^ 2) η :=
      (contDiffAt_norm ℝ hη).pow 2
    exact (Complex.ofRealCLM.contDiff.contDiffAt).comp η ((h1.mul h1').div h2 (pow_pos hn 2).ne')
  · have hc0 : c ≠ 0 := hc.ne'
    simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg hc.le]
    congr 1
    rw [show c * y p.1 * (c * y p.2) = c ^ 2 * (y p.1 * y p.2) by ring, mul_pow,
      mul_div_mul_left _ _ (pow_ne_zero 2 hc0)]

/-- uniform bound of the `k`-th derivative on the unit sphere of a function smooth off `0` -/
lemma symlin_sph_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : 𝔼 → F} (hg : ContDiffOn ℝ ∞ g ({0} : Set 𝔼)ᶜ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Metric.sphere (0 : 𝔼) 1, ‖iteratedFDeriv ℝ k g x‖ ≤ K := by
  have hs : IsOpen ({0} : Set 𝔼)ᶜ := isOpen_compl_singleton
  have h1 : ContinuousOn (iteratedFDerivWithin ℝ k g ({0} : Set 𝔼)ᶜ) ({0} : Set 𝔼)ᶜ :=
    hg.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs.uniqueDiffOn
  have h2 : ContinuousOn (iteratedFDeriv ℝ k g) ({0} : Set 𝔼)ᶜ :=
    h1.congr (iteratedFDerivWithin_of_isOpen k hs).symm
  have hsub : Metric.sphere (0 : 𝔼) 1 ⊆ ({0} : Set 𝔼)ᶜ := fun x hx => by
    intro h0
    rw [Set.mem_singleton_iff] at h0
    subst h0
    simp at hx
  have hcont : ContinuousOn (fun x => ‖iteratedFDeriv ℝ k g x‖) (Metric.sphere (0 : 𝔼) 1) :=
    (h2.mono hsub).norm
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : 𝔼) 1).exists_bound_of_continuousOn hcont
  refine ⟨max K 0, le_max_right _ _, fun x hx => ?_⟩
  have := hK x hx
  rw [norm_norm] at this
  exact this.trans (le_max_left _ _)

/-- scaling: `‖D^k g (ρ w) ‖ ≤ ρ^{-k} ‖D^k (g(ρ ·)) (w)‖` -/
lemma symlin_scale_up {g : 𝔼 → ℂ} (hg : ContDiffOn ℝ ∞ g ({0} : Set 𝔼)ᶜ) {ρ : ℝ} (hρ : 0 < ρ)
    {w : 𝔼} (hw : w ≠ 0) (k : ℕ) :
    ‖iteratedFDeriv ℝ k g (ρ • w)‖ ≤ (ρ⁻¹) ^ k * ‖iteratedFDeriv ℝ k (fun y : 𝔼 => g (ρ • y)) w‖ := by
  have hs : IsOpen ({0} : Set 𝔼)ᶜ := isOpen_compl_singleton
  set g' : 𝔼 → ℂ := fun y => g (ρ • y) with hg'
  set ℓ : 𝔼 →L[ℝ] 𝔼 := ρ⁻¹ • ContinuousLinearMap.id ℝ 𝔼 with hℓ
  have hℓy : ∀ y, ℓ y = ρ⁻¹ • y := fun y => by simp [hℓ]
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hgg' : g = g' ∘ ℓ := by
    funext y; simp [hg', hℓy, smul_smul, hρ0]
  have hg's : ContDiffOn ℝ ∞ g' ({0} : Set 𝔼)ᶜ := by
    intro y hy
    have h0 : ρ • y ∈ ({0} : Set 𝔼)ᶜ := by simpa [hρ0] using hy
    exact ((hg.contDiffAt (hs.mem_nhds h0)).comp y
      (contDiff_const_smul ρ).contDiffAt).contDiffWithinAt
  have hsg : IsOpen (ℓ ⁻¹' ({0} : Set 𝔼)ᶜ) := hs.preimage ℓ.continuous
  have hℓw : ℓ (ρ • w) ∈ ({0} : Set 𝔼)ᶜ := by
    rw [hℓy, smul_smul, inv_mul_cancel₀ hρ0, one_smul]; exact hw
  have hle : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have h1 := ℓ.iteratedFDerivWithin_comp_right hg's hs.uniqueDiffOn hsg.uniqueDiffOn hℓw hle
  have hmem : ρ • w ∈ ℓ ⁻¹' ({0} : Set 𝔼)ᶜ := hℓw
  rw [← hgg', iteratedFDerivWithin_of_isOpen k hsg hmem,
    iteratedFDerivWithin_of_isOpen k hs hℓw] at h1
  have hℓw' : ℓ (ρ • w) = w := by rw [hℓy, smul_smul, inv_mul_cancel₀ hρ0, one_smul]
  rw [hℓw'] at h1
  rw [h1]
  have hℓn : ‖ℓ‖ ≤ ρ⁻¹ := by
    calc ‖ℓ‖ = ‖ρ⁻¹‖ * ‖ContinuousLinearMap.id ℝ 𝔼‖ := norm_smul _ _
      _ ≤ ‖ρ⁻¹‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = ρ⁻¹ := by rw [mul_one, Real.norm_of_nonneg (inv_nonneg.2 hρ.le)]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g' w) (fun _ : Fin k => ℓ)
  have h3 : ∏ _j : Fin k, ‖ℓ‖ ≤ (ρ⁻¹) ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hℓn _
  calc _ ≤ ‖iteratedFDeriv ℝ k g' w‖ * ∏ _j : Fin k, ‖ℓ‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ k g' w‖ * (ρ⁻¹) ^ k := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = _ := by rw [mul_comm]

/-- the symbol `|ξ|^r (1+4π²|ξ|²)^{-r/2}` -/
def symlin_sigma (d : ℕ) (r : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((‖ξ‖ ^ r * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-r / 2) : ℝ) : ℂ)

def symlin_P (d : ℕ) (r : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ := ((‖ξ‖ ^ r : ℝ) : ℂ)

def symlin_R (d : ℕ) (r : ℝ) (ζ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  (((1 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2) ^ (-r / 2) : ℝ) : ℂ)

lemma symlin_pos_base (ζ : 𝔼) : 0 < 1 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2 := by positivity

lemma symlin_R_contDiff (r : ℝ) : ContDiff ℝ ∞ (symlin_R d r) := by
  unfold symlin_R
  have h1 : ContDiff ℝ ∞ (fun ζ : 𝔼 => 1 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have h2 : ContDiff ℝ ∞ (fun ζ : 𝔼 => (1 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2) ^ (-r / 2)) :=
    h1.rpow_const_of_ne (fun ζ => (symlin_pos_base ζ).ne')
  exact Complex.ofRealCLM.contDiff.comp h2

lemma symlin_P_contDiffOn (r : ℝ) : ContDiffOn ℝ ∞ (symlin_P d r) ({0} : Set 𝔼)ᶜ := by
  intro y hy
  have h : ContDiffAt ℝ ∞ (fun ξ : 𝔼 => ‖ξ‖ ^ r) y :=
    (contDiffAt_norm ℝ hy).rpow_const_of_ne (norm_ne_zero_iff.2 hy)
  exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp y h).contDiffWithinAt

lemma symlin_sigma_contDiffAt (r : ℝ) {y : 𝔼} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (symlin_sigma d r) y := by
  have h1 : ContDiffAt ℝ ∞ (fun ξ : 𝔼 => ‖ξ‖ ^ r) y :=
    (contDiffAt_norm ℝ hy).rpow_const_of_ne (norm_ne_zero_iff.2 hy)
  have h2 : ContDiffAt ℝ ∞ (fun ζ : 𝔼 => (1 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2) ^ (-r / 2)) y := by
    have hh : ContDiff ℝ ∞ (fun ζ : 𝔼 => (1 + 4 * Real.pi ^ 2 * ‖ζ‖ ^ 2) ^ (-r / 2)) :=
      (contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))).rpow_const_of_ne
        (fun ζ : 𝔼 => (symlin_pos_base ζ).ne')
    exact hh.contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt).comp y (h1.mul h2)

lemma symlin_sigma_small (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (y : 𝔼) :
    symlin_sigma d r (ρ • y) = ((ρ ^ r : ℝ) : ℂ) • (symlin_P d r y * symlin_R d r (ρ • y)) := by
  unfold symlin_sigma symlin_P symlin_R
  rw [norm_smul, Real.norm_of_nonneg hρ.le, Real.mul_rpow hρ.le (norm_nonneg _)]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

lemma symlin_iter_comp_smul_le {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) (x : 𝔼) :
    ‖iteratedFDeriv ℝ m (fun y : 𝔼 => f (ρ • y)) x‖ ≤ ρ ^ m * ‖iteratedFDeriv ℝ m f (ρ • x)‖ := by
  set ℓ : 𝔼 →L[ℝ] 𝔼 := ρ • ContinuousLinearMap.id ℝ 𝔼 with hℓ
  have hℓy : ∀ y, ℓ y = ρ • y := fun y => by simp [hℓ]
  have e : (fun y : 𝔼 => f (ρ • y)) = f ∘ ℓ := by funext y; simp [hℓy]
  rw [e, ℓ.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top), hℓy]
  have hℓn : ‖ℓ‖ ≤ ρ := by
    calc ‖ℓ‖ = ‖ρ‖ * ‖ContinuousLinearMap.id ℝ 𝔼‖ := norm_smul _ _
      _ ≤ ‖ρ‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = ρ := by rw [mul_one, Real.norm_of_nonneg hρ.le]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ m f (ρ • x)) (fun _ : Fin m => ℓ)
  have h3 : ∏ _j : Fin m, ‖ℓ‖ ≤ ρ ^ m := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hℓn _
  calc _ ≤ ‖iteratedFDeriv ℝ m f (ρ • x)‖ * ∏ _j : Fin m, ‖ℓ‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ m f (ρ • x)‖ * ρ ^ m := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = _ := by rw [mul_comm]

lemma symlin_case_small (r : ℝ) (hr : 0 < r) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ η : 𝔼, ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ k (fun y : 𝔼 => symlin_sigma d r (ρ • y)) η‖ ≤ B := by
  have hKex : ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Metric.sphere (0 : 𝔼) 1,
      ‖iteratedFDeriv ℝ j (symlin_P d r) x‖ ≤ K := fun j => symlin_sph_bound (symlin_P_contDiffOn r) j
  choose K hK0 hK using hKex
  have hMex : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ : 𝔼, ‖ζ‖ ≤ 1 →
      ‖iteratedFDeriv ℝ m (symlin_R d r) ζ‖ ≤ M := by
    intro m
    have hc : Continuous (iteratedFDeriv ℝ m (symlin_R d r)) :=
      (symlin_R_contDiff r).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : 𝔼) 1).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max M 0, le_max_right _ _, fun ζ hζ => ?_⟩
    exact (hM ζ (by simpa using hζ)).trans (le_max_left _ _)
  choose M hM0 hM using hMex
  refine ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * K j * M (k - j), ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by positivity) (hK0 j)) (hM0 _)
  intro ρ hρ hρ1 η hη
  have hs : IsOpen ({0} : Set 𝔼)ᶜ := isOpen_compl_singleton
  have hη0 : η ≠ 0 := by
    intro h; rw [h] at hη; simp at hη
  have hηs : η ∈ ({0} : Set 𝔼)ᶜ := hη0
  have e : (fun y : 𝔼 => symlin_sigma d r (ρ • y)) =
      fun y : 𝔼 => ((ρ ^ r : ℝ) : ℂ) • (symlin_P d r y * symlin_R d r (ρ • y)) := by
    funext y; exact symlin_sigma_small r hρ y
  have hPat : ContDiffAt ℝ ∞ (symlin_P d r) η := (symlin_P_contDiffOn r).contDiffAt (hs.mem_nhds hηs)
  have hRρ : ContDiff ℝ ∞ (fun y : 𝔼 => symlin_R d r (ρ • y)) :=
    (symlin_R_contDiff r).comp (contDiff_const_smul ρ)
  have hFat : ContDiffAt ℝ ∞ (fun y : 𝔼 => symlin_P d r y * symlin_R d r (ρ • y)) η :=
    hPat.mul hRρ.contDiffAt
  rw [e, iteratedFDeriv_const_smul_apply' (hFat.of_le (by exact_mod_cast le_top)), norm_smul]
  have hρr : ‖((ρ ^ r : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hρ.le _)]
    exact Real.rpow_le_one hρ.le hρ1 hr.le
  have hle : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hPs := symlin_P_contDiffOn (d := d) r
  have hRs : ContDiffOn ℝ ∞ (fun y : 𝔼 => symlin_R d r (ρ • y)) ({0} : Set 𝔼)ᶜ := hRρ.contDiffOn
  have h1 := norm_iteratedFDerivWithin_mul_le hPs hRs hs.uniqueDiffOn hηs hle (n := k)
  rw [iteratedFDerivWithin_of_isOpen k hs hηs] at h1
  have h2 : ∀ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      ‖iteratedFDerivWithin ℝ j (symlin_P d r) ({0} : Set 𝔼)ᶜ η‖ *
      ‖iteratedFDerivWithin ℝ (k - j) (fun y : 𝔼 => symlin_R d r (ρ • y)) ({0} : Set 𝔼)ᶜ η‖ ≤
      (k.choose j : ℝ) * K j * M (k - j) := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hs hηs, iteratedFDerivWithin_of_isOpen (k - j) hs hηs]
    have hb1 := hK j η (by simpa using hη)
    have hb2 := symlin_iter_comp_smul_le (symlin_R_contDiff r) hρ (k - j) η
    have hb3 := hM (k - j) (ρ • η) (by rw [norm_smul, hη, Real.norm_of_nonneg hρ.le]; linarith)
    have hρp : ρ ^ (k - j) ≤ 1 := pow_le_one₀ hρ.le hρ1
    have hb4 : ‖iteratedFDeriv ℝ (k - j) (fun y : 𝔼 => symlin_R d r (ρ • y)) η‖ ≤ M (k - j) := by
      calc _ ≤ ρ ^ (k - j) * ‖iteratedFDeriv ℝ (k - j) (symlin_R d r) (ρ • η)‖ := hb2
        _ ≤ 1 * M (k - j) := by gcongr
        _ = _ := one_mul _
    have hKj := hK0 j
    gcongr
  calc ‖((ρ ^ r : ℝ) : ℂ)‖ * ‖iteratedFDeriv ℝ k (fun y : 𝔼 => symlin_P d r y * symlin_R d r (ρ • y)) η‖
      ≤ 1 * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * K j * M (k - j) := by
        gcongr
        exact h1.trans (Finset.sum_le_sum h2)
    _ = _ := one_mul _

lemma symlin_sigma_real_inv (r : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ r * (1 + 4 * Real.pi ^ 2 * x ^ 2) ^ (-r / 2) = (4 * Real.pi ^ 2 + (x ^ 2)⁻¹) ^ (-r / 2) := by
  have hx2 : 0 < x ^ 2 := by positivity
  have hb : 0 < 1 + 4 * Real.pi ^ 2 * x ^ 2 := by positivity
  have h : 4 * Real.pi ^ 2 + (x ^ 2)⁻¹ = (1 + 4 * Real.pi ^ 2 * x ^ 2) / x ^ 2 := by
    field_simp
    ring
  rw [h, Real.div_rpow hb.le hx2.le]
  have h2 : (x ^ 2) ^ (-r / 2) = (x ^ r)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_neg hx.le]
    congr 1; push_cast; ring
  rw [h2, div_inv_eq_mul]
  ring

/-- the outer function `Φ(t) = (4π² + t)^{-r/2}` -/
def symlin_Phi (r : ℝ) (t : ℝ) : ℂ := (((4 * Real.pi ^ 2 + t) ^ (-r / 2) : ℝ) : ℂ)

lemma symlin_sigma_large (r : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {y : 𝔼} (hy : y ≠ 0) :
    symlin_sigma d r (ρ • y) = symlin_Phi r ((ρ⁻¹) ^ 2 * (‖y‖ ^ 2)⁻¹) := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  unfold symlin_sigma symlin_Phi
  rw [norm_smul, Real.norm_of_nonneg hρ.le]
  congr 1
  rw [symlin_sigma_real_inv r (mul_pos hρ hn)]
  congr 2
  rw [mul_pow, mul_inv, inv_pow]

lemma symlin_Phi_contDiffOn (r : ℝ) : ContDiffOn ℝ ∞ (symlin_Phi r) (Set.Ioo (-(4 * Real.pi ^ 2) / 2) 5) := by
  intro t ht
  have hpos : 0 < 4 * Real.pi ^ 2 + t := by
    have := ht.1
    have : 0 < Real.pi ^ 2 := by positivity
    linarith
  have h : ContDiffAt ℝ ∞ (fun t : ℝ => (4 * Real.pi ^ 2 + t) ^ (-r / 2)) t :=
    (contDiffAt_const.add contDiffAt_id).rpow_const_of_ne hpos.ne'
  exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp t h).contDiffWithinAt

lemma symlin_case_large (r : ℝ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ η : 𝔼, ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ k (fun y : 𝔼 => symlin_sigma d r (ρ • y)) η‖ ≤ B := by
  have hc : 0 < 4 * Real.pi ^ 2 := by positivity
  set T : Set ℝ := Set.Ioo (-(4 * Real.pi ^ 2) / 2) 5 with hT
  have hTo : IsOpen T := isOpen_Ioo
  have hΦ := symlin_Phi_contDiffOn r
  -- constants for Φ
  have hCex : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i (symlin_Phi r) T u‖ ≤ C := by
    intro i
    have hcont : ContinuousOn (iteratedFDerivWithin ℝ i (symlin_Phi r) T) T :=
      hΦ.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hTo.uniqueDiffOn
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ T := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (hcont.mono hsub).norm
    refine ⟨max C 0, le_max_right _ _, fun u hu => ?_⟩
    have := hC u hu
    rw [norm_norm] at this
    exact this.trans (le_max_left _ _)
  choose C hC0 hC using hCex
  -- constants for F0 = (‖y‖²)⁻¹
  have hF0 : ContDiffOn ℝ ∞ (fun y : 𝔼 => (‖y‖ ^ 2)⁻¹) ({0} : Set 𝔼)ᶜ := by
    intro y hy
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have h1 : ContDiffAt ℝ ∞ (fun y : 𝔼 => ‖y‖ ^ 2) y := (contDiffAt_norm ℝ hy).pow 2
    exact (h1.inv (pow_ne_zero 2 hn)).contDiffWithinAt
  have hKex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Metric.sphere (0 : 𝔼) 1,
      ‖iteratedFDeriv ℝ i (fun y : 𝔼 => (‖y‖ ^ 2)⁻¹) x‖ ≤ K := fun i => symlin_sph_bound hF0 i
  choose K hK0 hK using hKex
  set D : ℝ := 1 + ∑ i ∈ Finset.range (k + 1), K i with hD
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), K i := Finset.sum_nonneg fun i _ => hK0 i
    linarith
  set Cs : ℝ := ∑ i ∈ Finset.range (k + 1), C i with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨(k.factorial : ℝ) * Cs * D ^ k, by positivity, ?_⟩
  intro ρ hρ η hη
  have hρ0 : 0 < ρ := by linarith
  have hη0 : η ≠ 0 := by intro h; rw [h] at hη; simp at hη
  set μ : ℝ := ρ⁻¹ with hμ
  have hμ0 : 0 < μ := inv_pos.2 hρ0
  have hμ1 : μ ≤ 1 := inv_le_one_of_one_le₀ hρ
  set S : Set 𝔼 := {y | 1 / 2 < ‖y‖ ∧ ‖y‖ < 2} with hS
  have hSo : IsOpen S := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hηS : η ∈ S := by rw [hS]; simp [hη]; norm_num
  set f : 𝔼 → ℝ := fun y => μ ^ 2 * (‖y‖ ^ 2)⁻¹ with hf
  have hfsm : ContDiffOn ℝ ∞ f S := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h; have := hy.1; rw [h] at this; simp at this; linarith
    exact (((hF0 y hy0).contDiffAt (isOpen_compl_singleton.mem_nhds hy0)).const_smul (μ ^ 2)).contDiffWithinAt
  have hmaps : Set.MapsTo f S T := by
    intro y hy
    have h1 : 1 / 2 < ‖y‖ := hy.1
    have h2 : 0 < ‖y‖ ^ 2 := by positivity
    have h3 : 1 / 4 < ‖y‖ ^ 2 := by nlinarith
    have h4 : (‖y‖ ^ 2)⁻¹ < 4 := by
      rw [inv_lt_comm₀ h2 (by norm_num)]; linarith
    have h5 : 0 < (‖y‖ ^ 2)⁻¹ := inv_pos.2 h2
    have h6 : μ ^ 2 ≤ 1 := pow_le_one₀ hμ0.le hμ1
    refine ⟨?_, ?_⟩
    · have : 0 < μ ^ 2 * (‖y‖ ^ 2)⁻¹ := by positivity
      linarith
    · calc μ ^ 2 * (‖y‖ ^ 2)⁻¹ ≤ 1 * (‖y‖ ^ 2)⁻¹ := by gcongr
        _ < 5 := by linarith
  have hfη : f η ∈ Set.Icc (0 : ℝ) 1 := by
    have : f η = μ ^ 2 := by simp [hf, hη]
    rw [this]
    exact ⟨by positivity, pow_le_one₀ hμ0.le hμ1⟩
  have hle : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hcomp := norm_iteratedFDerivWithin_comp_le (n := k) hΦ hfsm hle hTo.uniqueDiffOn
    hSo.uniqueDiffOn hmaps hηS (C := Cs) (D := D)
    (fun i hi => by
      refine (hC i _ hfη).trans ?_
      exact Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (by omega)))
    (fun i hi1 hik => by
      rw [iteratedFDerivWithin_of_isOpen i hSo hηS]
      have hfe : f = fun y : 𝔼 => (μ ^ 2) • (fun y : 𝔼 => (‖y‖ ^ 2)⁻¹) y := by
        funext y; simp [hf]
      have hat : ContDiffAt ℝ ∞ (fun y : 𝔼 => (‖y‖ ^ 2)⁻¹) η :=
        (hF0 η hη0).contDiffAt (isOpen_compl_singleton.mem_nhds hη0)
      rw [hfe, iteratedFDeriv_const_smul_apply' (hat.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_of_nonneg (by positivity)]
      have hK' := hK i η (by simpa using hη)
      have hKD : K i ≤ D := by
        have := Finset.single_le_sum (f := K) (fun j _ => hK0 j) (Finset.mem_range.2 (by omega : i < k + 1))
        linarith
      have hμ2 : μ ^ 2 ≤ 1 := pow_le_one₀ hμ0.le hμ1
      calc μ ^ 2 * ‖iteratedFDeriv ℝ i (fun y : 𝔼 => (‖y‖ ^ 2)⁻¹) η‖ ≤ 1 * K i := by gcongr
        _ ≤ D := by linarith
        _ ≤ D ^ i := le_self_pow₀ hD1 (by omega))
  have heq : (fun y : 𝔼 => symlin_sigma d r (ρ • y)) =ᶠ[𝓝 η] (symlin_Phi r ∘ f) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hη0] with y hy
    rw [symlin_sigma_large r hρ0 hy]
    rfl
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen k hSo hηS]
  exact hcomp

/-- the symbols `|ξ|^r (1+4π²|ξ|²)^{-r/2}`, `r > 0`, are Mikhlin -/
theorem isMikhlin_fracBessel (d : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ mik1_IsMikhlin d A
      (fun ξ : EuclideanSpace ℝ (Fin d) =>
        ((‖ξ‖ ^ r * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-r / 2) : ℝ) : ℂ)) := by
  have hex : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 0 < ρ → ∀ η : EuclideanSpace ℝ (Fin d), ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun y : EuclideanSpace ℝ (Fin d) => symlin_sigma d r (ρ • y)) η‖ ≤ B := by
    intro i
    obtain ⟨B1, hB1, h1⟩ := symlin_case_small (d := d) r hr i
    obtain ⟨B2, hB2, h2⟩ := symlin_case_large (d := d) r i
    refine ⟨max B1 B2, le_max_of_le_left hB1, fun ρ hρ η hη => ?_⟩
    rcases le_total ρ 1 with h | h
    · exact (h1 ρ hρ h η hη).trans (le_max_left _ _)
    · exact (h2 ρ h η hη).trans (le_max_right _ _)
  choose B hB0 hB using hex
  refine ⟨∑ i ∈ Finset.range (d + 2), B i, Finset.sum_nonneg fun i _ => hB0 i, ?_, ?_⟩
  · intro ξ hξ
    exact symlin_sigma_contDiffAt r hξ
  · intro i hi ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hσ : ContDiffOn ℝ ∞ (symlin_sigma d r) ({0} : Set (EuclideanSpace ℝ (Fin d)))ᶜ :=
      fun y hy => (symlin_sigma_contDiffAt r hy).contDiffWithinAt
    set w : EuclideanSpace ℝ (Fin d) := ‖ξ‖⁻¹ • ξ with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hn.ne'
    have hw0 : w ≠ 0 := by intro h; rw [h] at hwn; simp at hwn
    have hξw : ξ = ‖ξ‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hs := symlin_scale_up hσ hn hw0 i
    rw [← hξw] at hs
    have hb := hB i ‖ξ‖ hn w hwn
    have hKA : B i ≤ ∑ j ∈ Finset.range (d + 2), B j :=
      Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_range.2 (by omega))
    have hpow : ‖ξ‖ ^ (-(i : ℝ)) = (‖ξ‖⁻¹) ^ i := by
      rw [Real.rpow_neg hn.le, Real.rpow_natCast, inv_pow]
    rw [hpow]
    calc _ ≤ (‖ξ‖⁻¹) ^ i * ‖iteratedFDeriv ℝ i (fun y => symlin_sigma d r (‖ξ‖ • y)) w‖ := hs
      _ ≤ (‖ξ‖⁻¹) ^ i * B i := by gcongr
      _ ≤ (‖ξ‖⁻¹) ^ i * ∑ j ∈ Finset.range (d + 2), B j := by gcongr
      _ = _ := by ring

/-- the symbols `ξ_i |ξ|^{β-1} (1+4π²|ξ|²)^{-β/2}` (the symbol of `pvOdd_θ ∘ Bessel^{-(θ-1)}` with
`β = θ - 1 ∈ (0,1)`; only `β > 0` is used) are Mikhlin, with a constant depending on `d, β` only -/
theorem isMikhlin_pvOdd_bessel (d : ℕ) {β : ℝ} (hβ : 0 < β) (_hβ1 : β < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i : Fin d, mik1_IsMikhlin d A
      (fun ξ : EuclideanSpace ℝ (Fin d) =>
        ((ξ i * ‖ξ‖ ^ (β - 1) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-β / 2) : ℝ) : ℂ)) := by
  obtain ⟨A1, hA1, h1⟩ := isMikhlin_riesz d
  obtain ⟨A2, hA2, h2⟩ := isMikhlin_fracBessel d hβ
  refine ⟨2 ^ (d + 1) * A1 * A2, by positivity, fun i => ?_⟩
  have hm := symlin_mikhlin_mul hA1 hA2 (h1 i) h2
  have e : (fun ξ : EuclideanSpace ℝ (Fin d) =>
      ((ξ i * ‖ξ‖ ^ (β - 1) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-β / 2) : ℝ) : ℂ)) =
      fun ξ : EuclideanSpace ℝ (Fin d) => ((ξ i / ‖ξ‖ : ℝ) : ℂ) *
        ((‖ξ‖ ^ β * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-β / 2) : ℝ) : ℂ) := by
    funext ξ
    by_cases hξ : ξ = 0
    · subst hξ; simp
    · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      rw [← Complex.ofReal_mul, Real.rpow_sub_one hn.ne']
      congr 1
      field_simp
  rw [e]
  exact hm

end HRS.CZ.Sym
