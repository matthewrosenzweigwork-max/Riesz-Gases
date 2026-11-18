import HRS.PDE.MeanFieldTransient
import HRS.PDE.MeanFieldInputs
import HRS.PDE.Hadamard
import HRS.PDE.Convention
import HRS.PDE.MeanFieldPairing

/-!
# The nonlinear transient, assembly (package MF-01, packet P10b)

From the mild solution of `MeanFieldTransient.lean`: the amplitude `A(ε)`, the `C^j` remainder
bounds, smoothness and positivity of `ρ^t = toFun (rhoC k f t)`, the weak-solution clause and the
assembled statement `nonlinear_transient_main`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFTransient

open HRS

variable {d : ℕ} {s β : ℝ} {k : Lattice d}

/-! ### Convolution of the dominating sequence -/

/-- `T_n = ∑_m S_{n-m} S_m`. -/
def Tconv (S : ℤ → ℝ) (n : ℤ) : ℝ := ∑' m : ℤ, S (n - m) * S m

theorem Tconv_facts {S : ℤ → ℝ} (hS : Summable S) (hS0 : ∀ n, 0 ≤ S n) :
    (∀ n, Summable fun m : ℤ => S (n - m) * S m) ∧ (∀ n, 0 ≤ Tconv S n) ∧ Summable (Tconv S) ∧
      ∑' n, Tconv S n ≤ (∑' n, S n) ^ 2 := by
  have := conv_kernel_le (a := fun n m => S (n - m) * S m) (K := 1) hS hS (fun n => hS0 n)
    (fun n => hS0 n) (fun n m => mul_nonneg (hS0 _) (hS0 _)) (fun n m => by simp)
  refine ⟨this.1, fun n => tsum_nonneg fun m => mul_nonneg (hS0 _) (hS0 _), this.2.1, ?_⟩
  have h2 := this.2.2
  simp only [one_mul] at h2
  unfold Tconv
  nlinarith [h2]


/-! ### Bounds on the nonlinear forcing -/

theorem exp_two_omg (a σ : ℝ) : Real.exp (-(2 * a * σ)) = (Real.exp (a * σ))⁻¹ * (Real.exp (a * σ))⁻¹ := by
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1; ring

theorem Fnl_wt_term (h : Hyp d s β k) {f : ℤ → ℝ → ℝ} {S : ℤ → ℝ}
    (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n)
    {n : ℤ} (hn : n ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) (m : ℤ) :
    wt n * (|(m : ℝ)| * rieszCoeff d s (m • k) * |f (n - m) σ| * |f m σ|) ≤
      (2 * |(n : ℝ)| * rieszCoeff d s k * Real.exp (-(2 * omg d s β k * σ))) *
        (S (n - m) * S m) := by
  set E := Real.exp (omg d s β k * σ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h1 := hb (n - m) σ hσ
  have h2 := hb m σ hσ
  have h1' : wt (n - m) * |f (n - m) σ| ≤ S (n - m) * E⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hE0]; linarith
  have h2' : wt m * |f m σ| ≤ S m * E⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hE0]; linarith
  have hk := wt_mul_abs_le hn m
  have hg := rieszCoeff_zsmul_le h m
  have hg0 := rieszCoeff_nonneg' h (m • k)
  have hgk := rieszCoeff_nonneg' h k
  have ha := abs_nonneg (f (n - m) σ)
  have hb' := abs_nonneg (f m σ)
  have hu := mul_nonneg (wt_pos (n - m)).le ha
  have hv := mul_nonneg (wt_pos m).le hb'
  have hS1 : 0 ≤ S (n - m) * E⁻¹ := hu.trans h1'
  rw [exp_two_omg]
  calc wt n * (|(m : ℝ)| * rieszCoeff d s (m • k) * |f (n - m) σ| * |f m σ|)
      = (wt n * |(m : ℝ)|) * rieszCoeff d s (m • k) * (|f (n - m) σ| * |f m σ|) := by ring
    _ ≤ (2 * |(n : ℝ)| * (wt (n - m) * wt m)) * rieszCoeff d s k * (|f (n - m) σ| * |f m σ|) := by
        have := wt_pos (n - m)
        have := wt_pos m
        gcongr
    _ = (2 * |(n : ℝ)| * rieszCoeff d s k) * ((wt (n - m) * |f (n - m) σ|) * (wt m * |f m σ|)) := by
        ring
    _ ≤ (2 * |(n : ℝ)| * rieszCoeff d s k) * ((S (n - m) * E⁻¹) * (S m * E⁻¹)) := by
        gcongr
    _ = _ := by ring

theorem Fnl_wt_le (h : Hyp d s β k) {f : ℤ → ℝ → ℝ} {S : ℤ → ℝ} (hS : Summable S)
    (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n)
    {n : ℤ} (hn : n ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    wt n * |Fnl d s k (fun j => f j σ) (fun j => f j σ) n| ≤
      2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 * Real.exp (-(2 * omg d s β k * σ)) *
        Tconv S n := by
  have hS0 : ∀ n, 0 ≤ S n := fun n => by
    have := hb n 0 le_rfl
    have h1 := wt_pos n
    have h2 := Real.exp_pos (omg d s β k * 0)
    exact (mul_nonneg (mul_nonneg h1.le h2.le) (abs_nonneg _)).trans this
  obtain ⟨hsum, -, -, -⟩ := Tconv_facts hS hS0
  set K : ℝ := 2 * |(n : ℝ)| * rieszCoeff d s k * Real.exp (-(2 * omg d s β k * σ)) with hK
  have hK0 : 0 ≤ K := by
    have := rieszCoeff_nonneg' h k
    positivity
  set a : ℤ → ℝ := fun m => |(m : ℝ)| * rieszCoeff d s (m • k) * |f (n - m) σ| * |f m σ| with ha
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    have := rieszCoeff_nonneg' h (m • k)
    simp only [ha]; positivity
  have hwa : ∀ m, wt n * a m ≤ K * (S (n - m) * S m) := fun m => Fnl_wt_term h hb hn hσ m
  have hwn := wt_pos n
  have hsa : Summable a := by
    refine Summable.of_nonneg_of_le ha0 (fun m => ?_) ((hsum n).mul_left (K / wt n))
    rw [div_mul_eq_mul_div, le_div_iff₀ hwn]
    linarith [hwa m]
  have hFnl : Fnl d s k (fun j => f j σ) (fun j => f j σ) n =
      -(qk k ^ 2) * (n : ℝ) * ∑' m : ℤ, (m : ℝ) * rieszCoeff d s (m • k) * f (n - m) σ * f m σ := rfl
  have hle : |∑' m : ℤ, (m : ℝ) * rieszCoeff d s (m • k) * f (n - m) σ * f m σ| ≤ ∑' m, a m := by
    have habs : ∀ m : ℤ, |(m : ℝ) * rieszCoeff d s (m • k) * f (n - m) σ * f m σ| = a m := fun m => by
      simp only [ha]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (rieszCoeff_nonneg' h (m • k))]
    have : Summable fun m : ℤ => |(m : ℝ) * rieszCoeff d s (m • k) * f (n - m) σ * f m σ| :=
      hsa.congr fun m => (habs m).symm
    have h3 := norm_tsum_le_tsum_norm (f := fun m : ℤ => (m : ℝ) * rieszCoeff d s (m • k) *
      f (n - m) σ * f m σ) (by simpa [Real.norm_eq_abs] using this)
    simp only [Real.norm_eq_abs] at h3
    rw [tsum_congr habs] at h3
    exact h3
  have hq : 0 ≤ qk k ^ 2 := sq_nonneg _
  rw [hFnl, abs_mul, abs_mul, abs_neg, abs_of_nonneg hq]
  have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  calc wt n * (qk k ^ 2 * |(n : ℝ)| * |∑' m : ℤ, (m : ℝ) * rieszCoeff d s (m • k) * f (n - m) σ * f m σ|)
      ≤ wt n * (qk k ^ 2 * |(n : ℝ)| * ∑' m, a m) := by gcongr
    _ = qk k ^ 2 * |(n : ℝ)| * ∑' m, wt n * a m := by rw [tsum_mul_left]; ring
    _ ≤ qk k ^ 2 * |(n : ℝ)| * ∑' m, K * (S (n - m) * S m) :=
        mul_le_mul_of_nonneg_left
          (Summable.tsum_le_tsum hwa (hsa.mul_left _) ((hsum n).mul_left K)) (by positivity)
    _ = qk k ^ 2 * |(n : ℝ)| * (K * Tconv S n) := by rw [tsum_mul_left]; rfl
    _ = 2 * qk k ^ 2 * rieszCoeff d s k * (|(n : ℝ)| ^ 2) * Real.exp (-(2 * omg d s β k * σ)) *
          Tconv S n := by simp only [hK]; ring
    _ = _ := by rw [hsq]


/-! ### Duhamel estimates -/

theorem duhamel_integral_le {l c C t : ℝ} (hlc : c < l) (hC : 0 ≤ C) (_ht : 0 ≤ t) :
    ∫ σ in (0 : ℝ)..t, Real.exp (-(l * (t - σ))) * (C * Real.exp (-(c * σ))) ≤
      C * Real.exp (-(c * t)) / (l - c) := by
  have hlc' : l - c ≠ 0 := (sub_pos.mpr hlc).ne'
  have hp : 0 < l - c := sub_pos.mpr hlc
  have e1 : ∀ σ : ℝ, Real.exp (-(l * (t - σ))) * (C * Real.exp (-(c * σ))) =
      (C * Real.exp (-(l * t))) * Real.exp ((l - c) * σ) := fun σ => by
    have : Real.exp (-(l * (t - σ))) * Real.exp (-(c * σ)) =
        Real.exp (-(l * t)) * Real.exp ((l - c) * σ) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc _ = C * (Real.exp (-(l * (t - σ))) * Real.exp (-(c * σ))) := by ring
      _ = _ := by rw [this]; ring
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_real _ _ hlc']
  have e2 : Real.exp (-(l * t)) * Real.exp ((l - c) * t) = Real.exp (-(c * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : 0 < Real.exp (-(l * t)) := Real.exp_pos _
  calc C * Real.exp (-(l * t)) * ((Real.exp ((l - c) * t) - 1) / (l - c))
      = C * (Real.exp (-(l * t)) * Real.exp ((l - c) * t) - Real.exp (-(l * t))) / (l - c) := by
        field_simp
    _ ≤ C * Real.exp (-(c * t)) / (l - c) := by
        rw [e2]
        apply div_le_div_of_nonneg_right _ hp.le
        nlinarith

/-- Duhamel formula for a mode with no initial datum: `w(n) |f_n(t)| ≤ K T_n e^{-2ωt}`. -/
theorem wt_f_le_of_ge_two (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {S : ℤ → ℝ} (hS : Summable S)
    (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n)
    {n : ℤ} (hn : 2 ≤ |n|) {t : ℝ} (ht : 0 ≤ t) :
    wt n * |f n t| ≤ (6 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k) * Tconv S n *
      Real.exp (-(2 * omg d s β k * t)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hS0 : ∀ n, 0 ≤ S n := fun n => by
    have := hb n 0 le_rfl
    exact (mul_nonneg (mul_nonneg (wt_pos n).le (Real.exp_pos _).le) (abs_nonneg _)).trans this
  obtain ⟨-, hT0, -, -⟩ := Tconv_facts hS hS0
  have hl := lam_pos h
  have hg := rieszCoeff_nonneg' h k
  have hq : 0 ≤ qk k ^ 2 := sq_nonneg _
  have hn1 : n ≠ 1 ∧ n ≠ -1 := by
    constructor <;> rintro rfl <;> simp at hn
  have hf0 : f0 ε n = 0 := by simp [f0, hn1.1, hn1.2]
  have hm := hf.mild n t ht
  rw [hf0, zero_mul, zero_add] at hm
  have hn2 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : ((2 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn
    have h4 : (2 : ℝ) ≤ |(n : ℝ)| := by simpa using this
    nlinarith [sq_abs (n : ℝ)]
  have hlam := lam_ge h n
  have hω : omg d s β k = (3 / 4) * transientRate d s β k := rfl
  have hgap : (n : ℝ) ^ 2 * transientRate d s β k / 3 ≤ lam d s β k n - 2 * omg d s β k := by
    rw [hω]; nlinarith
  have hgap0 : 0 < lam d s β k n - 2 * omg d s β k := by
    have : 0 < (n : ℝ) ^ 2 * transientRate d s β k / 3 := by positivity
    linarith
  set Φ : ℝ := 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 * Tconv S n with hΦ
  have hΦ0 : 0 ≤ Φ := by rw [hΦ]; have := hT0 n; positivity
  have hw := wt_pos n
  -- pointwise bound on the forcing
  have hF : ∀ σ ∈ Set.uIcc (0 : ℝ) t, |Fnl d s k (fun j => f j σ) (fun j => f j σ) n| ≤
      (Φ / wt n) * Real.exp (-(2 * omg d s β k * σ)) := by
    intro σ hσ
    rw [Set.uIcc_of_le ht] at hσ
    have := Fnl_wt_le h hS hb hn0 hσ.1
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    calc _ = wt n * |Fnl d s k (fun j => f j σ) (fun j => f j σ) n| := by ring
      _ ≤ _ := this
      _ = _ := by simp only [hΦ]; ring
  have hint : |∫ σ in (0 : ℝ)..t, Real.exp (-(lam d s β k n * (t - σ))) *
      Fnl d s k (fun j => f j σ) (fun j => f j σ) n| ≤
      ∫ σ in (0 : ℝ)..t, Real.exp (-(lam d s β k n * (t - σ))) *
        ((Φ / wt n) * Real.exp (-(2 * omg d s β k * σ))) := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall fun σ hσ => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hF σ (by rw [Set.uIcc_of_le ht]; exact ⟨hσ.1.le, hσ.2⟩))
        (Real.exp_pos _).le
    · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hdu := duhamel_integral_le (l := lam d s β k n) (c := 2 * omg d s β k) (C := Φ / wt n)
    (t := t) (by linarith) (div_nonneg hΦ0 (wt_pos n).le) ht
  have hfin : |f n t| ≤ Φ / wt n * Real.exp (-(2 * omg d s β k * t)) /
      (lam d s β k n - 2 * omg d s β k) := by
    rw [hm]; exact hint.trans hdu
  have hq3 : Φ / (lam d s β k n - 2 * omg d s β k) ≤
      (6 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k) * Tconv S n := by
    rw [div_le_iff₀ hgap0]
    have hT := hT0 n
    have : (6 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k) * Tconv S n *
        (lam d s β k n - 2 * omg d s β k) ≥ (6 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k) *
          Tconv S n * ((n : ℝ) ^ 2 * transientRate d s β k / 3) :=
      mul_le_mul_of_nonneg_left hgap (mul_nonneg (by positivity) hT)
    have e : (6 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k) * Tconv S n *
        ((n : ℝ) ^ 2 * transientRate d s β k / 3) = Φ := by
      simp only [hΦ]; field_simp; ring
    linarith
  calc wt n * |f n t| ≤ wt n * (Φ / wt n * Real.exp (-(2 * omg d s β k * t)) /
      (lam d s β k n - 2 * omg d s β k)) := mul_le_mul_of_nonneg_left hfin hw.le
    _ = (Φ / (lam d s β k n - 2 * omg d s β k)) * Real.exp (-(2 * omg d s β k * t)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hq3 (Real.exp_pos _).le


/-! ### The amplitude -/

theorem f0_one (ε : ℝ) : f0 ε 1 = ε / Real.sqrt 2 := by simp [f0]

/-- The forcing of the first mode: `|F_1(σ)| ≤ c₁ e^{-2ωσ}`. -/
theorem Fnl_one_le (h : Hyp d s β k) {f : ℤ → ℝ → ℝ} {S : ℤ → ℝ} (hS : Summable S)
    (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    |Fnl d s k (fun j => f j σ) (fun j => f j σ) 1| ≤
      (2 * qk k ^ 2 * rieszCoeff d s k * Tconv S 1 / wt 1) * Real.exp (-(2 * omg d s β k * σ)) := by
  have := Fnl_wt_le h hS hb (n := 1) one_ne_zero hσ
  have hw := wt_pos 1
  rw [div_mul_eq_mul_div, le_div_iff₀ hw]
  simp only [Int.cast_one, one_pow, mul_one] at this
  calc _ = wt 1 * |Fnl d s k (fun j => f j σ) (fun j => f j σ) 1| := by ring
    _ ≤ _ := this
    _ = _ := by ring

theorem amplitude_exists (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {S : ℤ → ℝ} (hS : Summable S)
    (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n) :
    ∃ a : ℝ, |a| ≤ (2 * qk k ^ 2 * rieszCoeff d s k * Tconv S 1 / wt 1) * (2 / transientRate d s β k) ∧
      ∀ t, 0 ≤ t → |Real.exp (transientRate d s β k * t) * f 1 t - ε / Real.sqrt 2 - a| ≤
        (2 * qk k ^ 2 * rieszCoeff d s k * Tconv S 1 / wt 1) * (2 / transientRate d s β k) *
          Real.exp (-(transientRate d s β k / 2) * t) := by
  have hS0 : ∀ n, 0 ≤ S n := fun n => by
    have := hb n 0 le_rfl
    exact (mul_nonneg (mul_nonneg (wt_pos n).le (Real.exp_pos _).le) (abs_nonneg _)).trans this
  obtain ⟨-, hT0, -, -⟩ := Tconv_facts hS hS0
  have hl := lam_pos h
  set lm := transientRate d s β k with hlm
  have hg := rieszCoeff_nonneg' h k
  set c₁ : ℝ := 2 * qk k ^ 2 * rieszCoeff d s k * Tconv S 1 / wt 1 with hc₁
  have hc₁0 : 0 ≤ c₁ := by
    have := hT0 1; have := wt_pos 1; rw [hc₁]; positivity
  set F : ℝ → ℝ := fun σ => Fnl d s k (fun j => f j σ) (fun j => f j σ) 1 with hF
  set G : ℝ → ℝ := fun σ => Real.exp (lm * σ) * F σ with hG
  have hGc : Continuous G := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (hf.contF 1)
  have hω : 2 * omg d s β k = 3 / 2 * lm := by simp only [omg, hlm]; ring
  have hGb : ∀ σ, 0 ≤ σ → |G σ| ≤ c₁ * Real.exp (-(lm / 2) * σ) := by
    intro σ hσ
    have h1 := Fnl_one_le h hS hb hσ
    rw [hω] at h1
    simp only [hG, hF]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (lm * σ) * |Fnl d s k (fun j => f j σ) (fun j => f j σ) 1|
        ≤ Real.exp (lm * σ) * (c₁ * Real.exp (-(3 / 2 * lm * σ))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = c₁ * Real.exp (-(lm / 2) * σ) := by
          have : Real.exp (lm * σ) * Real.exp (-(3 / 2 * lm * σ)) = Real.exp (-(lm / 2) * σ) := by
            rw [← Real.exp_add]; congr 1; ring
          calc _ = c₁ * (Real.exp (lm * σ) * Real.exp (-(3 / 2 * lm * σ))) := by ring
            _ = _ := by rw [this]
  have hneg : -(lm / 2) < 0 := by linarith
  have hexpI : ∀ c : ℝ, IntegrableOn (fun σ => c₁ * Real.exp (-(lm / 2) * σ)) (Set.Ioi c) :=
    fun c => Integrable.const_mul (integrableOn_exp_mul_Ioi hneg c) c₁
  have hGI : ∀ c : ℝ, 0 ≤ c → IntegrableOn G (Set.Ioi c) := fun c hc => by
    refine Integrable.mono' (hexpI c) hGc.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    rw [Real.norm_eq_abs]
    exact hGb σ (hc.trans (le_of_lt hσ))
  have hint_tail : ∀ c : ℝ, 0 ≤ c → |∫ σ in Set.Ioi c, G σ| ≤
      c₁ * (2 / lm) * Real.exp (-(lm / 2) * c) := by
    intro c hc
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hexpI c) ?_).trans ?_
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun σ hσ => ?_
      rw [Real.norm_eq_abs]
      exact hGb σ (hc.trans (le_of_lt hσ))
    · rw [integral_const_mul, integral_exp_mul_Ioi hneg c]
      have : -Real.exp (-(lm / 2) * c) / (-(lm / 2)) = 2 / lm * Real.exp (-(lm / 2) * c) := by
        field_simp
      rw [this]; ring_nf; exact le_rfl
  refine ⟨∫ σ in Set.Ioi 0, G σ, ?_, ?_⟩
  · have := hint_tail 0 le_rfl
    simpa using this
  · intro t ht
    have hm := hf.mild 1 t ht
    rw [f0_one, lam_one, ← hlm] at hm
    have hsplit : ∫ σ in Set.Ioi (0 : ℝ), G σ = (∫ σ in (0 : ℝ)..t, G σ) + ∫ σ in Set.Ioi t, G σ := by
      rw [intervalIntegral.integral_of_le ht, ← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi, Set.Ioc_union_Ioi_eq_Ioi ht]
      · exact (hGI 0 le_rfl).mono_set Set.Ioc_subset_Ioi_self
      · exact hGI t ht
    have e1 : Real.exp (lm * t) * (ε / Real.sqrt 2 * Real.exp (-(lm * t))) = ε / Real.sqrt 2 := by
      rw [mul_left_comm, ← Real.exp_add]; simp
    have e2 : Real.exp (lm * t) * ∫ σ in (0 : ℝ)..t, Real.exp (-(lm * (t - σ))) * F σ =
        ∫ σ in (0 : ℝ)..t, G σ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      simp only [hG]
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    have hmul : Real.exp (lm * t) * f 1 t = ε / Real.sqrt 2 + ∫ σ in (0 : ℝ)..t, G σ := by
      rw [hm, mul_add, e1]
      congr 1
    have : Real.exp (lm * t) * f 1 t - ε / Real.sqrt 2 - ∫ σ in Set.Ioi (0 : ℝ), G σ =
        -∫ σ in Set.Ioi t, G σ := by
      rw [hmul, hsplit]; ring
    rw [this, abs_neg]
    exact hint_tail t ht


/-! ### The weighted remainder -/

theorem MildSol.f_zero {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f) {t : ℝ} (ht : 0 ≤ t) :
    f 0 t = 0 := by
  have hm := hf.mild 0 t ht
  have h1 : f0 ε 0 = 0 := by simp [f0]
  have h2 : ∀ σ : ℝ, Fnl d s k (fun j => f j σ) (fun j => f j σ) 0 = 0 := fun σ => by
    simp [Fnl]
  simp [h1, h2] at hm
  exact hm

/-- The constant of the amplitude bound, `32 q² ĝ(k) w(1)`. -/
def Cc (d : ℕ) (s : ℝ) (k : Lattice d) : ℝ := 32 * qk k ^ 2 * rieszCoeff d s k * wt 1

/-- `|A - ε| ≤ CA ε²`. -/
def CA (d : ℕ) (s β : ℝ) (k : Lattice d) : ℝ := 4 * Cc d s k / transientRate d s β k

/-- The constant of the weighted remainder. -/
def CR (d : ℕ) (s β : ℝ) (k : Lattice d) : ℝ :=
  2 * (wt 1 * Cc d s k * (2 / transientRate d s β k)) +
    (6 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k) * (16 * wt 1 ^ 2)

theorem Cc_nonneg (h : Hyp d s β k) : 0 ≤ Cc d s k := by
  have := rieszCoeff_nonneg' h k
  have := wt_pos 1
  unfold Cc; positivity

theorem CA_nonneg (h : Hyp d s β k) : 0 ≤ CA d s β k := by
  have := Cc_nonneg h
  have := lam_pos h
  unfold CA; positivity

theorem CR_nonneg (h : Hyp d s β k) : 0 ≤ CR d s β k := by
  have := Cc_nonneg h
  have := lam_pos h
  have := rieszCoeff_nonneg' h k
  have := wt_pos 1
  unfold CR; positivity

/-- The weighted remainder bound. -/
theorem remainder_weighted (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f) :
    ∃ A : ℝ, |A - ε| ≤ CA d s β k * ε ^ 2 ∧ ∀ t, 0 ≤ t →
      Summable (fun n : ℤ => wt n * |f n t - (if n = 1 ∨ n = -1 then
          A / Real.sqrt 2 * Real.exp (-(transientRate d s β k * t)) else 0)|) ∧
      ∑' n : ℤ, wt n * |f n t - (if n = 1 ∨ n = -1 then
          A / Real.sqrt 2 * Real.exp (-(transientRate d s β k * t)) else 0)| ≤
        CR d s β k * ε ^ 2 * Real.exp (-(3 * transientRate d s β k * t / 2)) := by
  obtain ⟨S, hSs, hSsum, hSb⟩ := hf.bound
  have hS0 : ∀ n, 0 ≤ S n := fun n => by
    have := hSb n 0 le_rfl
    exact (mul_nonneg (mul_nonneg (wt_pos n).le (Real.exp_pos _).le) (abs_nonneg _)).trans this
  obtain ⟨-, hT0, hTs, hTsum⟩ := Tconv_facts hSs hS0
  have hl := lam_pos h
  set lm := transientRate d s β k with hlm
  have hg := rieszCoeff_nonneg' h k
  have hq : 0 ≤ qk k ^ 2 := sq_nonneg _
  have hw1 := wt_pos 1
  have hSS0 : 0 ≤ ∑' n, S n := tsum_nonneg hS0
  have hSS2 : (∑' n, S n) ^ 2 ≤ 16 * wt 1 ^ 2 * ε ^ 2 := by
    have := pow_le_pow_left₀ hSS0 hSsum 2
    calc _ ≤ (4 * wt 1 * |ε|) ^ 2 := this
      _ = _ := by rw [mul_pow, sq_abs]; ring
  have hTsq : ∑' n, Tconv S n ≤ 16 * wt 1 ^ 2 * ε ^ 2 := hTsum.trans hSS2
  have hT1 : Tconv S 1 ≤ 16 * wt 1 ^ 2 * ε ^ 2 := (hTs.le_tsum 1 fun j _ => hT0 j).trans hTsq
  obtain ⟨a, ha, hat⟩ := amplitude_exists h hf hSs hSb
  set c₁ : ℝ := 2 * qk k ^ 2 * rieszCoeff d s k * Tconv S 1 / wt 1 with hc₁
  have hc₁0 : 0 ≤ c₁ := by have := hT0 1; rw [hc₁]; positivity
  have hc₁le : c₁ ≤ Cc d s k * ε ^ 2 := by
    rw [hc₁, div_le_iff₀ hw1]
    unfold Cc
    have : 2 * qk k ^ 2 * rieszCoeff d s k * Tconv S 1 ≤
        2 * qk k ^ 2 * rieszCoeff d s k * (16 * wt 1 ^ 2 * ε ^ 2) :=
      mul_le_mul_of_nonneg_left hT1 (by positivity)
    nlinarith
  have hsq2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq0 : 0 < Real.sqrt 2 := by positivity
  refine ⟨ε + Real.sqrt 2 * a, ?_, fun t ht => ?_⟩
  · have : ε + Real.sqrt 2 * a - ε = Real.sqrt 2 * a := by ring
    rw [this, abs_mul, abs_of_pos hsq0]
    have h1 : |a| ≤ Cc d s k * ε ^ 2 * (2 / lm) :=
      ha.trans (mul_le_mul_of_nonneg_right hc₁le (by positivity))
    calc Real.sqrt 2 * |a| ≤ 2 * (Cc d s k * ε ^ 2 * (2 / lm)) :=
          mul_le_mul hsq2 h1 (abs_nonneg _) (by norm_num)
      _ = CA d s β k * ε ^ 2 := by unfold CA; rw [← hlm]; field_simp; ring
  · -- pointwise bounds
    set A : ℝ := ε + Real.sqrt 2 * a with hA
    have hAs : A / Real.sqrt 2 = ε / Real.sqrt 2 + a := by
      rw [hA]; field_simp
    set E : ℝ := Real.exp (-(3 * lm * t / 2)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    set g : ℤ → ℝ := fun n => f n t - (if n = 1 ∨ n = -1 then
          A / Real.sqrt 2 * Real.exp (-(lm * t)) else 0) with hg_def
    set K1 : ℝ := wt 1 * (c₁ * (2 / lm)) with hK1
    set K2 : ℝ := 6 * qk k ^ 2 * rieszCoeff d s k / lm with hK2
    have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
    have hK20 : 0 ≤ K2 := by rw [hK2]; positivity
    have hg1 : |g 1| ≤ c₁ * (2 / lm) * E := by
      have h1 := hat t ht
      have e : g 1 = Real.exp (-(lm * t)) * (Real.exp (lm * t) * f 1 t - ε / Real.sqrt 2 - a) := by
        simp only [hg_def, if_true, true_or]
        rw [hAs]
        have : Real.exp (-(lm * t)) * Real.exp (lm * t) = 1 := by rw [← Real.exp_add]; simp
        calc f 1 t - (ε / Real.sqrt 2 + a) * Real.exp (-(lm * t))
            = (Real.exp (-(lm * t)) * Real.exp (lm * t)) * f 1 t -
              (ε / Real.sqrt 2 + a) * Real.exp (-(lm * t)) := by rw [this, one_mul]
          _ = _ := by ring
      rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(lm * t)) * |Real.exp (lm * t) * f 1 t - ε / Real.sqrt 2 - a|
          ≤ Real.exp (-(lm * t)) * (c₁ * (2 / lm) * Real.exp (-(lm / 2) * t)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = c₁ * (2 / lm) * E := by
            rw [hE]
            calc _ = c₁ * (2 / lm) * (Real.exp (-(lm * t)) * Real.exp (-(lm / 2) * t)) := by ring
              _ = _ := by rw [← Real.exp_add]; congr 2; ring
    have hgm1 : |g (-1)| = |g 1| := by
      simp only [hg_def]
      rw [hf.even 1 t]
      simp
    have hpt : ∀ n : ℤ, wt n * |g n| ≤ E * (K1 * (if n = 1 ∨ n = -1 then 1 else 0) + K2 * Tconv S n) := by
      intro n
      by_cases h0 : n = 0
      · subst h0
        have : g 0 = 0 := by simp [hg_def, hf.f_zero ht]
        rw [this]; simp only [abs_zero, mul_zero]
        have := hT0 0
        positivity
      · by_cases h1 : n = 1 ∨ n = -1
        · have hwn : wt n = wt 1 := by rcases h1 with rfl | rfl <;> simp [wt_neg]
          have hgn : |g n| = |g 1| := by rcases h1 with rfl | rfl; rfl; exact hgm1
          rw [hwn, hgn, if_pos h1]
          have := hT0 n
          calc wt 1 * |g 1| ≤ wt 1 * (c₁ * (2 / lm) * E) := mul_le_mul_of_nonneg_left hg1 hw1.le
            _ = E * (K1 * 1) := by rw [hK1]; ring
            _ ≤ E * (K1 * 1 + K2 * Tconv S n) := by
                apply mul_le_mul_of_nonneg_left _ hE0.le
                have := mul_nonneg hK20 (hT0 n)
                linarith
        · have h2 : 2 ≤ |n| := by
            have := Int.one_le_abs h0
            have h3 : |n| ≠ 1 := fun h4 => h1 (by
              rcases abs_eq (zero_le_one) |>.mp h4 with rfl | rfl <;> simp)
            omega
          have := wt_f_le_of_ge_two h hf hSs hSb h2 ht
          have hgn : g n = f n t := by simp [hg_def, h1]
          rw [hgn, if_neg h1]
          calc wt n * |f n t| ≤ K2 * Tconv S n * Real.exp (-(2 * omg d s β k * t)) := this
            _ = E * (K1 * 0 + K2 * Tconv S n) := by
                have : Real.exp (-(2 * omg d s β k * t)) = E := by
                  rw [hE]; congr 1; simp only [omg, hlm]; ring
                rw [this]; ring
    have hind : Summable (fun n : ℤ => (if n = 1 ∨ n = -1 then (1 : ℝ) else 0)) := by
      refine summable_of_ne_finset_zero (s := {1, -1}) fun n hn => ?_
      have : ¬ (n = 1 ∨ n = -1) := by simpa using hn
      simp [this]
    have hindsum : ∑' n : ℤ, (if n = 1 ∨ n = -1 then (1 : ℝ) else 0) = 2 := by
      rw [tsum_eq_sum (s := {1, -1}) (fun n hn => by
        have : ¬ (n = 1 ∨ n = -1) := by simpa using hn
        simp [this])]
      rw [Finset.sum_pair (by norm_num)]
      norm_num
    have hbs : Summable (fun n : ℤ => E * (K1 * (if n = 1 ∨ n = -1 then 1 else 0) + K2 * Tconv S n)) :=
      ((hind.mul_left K1).add (hTs.mul_left K2)).mul_left E
    have hsmg : Summable (fun n : ℤ => wt n * |g n|) :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (wt_pos n).le (abs_nonneg _)) hpt hbs
    refine ⟨hsmg, ?_⟩
    calc ∑' n, wt n * |g n| ≤ ∑' n : ℤ, E * (K1 * (if n = 1 ∨ n = -1 then 1 else 0) + K2 * Tconv S n) :=
          Summable.tsum_le_tsum hpt hsmg hbs
      _ = E * (K1 * 2 + K2 * ∑' n, Tconv S n) := by
          rw [tsum_mul_left, (hind.mul_left K1).tsum_add (hTs.mul_left K2), tsum_mul_left,
            tsum_mul_left, hindsum]
      _ ≤ E * (K1 * 2 + K2 * (16 * wt 1 ^ 2 * ε ^ 2)) := by
          gcongr
      _ ≤ E * (CR d s β k * ε ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hE0.le
          have hK1le : K1 ≤ wt 1 * Cc d s k * (2 / lm) * ε ^ 2 := by
            rw [hK1]
            calc wt 1 * (c₁ * (2 / lm)) ≤ wt 1 * (Cc d s k * ε ^ 2 * (2 / lm)) := by
                  gcongr
              _ = _ := by ring
          unfold CR
          rw [← hlm]
          nlinarith [hK1le]
      _ = _ := by ring


/-! ### Sobolev norms of line-supported coefficients -/

/-- The constant relating `H^N` norms on the line to weighted `ℓ¹` norms. -/
def BK (k : Lattice d) (N : ℕ) : ℝ :=
  Real.sqrt ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ N) * ((N.factorial : ℝ) * Real.exp 1)

theorem BK_nonneg (k : Lattice d) (N : ℕ) : 0 ≤ BK k N := by unfold BK; positivity

theorem pow_one_add_le_wt (N : ℕ) (n : ℤ) :
    (1 + |(n : ℝ)|) ^ N ≤ (N.factorial : ℝ) * Real.exp 1 * wt n := by
  have h1 := Real.pow_div_factorial_le_exp (1 + |(n : ℝ)|) (by positivity) N
  have hf : (0 : ℝ) < N.factorial := by positivity
  rw [div_le_iff₀ hf] at h1
  have e : Real.exp (1 + |(n : ℝ)|) = Real.exp 1 * Real.exp |(n : ℝ)| := Real.exp_add _ _
  have h2 : Real.exp |(n : ℝ)| ≤ wt n := by
    unfold wt
    have := Real.exp_pos |(n : ℝ)|
    nlinarith [abs_nonneg (n : ℝ)]
  calc (1 + |(n : ℝ)|) ^ N ≤ Real.exp (1 + |(n : ℝ)|) * N.factorial := h1
    _ = (N.factorial : ℝ) * Real.exp 1 * Real.exp |(n : ℝ)| := by rw [e]; ring
    _ ≤ _ := by gcongr

theorem sobWeight_zsmul_le (k : Lattice d) (N : ℕ) (n : ℤ) :
    sobWeight (N : ℝ) (n • k) ≤
      (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ N * ((1 + |(n : ℝ)|) ^ N) ^ 2 := by
  unfold sobWeight
  rw [Real.rpow_natCast, enorm_zsmul, ← pow_mul, mul_comm N 2, pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  set a : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have : (|(n : ℝ)| * Lattice.enorm k) ^ 2 = (n : ℝ) ^ 2 * Lattice.enorm k ^ 2 := by
    rw [mul_pow, sq_abs]
  have e : 4 * Real.pi ^ 2 * (|(n : ℝ)| * Lattice.enorm k) ^ 2 = (n : ℝ) ^ 2 * a := by
    rw [this, ha]; ring
  rw [e]
  have hn := abs_nonneg (n : ℝ)
  nlinarith [sq_abs (n : ℝ), mul_nonneg ha0 hn, mul_nonneg ha0 (sq_nonneg (n : ℝ))]

theorem hsNorm_lineCoeff_le (hk : k ≠ 0) (N : ℕ) (a : ℤ → ℂ)
    (ha : Summable fun n => wt n * ‖a n‖) :
    MemHs (N : ℝ) (lineCoeff k a) ∧
      hsNorm (N : ℝ) (lineCoeff k a) ≤ BK k N * ∑' n, wt n * ‖a n‖ := by
  set β0 : ℝ := 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hβ0
  have hβ0p : 0 < β0 := by rw [hβ0]; positivity
  set u : ℤ → ℝ := fun n => (1 + |(n : ℝ)|) ^ N * ‖a n‖ with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hule : ∀ n, u n ≤ ((N.factorial : ℝ) * Real.exp 1) * (wt n * ‖a n‖) := fun n => by
    simp only [hu]
    calc (1 + |(n : ℝ)|) ^ N * ‖a n‖ ≤ ((N.factorial : ℝ) * Real.exp 1 * wt n) * ‖a n‖ :=
          mul_le_mul_of_nonneg_right (pow_one_add_le_wt N n) (norm_nonneg _)
      _ = _ := by ring
  have hus : Summable u := Summable.of_nonneg_of_le hu0 hule (ha.mul_left _)
  have huS : ∑' n, u n ≤ ((N.factorial : ℝ) * Real.exp 1) * ∑' n, wt n * ‖a n‖ := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hule hus (ha.mul_left _)
  set U : ℝ := ∑' n, u n with hU
  have hU0 : 0 ≤ U := tsum_nonneg hu0
  have hterm : ∀ n : ℤ, sobWeight (N : ℝ) (n • k) * ‖a n‖ ^ 2 ≤ β0 ^ N * (U * u n) := fun n => by
    have h1 := sobWeight_zsmul_le k N n
    have h2 : u n ≤ U := hus.le_tsum n fun j _ => hu0 j
    have h3 : u n ^ 2 ≤ U * u n := by nlinarith [hu0 n]
    calc sobWeight (N : ℝ) (n • k) * ‖a n‖ ^ 2
        ≤ (β0 ^ N * ((1 + |(n : ℝ)|) ^ N) ^ 2) * ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = β0 ^ N * u n ^ 2 := by simp only [hu]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hs1 : Summable fun n : ℤ => sobWeight (N : ℝ) (n • k) * ‖a n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => by unfold sobWeight; positivity) hterm
      ((hus.mul_left U).mul_left _)
  have hcomp : (fun j : Lattice d => sobWeight (N : ℝ) j * ‖lineCoeff k a j‖ ^ 2) ∘
      (fun n : ℤ => n • k) = fun n => sobWeight (N : ℝ) (n • k) * ‖a n‖ ^ 2 := by
    funext n; simp only [Function.comp, lineCoeff_smul hk]
  have hoff : ∀ j ∉ Set.range (fun n : ℤ => n • k),
      sobWeight (N : ℝ) j * ‖lineCoeff k a j‖ ^ 2 = 0 := fun j hj => by
    rw [lineCoeff_of_not_mem _ j (fun n hn => hj ⟨n, hn.symm⟩)]; simp
  have hmem : MemHs (N : ℝ) (lineCoeff k a) := by
    unfold MemHs
    rw [← (smul_injective_of_ne_zero hk).summable_iff hoff, hcomp]
    exact hs1
  refine ⟨hmem, ?_⟩
  have hsq : hsNormSq (N : ℝ) (lineCoeff k a) =
      ∑' n : ℤ, sobWeight (N : ℝ) (n • k) * ‖a n‖ ^ 2 := by
    unfold hsNormSq
    rw [← (smul_injective_of_ne_zero hk).tsum_eq (f := fun j : Lattice d =>
      sobWeight (N : ℝ) j * ‖lineCoeff k a j‖ ^ 2) (fun j hj => by
        by_contra hc; exact hj (hoff j hc))]
    exact tsum_congr fun n => by rw [lineCoeff_smul hk]
  have hsq2 : hsNormSq (N : ℝ) (lineCoeff k a) ≤ β0 ^ N * U ^ 2 := by
    rw [hsq]
    calc _ ≤ ∑' n : ℤ, β0 ^ N * (U * u n) := Summable.tsum_le_tsum hterm hs1
          ((hus.mul_left U).mul_left _)
      _ = β0 ^ N * U ^ 2 := by rw [tsum_mul_left, tsum_mul_left]; ring
  unfold hsNorm
  calc Real.sqrt (hsNormSq (N : ℝ) (lineCoeff k a)) ≤ Real.sqrt (β0 ^ N * U ^ 2) :=
        Real.sqrt_le_sqrt hsq2
    _ = Real.sqrt (β0 ^ N) * U := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hU0]
    _ ≤ Real.sqrt (β0 ^ N) * (((N.factorial : ℝ) * Real.exp 1) * ∑' n, wt n * ‖a n‖) :=
        mul_le_mul_of_nonneg_left huS (Real.sqrt_nonneg _)
    _ = _ := by unfold BK; rw [← hβ0]; ring


/-! ### The remainder as a function -/

theorem toFun_sub_of_summable {a b : Coeff d} (ha : Summable fun j => ‖a j‖)
    (hb : Summable fun j => ‖b j‖) (x : Torus d) : toFun (a - b) x = toFun a x - toFun b x := by
  unfold toFun series
  have h1 := summable_series_terms a ha x
  have h2 := summable_series_terms b hb x
  have : (fun j => (a - b) j * Torus.mode j x) = fun j => a j * Torus.mode j x - b j * Torus.mode j x := by
    funext j; simp [sub_mul]
  rw [this, h1.tsum_sub h2, Complex.sub_re]

theorem lineCoeff_sub (hk : k ≠ 0) (a b : ℤ → ℂ) : lineCoeff k (a - b) = lineCoeff k a - lineCoeff k b := by
  funext j
  by_cases h : ∃ n : ℤ, j = n • k
  · obtain ⟨n, rfl⟩ := h
    simp only [Pi.sub_apply, lineCoeff_smul hk]
  · push Not at h
    simp [lineCoeff_of_not_mem _ j h]

theorem summable_data (hk : k ≠ 0) (a : ℝ) :
    Summable fun j => ‖coeffOf (fun x => 1 + a * cosTest k x) j‖ := by
  rw [coeffOf_data_line hk]
  refine summable_norm_lineCoeff hk ?_
  refine summable_of_ne_finset_zero (s := {0, 1, -1}) fun n hn => ?_
  have h0 : n ≠ 0 := by intro h; apply hn; simp [h]
  have h1 : n ≠ 1 := by intro h; apply hn; simp [h]
  have h2 : n ≠ -1 := by intro h; apply hn; simp [h]
  simp [deltaSeq, f0, h0, h1, h2]

theorem toFun_data (hk : k ≠ 0) (a : ℝ) :
    toFun (coeffOf (fun x => 1 + a * cosTest k x)) = fun x => 1 + a * cosTest k x := by
  refine toFun_coeffOf _ ?_ (summable_data hk a)
  unfold cosTest
  exact continuous_const.add (continuous_const.mul
    (continuous_const.mul (Torus.continuous_cosMode k)))

theorem isRealCoeff_data (a : ℝ) : IsRealCoeff (coeffOf (fun x => 1 + a * cosTest k x)) := by
  refine isRealCoeff_coeffOf _ ?_
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  unfold cosTest
  exact continuous_const.add (continuous_const.mul
    (continuous_const.mul (Torus.continuous_cosMode k)))


theorem isRealCoeff_sub {a b : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b) :
    IsRealCoeff (a - b) := fun j => by
  simp only [Pi.sub_apply, map_sub]; rw [ha j, hb j]

/-- The `C^j` remainder bound. -/
theorem remainder_cbNorm (h : Hyp d s β k) :
    ∃ Cj : ℕ → ℝ, ∀ (ε : ℝ) (f : ℤ → ℝ → ℝ), MildSol d s β k ε f →
      ∃ A : ℝ, |A - ε| ≤ CA d s β k * ε ^ 2 ∧ ∀ (j : ℕ) (t : ℝ), 0 ≤ t →
        Torus.cbNorm j (fun x => toFun (rhoC k f t) x - 1 -
            A * Real.exp (-transientRate d s β k * t) * cosTest k x) ≤
          Cj j * ε ^ 2 * Real.exp (-3 * transientRate d s β k * t / 2) := by
  have hemb : ∀ j : ℕ, ∃ C : ℝ, ∀ c : Coeff d, MemHs (((j + d : ℕ) : ℝ)) c → IsRealCoeff c →
      Torus.IsCk j (toFun c) ∧ Torus.cbNorm j (toFun c) ≤ C * hsNorm (((j + d : ℕ) : ℝ)) c :=
    fun j => toFun_isCk_le j _ (by
      have : (2 : ℝ) ≤ d := by exact_mod_cast h.hd
      push_cast; linarith)
  choose Ce hCe using hemb
  refine ⟨fun j => |Ce j| * BK k (j + d) * CR d s β k, fun ε f hf => ?_⟩
  obtain ⟨A, hA, hrem⟩ := remainder_weighted h hf
  refine ⟨A, hA, fun j t ht => ?_⟩
  obtain ⟨hsm, hsum⟩ := hrem t ht
  set a' : ℝ := A * Real.exp (-transientRate d s β k * t) with ha'
  set g : ℤ → ℂ := fun n => ((f n t : ℝ) : ℂ) - ((f0 a' n : ℝ) : ℂ) with hg
  have hgn : ∀ n, ‖g n‖ = |f n t - (if n = 1 ∨ n = -1 then
      A / Real.sqrt 2 * Real.exp (-(transientRate d s β k * t)) else 0)| := fun n => by
    simp only [hg, f0]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    congr 2
    split_ifs
    · rw [ha']; rw [neg_mul]; ring
    · rfl
  have hsmg : Summable fun n => wt n * ‖g n‖ := by simpa only [hgn] using hsm
  have hsumg : ∑' n, wt n * ‖g n‖ = ∑' n : ℤ, wt n * |f n t - (if n = 1 ∨ n = -1 then
          A / Real.sqrt 2 * Real.exp (-(transientRate d s β k * t)) else 0)| := by
    simp only [hgn]
  have hline : rhoC k f t - coeffOf (fun x => 1 + a' * cosTest k x) = lineCoeff k g := by
    rw [coeffOf_data_line h.hk, rhoC, ← lineCoeff_sub h.hk]
    congr 1
    funext n
    simp only [hg, Pi.sub_apply, Pi.add_apply]
    ring
  have hreal : IsRealCoeff (lineCoeff k g) := by
    rw [← hline]; exact isRealCoeff_sub (rhoC_isReal h.hk hf t) (isRealCoeff_data a')
  have hfun : (fun x => toFun (rhoC k f t) x - 1 - a' * cosTest k x) = toFun (lineCoeff k g) := by
    funext x
    rw [← hline, toFun_sub_of_summable (hf.summable_rhoC h ht) (summable_data h.hk a'), toFun_data h.hk]
    ring
  obtain ⟨hmem, hnorm⟩ := hsNorm_lineCoeff_le h.hk (j + d) g hsmg
  have hfun' : (fun x => toFun (rhoC k f t) x - 1 -
      A * Real.exp (-transientRate d s β k * t) * cosTest k x) = toFun (lineCoeff k g) := hfun
  rw [hfun']
  have h1 := (hCe j _ hmem hreal).2
  have hE : Real.exp (-(3 * transientRate d s β k * t / 2)) =
      Real.exp (-3 * transientRate d s β k * t / 2) := by congr 1; ring
  calc Torus.cbNorm j (toFun (lineCoeff k g)) ≤ Ce j * hsNorm (((j + d : ℕ) : ℝ)) (lineCoeff k g) := h1
    _ ≤ |Ce j| * hsNorm (((j + d : ℕ) : ℝ)) (lineCoeff k g) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
    _ ≤ |Ce j| * (BK k (j + d) * ∑' n, wt n * ‖g n‖) :=
        mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
    _ ≤ |Ce j| * (BK k (j + d) * (CR d s β k * ε ^ 2 * Real.exp (-(3 * transientRate d s β k * t / 2)))) := by
        rw [hsumg]
        gcongr
        exact BK_nonneg k _
    _ = _ := by rw [hE]; ring


/-! ### Smoothness and positivity of the density -/

theorem abs_toFun_le (c : Coeff d) (hs : Summable fun j => ‖c j‖) (x : Torus d) :
    |toFun c x| ≤ ∑' j, ‖c j‖ := by
  unfold toFun series
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_tsum_le_tsum_norm (summable_series_terms c hs x).norm).trans ?_
  simp [Torus.norm_mode]

theorem tsum_norm_lineCoeff (hk : k ≠ 0) (a : ℤ → ℂ) :
    ∑' j, ‖lineCoeff k a j‖ = ∑' n, ‖a n‖ := by
  rw [← (smul_injective_of_ne_zero hk).tsum_eq (f := fun j : Lattice d => ‖lineCoeff k a j‖)
    (fun j hj => by
      by_contra hc
      apply hj
      show ‖lineCoeff k a j‖ = 0
      rw [lineCoeff_of_not_mem _ j (fun n hn => hc ⟨n, hn.symm⟩)]; simp)]
  exact tsum_congr fun n => by rw [lineCoeff_smul hk]

theorem MildSol.abs_f_le (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {S : ℤ → ℝ} (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n)
    (n : ℤ) {t : ℝ} (ht : 0 ≤ t) : |f n t| ≤ S n := by
  have h1 : (1 : ℝ) ≤ Real.exp (omg d s β k * t) := Real.one_le_exp (mul_nonneg (omg_nonneg h) ht)
  have h2 : (1 : ℝ) ≤ wt n := by have := one_add_le_wt n; linarith [abs_nonneg (n : ℝ)]
  have := hb n t ht
  have h3 : 1 ≤ wt n * Real.exp (omg d s β k * t) := by nlinarith
  nlinarith [abs_nonneg (f n t)]

theorem rho_sub_one (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {t : ℝ} (ht : 0 ≤ t) (x : Torus d) :
    toFun (rhoC k f t) x - 1 = toFun (lineCoeff k (fun n => ((f n t : ℝ) : ℂ))) x := by
  have hline : rhoC k f t - coeffOf (fun x => 1 + (0 : ℝ) * cosTest k x) =
      lineCoeff k (fun n => ((f n t : ℝ) : ℂ)) := by
    rw [coeffOf_data_line h.hk, rhoC, ← lineCoeff_sub h.hk]
    congr 1
    funext n
    simp [f0]
  rw [← hline, toFun_sub_of_summable (hf.summable_rhoC h ht) (summable_data h.hk 0), toFun_data h.hk]
  ring

theorem rho_dev_le (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {t : ℝ} (ht : 0 ≤ t) (x : Torus d) :
    |toFun (rhoC k f t) x - 1| ≤ 4 * wt 1 * |ε| := by
  obtain ⟨S, hSs, hSsum, hSb⟩ := hf.bound
  have hfs : Summable fun n : ℤ => ‖((f n t : ℝ) : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hf.abs_f_le h hSb n ht) hSs
  rw [rho_sub_one h hf ht x]
  refine (abs_toFun_le _ (summable_norm_lineCoeff h.hk hfs) x).trans ?_
  rw [tsum_norm_lineCoeff h.hk]
  refine le_trans (Summable.tsum_le_tsum (fun n => ?_) hfs hSs) hSsum
  rw [Complex.norm_real, Real.norm_eq_abs]; exact hf.abs_f_le h hSb n ht

theorem rho_smooth (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {t : ℝ} (ht : 0 ≤ t) : Torus.IsSmooth (toFun (rhoC k f t)) := by
  obtain ⟨S, hSs, hSsum, hSb⟩ := hf.bound
  refine isSmooth_toFun_of_decay _ (rhoC_isReal h.hk hf t) fun N => ?_
  have hsm : Summable fun n : ℤ => wt n * ‖deltaSeq n + ((f n t : ℝ) : ℂ)‖ := by
    have hd0 : Summable fun n : ℤ => wt n * ‖deltaSeq n‖ := by
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      have : n ≠ 0 := by simpa using hn
      simp [deltaSeq, this]
    refine Summable.of_nonneg_of_le (fun n => by have := wt_pos n; positivity) (fun n => ?_)
      (hd0.add hSs)
    have h1 := hf.abs_f_le h hSb n ht
    have h2 : wt n * |f n t| ≤ S n := by
      have e : (1 : ℝ) ≤ Real.exp (omg d s β k * t) :=
        Real.one_le_exp (mul_nonneg (omg_nonneg h) ht)
      have := hSb n t ht
      nlinarith [mul_nonneg (wt_pos n).le (abs_nonneg (f n t))]
    have h3 : ‖deltaSeq n + ((f n t : ℝ) : ℂ)‖ ≤ ‖deltaSeq n‖ + |f n t| := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc wt n * ‖deltaSeq n + ((f n t : ℝ) : ℂ)‖
        ≤ wt n * (‖deltaSeq n‖ + |f n t|) := mul_le_mul_of_nonneg_left h3 (wt_pos n).le
      _ = wt n * ‖deltaSeq n‖ + wt n * |f n t| := by ring
      _ ≤ _ := by linarith
  have := (hsNorm_lineCoeff_le h.hk N _ hsm).1
  exact this


/-! ### Parseval pairing and the weak formulation -/

theorem isCk_of_isSmooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (n : ℕ) : Torus.IsCk n φ :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ)
    (by exact_mod_cast le_top)

theorem continuous_of_isSmooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  Torus.continuous_of_continuous_lift (isCk_of_isSmooth hφ 0).continuous

/-- Parseval for continuous real functions: `∑_j û(-j) v̂(j) = ∫ u v`. -/
theorem hasSum_pairing {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v) :
    HasSum (fun j : Lattice d => coeffOf u (-j) * coeffOf v j) (((∫ x, u x * v x : ℝ)) : ℂ) := by
  have hmem : ∀ w : Torus d → ℝ, Continuous w → MemLp (fun x => ((w x : ℝ) : ℂ)) 2 volume :=
    fun w hw => (Complex.continuous_ofReal.comp hw).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := hasSum_parseval (fun x => ((u x : ℝ) : ℂ)) (fun x => ((v x : ℝ) : ℂ)) (hmem u hu) (hmem v hv)
  have hr := isRealCoeff_coeffOf u (hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have e1 : ∀ n : Lattice d, conj (Torus.funFourierCoeff (fun x => ((u x : ℝ) : ℂ)) n) *
      Torus.funFourierCoeff (fun x => ((v x : ℝ) : ℂ)) n = coeffOf u (-n) * coeffOf v n := fun n => by
    show conj (coeffOf u n) * coeffOf v n = _
    rw [hr n]
  have e2 : ∫ t, conj (((u t : ℝ) : ℂ)) * ((v t : ℝ) : ℂ) = (((∫ x, u x * v x : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  simp_rw [e1, e2] at h
  exact h

theorem hasSum_line {F : Lattice d → ℂ} (hk : k ≠ 0) (hoff : ∀ j, (∀ n : ℤ, j ≠ n • k) → F j = 0)
    {v : ℂ} (h : HasSum F v) : HasSum (fun n : ℤ => F (n • k)) v := by
  rw [← (smul_injective_of_ne_zero hk).hasSum_iff (f := F) (fun j hj => hoff j (fun n hn => hj ⟨n, hn.symm⟩))]
    at h
  exact h

theorem enorm_neg' (j : Lattice d) : Lattice.enorm (-j) = Lattice.enorm j := by
  have := enorm_zsmul j (-1)
  simpa using this

theorem continuous_laplacian {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) : Continuous (Torus.laplacian ψ) := by
  have : Torus.laplacian ψ = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ψ) x :=
    funext (laplacian_eq_sum ψ hψ)
  rw [this]
  exact continuous_finset_sum _ fun j _ => continuous_partialDeriv j _ (isCk_one_partialDeriv j ψ hψ)


/-- The force component `g_i(x) = (∇g ⋆ ρ)_i(x)`. -/
def fcomp (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (i : Fin d) (x : Torus d) : ℝ :=
  convGradConv (periodicRieszGrad d s) ρ x i

theorem memLp_of_cont {w : Torus d → ℝ} (hw : Continuous w) : MemLp w 2 volume :=
  hw.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem key_pairing (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {t : ℝ} (ht : 0 ≤ t) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    HasSum (fun j : Lattice d => mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f t) (-j) * coeffOf ψ j)
      ((β⁻¹ * (∫ x, toFun (rhoC k f t) x * Torus.laplacian ψ x) -
        ∑ i : Fin d, ∫ x, toFun (rhoC k f t) x * fcomp d s (toFun (rhoC k f t)) i x *
          Torus.partialDeriv i ψ x : ℝ) : ℂ) := by
  set c := rhoC k f t with hc
  set ρ := toFun c with hρ
  have hsm := hf.summable_rhoC h ht
  have hcoef : coeffOf ρ = c := coeffOf_toFun c (rhoC_isReal h.hk hf t) hsm
  have hρs : Torus.IsSmooth ρ := rho_smooth h hf ht
  have hρ1 : Torus.IsCk 1 ρ := isCk_of_isSmooth hρs 1
  have hρc : Continuous ρ := continuous_of_isSmooth hρs
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hgc : ∀ i, Continuous (fcomp d s ρ i) := fun i => by
    have := convGradConv_continuous h.hd h.hs0 h.hsd ρ hρ1
    exact (EuclideanSpace.proj i).continuous.comp this
  have hgco : ∀ i, coeffOf (fcomp d s ρ i) = gradRieszCoeff d s i c := fun i => by
    have := convGradConv_coeff h.hd h.hs0 h.hsd ρ hρ1 i
    rw [hcoef] at this
    exact this
  have hprod : ∀ i, coeffOf (fun x => ρ x * fcomp d s ρ i x) =
      mulCoeff c (gradRieszCoeff d s i c) := fun i => by
    rw [coeffOf_mul ρ _ (memLp_of_cont hρc) (memLp_of_cont (hgc i)), hcoef, hgco i]
  have hA := hasSum_pairing hρc (continuous_laplacian hψ)
  have hB : ∀ i, HasSum (fun j : Lattice d => coeffOf (fun x => ρ x * fcomp d s ρ i x) (-j) *
      coeffOf (Torus.partialDeriv i ψ) j) ((∫ x, ρ x * fcomp d s ρ i x * Torus.partialDeriv i ψ x : ℝ) : ℂ) :=
    fun i => hasSum_pairing (u := fun x => ρ x * fcomp d s ρ i x) (hρc.mul (hgc i))
      (continuous_partialDeriv i ψ hψ1)
  have hS := (hA.mul_left (((β⁻¹ : ℝ)) : ℂ)).sub
    (hasSum_sum (s := Finset.univ) (fun i _ => hB i))
  convert hS using 1
  · funext j
    simp only [mfRhsCoeff]
    rw [coeffOf_zero_fun]
    have e1 : ∀ i : Fin d, (fun k' => derivCoeff i (fun _ : Lattice d => (0 : ℂ)) k' +
        gradRieszCoeff d s i c k') = gradRieszCoeff d s i c := fun i => by
      funext k'; simp [derivCoeff]
    simp only [e1]
    have e2 : coeffOf (Torus.laplacian ψ) j = -((4 * Real.pi ^ 2 * Lattice.enorm j ^ 2 : ℝ) : ℂ) *
        coeffOf ψ j := by
      rw [coeffOf_laplacian ψ hψ]; rfl
    have e3 : ∀ i, coeffOf (Torus.partialDeriv i ψ) j =
        (2 * Real.pi * Complex.I * (j i : ℂ)) * coeffOf ψ j := fun i => by
      rw [coeffOf_partialDeriv i ψ hψ1]; rfl
    simp only [e2, e3, hprod, hcoef, laplaceCoeff, derivCoeff, enorm_neg', Pi.neg_apply,
      Int.cast_neg]
    rw [add_mul, Finset.sum_mul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · push_cast; rfl


theorem grad_zero_fun (x : Torus d) : Torus.grad (fun _ : Torus d => (0 : ℝ)) x = 0 := by
  simp [Torus.grad, Torus.lift, gradient, Function.comp_def]

theorem matVec_neg_one (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

theorem weak_integrand (h : Hyp d s β k) {ρ : Torus d → ℝ} (hρ1 : Torus.IsCk 1 ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    pair (withDensityReal ρ) (fun x => (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).invβ *
        Torus.laplacian ψ x - inner ℝ (Torus.grad (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).V x)
          (Torus.grad ψ x)) +
      interactionPairing (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ) ψ (withDensityReal ρ)
        (withDensityReal ρ) =
    β⁻¹ * (∫ x, ρ x * Torus.laplacian ψ x) - ∑ i : Fin d, ∫ x, ρ x * fcomp d s ρ i x *
          Torus.partialDeriv i ψ x := by
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift hρ1.continuous
  have hmeas : Measurable ρ := hρc.measurable
  have hgc : ∀ i, Continuous (fcomp d s ρ i) := fun i => by
    have := convGradConv_continuous h.hd h.hs0 h.hsd ρ hρ1
    exact (EuclideanSpace.proj i).continuous.comp this
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hint := MFPairing.interactionPairing_eq_of_isCk (by have := h.hd; omega)
    (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ) ρ hρ1 hρ0 ψ hψ
  rw [hint]
  have hpair : pair (withDensityReal ρ) (fun x => (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).invβ *
        Torus.laplacian ψ x - inner ℝ (Torus.grad (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).V x)
          (Torus.grad ψ x)) = β⁻¹ * (∫ x, ρ x * Torus.laplacian ψ x) := by
    unfold pair
    rw [integral_withDensityReal_eq ρ hmeas hρ0]
    simp only [mfData, grad_zero_fun, inner_zero_left, sub_zero]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  rw [hpair]
  congr 1
  have e : ∀ x, ρ x * inner ℝ (Torus.grad ψ x) (Torus.matVec
      (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).M (convGradConv (periodicRieszGrad d
        (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).s) ρ x)) =
      -∑ i : Fin d, ρ x * fcomp d s ρ i x * Torus.partialDeriv i ψ x := fun x => by
    simp only [mfData, matVec_neg_one, inner_neg_right]
    simp only [PiLp.inner_apply, MFAux.grad_apply, fcomp, RCLike.inner_apply, conj_trivial]
    rw [mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_neg, integral_finset_sum]
  intro i _
  exact ((hρc.mul (hgc i)).mul (continuous_partialDeriv i ψ hψ1)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)


/-! ### Uniform bounds for the mode equation -/

/-- The scalar right-hand side of the `n`-th mode equation. -/
def Nn (d : ℕ) (s β : ℝ) (k : Lattice d) (f : ℤ → ℝ → ℝ) (n : ℤ) (σ : ℝ) : ℝ :=
  -(lam d s β k n) * f n σ + Fnl d s k (fun j => f j σ) (fun j => f j σ) n

theorem sq_le_wt (n : ℤ) : (n : ℝ) ^ 2 ≤ wt n := by
  unfold wt
  have h1 := Real.add_one_le_exp |(n : ℝ)|
  have h2 := abs_nonneg (n : ℝ)
  nlinarith [sq_abs (n : ℝ)]

theorem coeffOf_norm_le (ψ : Torus d → ℝ) (j : Lattice d) :
    ‖coeffOf ψ j‖ ≤ ∫ x, |ψ x| := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : ‖UnitAddTorus.mFourier (-j) x‖ = 1 := by
    have := Torus.norm_mode (-j) x
    exact this
  show ‖UnitAddTorus.mFourier (-j) x * ((ψ x : ℝ) : ℂ)‖ = |ψ x|
  rw [norm_mul, this, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem Nn_bound (h : Hyp d s β k) {f : ℤ → ℝ → ℝ} {S : ℤ → ℝ} (hS : Summable S)
    (hb : ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n)
    (n : ℤ) {σ : ℝ} (hσ : 0 ≤ σ) :
    |Nn d s β k f n σ| ≤ qk k ^ 2 * (β⁻¹ + rieszCoeff d s k) * S n +
      2 * qk k ^ 2 * rieszCoeff d s k * Tconv S n := by
  have hS0 : ∀ n, 0 ≤ S n := fun n => by
    have := hb n 0 le_rfl
    exact (mul_nonneg (mul_nonneg (wt_pos n).le (Real.exp_pos _).le) (abs_nonneg _)).trans this
  obtain ⟨-, hT0, -, -⟩ := Tconv_facts hS hS0
  have hg := rieszCoeff_nonneg' h k
  have hq : 0 ≤ qk k ^ 2 := sq_nonneg _
  have hb0 : 0 < β⁻¹ := inv_pos.mpr h.hβ
  have hwn := wt_pos n
  have hexp : (1 : ℝ) ≤ Real.exp (omg d s β k * σ) :=
    Real.one_le_exp (mul_nonneg (omg_nonneg h) hσ)
  have hwf : wt n * |f n σ| ≤ S n := by
    have := hb n σ hσ
    nlinarith [mul_nonneg hwn.le (abs_nonneg (f n σ))]
  -- linear part
  have hlin : |(-(lam d s β k n)) * f n σ| ≤ qk k ^ 2 * (β⁻¹ + rieszCoeff d s k) * S n := by
    rw [abs_mul, abs_neg]
    have hl0 : 0 ≤ lam d s β k n := by
      rw [lam_eq]; have := rieszCoeff_nonneg' h (n • k); positivity
    rw [abs_of_nonneg hl0]
    have hl : lam d s β k n ≤ qk k ^ 2 * (β⁻¹ + rieszCoeff d s k) * wt n := by
      rw [lam_eq]
      have h1 := rieszCoeff_zsmul_le h n
      have h2 := sq_le_wt n
      have h3 : qk k ^ 2 * (n : ℝ) ^ 2 * (β⁻¹ + rieszCoeff d s (n • k)) ≤
          qk k ^ 2 * (n : ℝ) ^ 2 * (β⁻¹ + rieszCoeff d s k) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h4 : qk k ^ 2 * (n : ℝ) ^ 2 * (β⁻¹ + rieszCoeff d s k) ≤
          qk k ^ 2 * wt n * (β⁻¹ + rieszCoeff d s k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hq
      nlinarith
    calc lam d s β k n * |f n σ| ≤ (qk k ^ 2 * (β⁻¹ + rieszCoeff d s k) * wt n) * |f n σ| :=
          mul_le_mul_of_nonneg_right hl (abs_nonneg _)
      _ = qk k ^ 2 * (β⁻¹ + rieszCoeff d s k) * (wt n * |f n σ|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwf (by positivity)
  have hnl : |Fnl d s k (fun j => f j σ) (fun j => f j σ) n| ≤
      2 * qk k ^ 2 * rieszCoeff d s k * Tconv S n := by
    by_cases hn : n = 0
    · subst hn; simp [Fnl]; have := hT0 0; positivity
    · have h1 := Fnl_wt_le h hS hb hn hσ
      have hE : Real.exp (-(2 * omg d s β k * σ)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have := omg_nonneg h; nlinarith)
      have hT := hT0 n
      have h2 : wt n * |Fnl d s k (fun j => f j σ) (fun j => f j σ) n| ≤
          (2 * qk k ^ 2 * rieszCoeff d s k * Tconv S n) * wt n := by
        calc _ ≤ 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 *
              Real.exp (-(2 * omg d s β k * σ)) * Tconv S n := h1
          _ ≤ 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 * 1 * Tconv S n := by
              gcongr
          _ = (2 * qk k ^ 2 * rieszCoeff d s k * Tconv S n) * (n : ℝ) ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (sq_le_wt n) (by positivity)
      nlinarith [mul_nonneg hwn.le (abs_nonneg (Fnl d s k (fun j => f j σ) (fun j => f j σ) n))]
  unfold Nn
  exact (abs_add_le _ _).trans (add_le_add hlin hnl)


/-! ### The density is a probability density -/

theorem coeffOf_zero_eq_integral (φ : Torus d → ℝ) : coeffOf φ 0 = ((∫ x, φ x : ℝ) : ℂ) := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [UnitAddTorus.mFourier_zero]

theorem rho_pos (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    (hε : 4 * wt 1 * |ε| ≤ 1 / 2) {t : ℝ} (ht : 0 ≤ t) (x : Torus d) :
    0 < toFun (rhoC k f t) x := by
  have := rho_dev_le h hf ht x
  have := (abs_le.mp (this.trans hε)).1
  linarith

theorem rho_isProb (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    (hε : 4 * wt 1 * |ε| ≤ 1 / 2) {t : ℝ} (ht : 0 ≤ t) : IsProbDensity (toFun (rhoC k f t)) := by
  have hs := rho_smooth h hf ht
  refine ⟨fun x => (rho_pos h hf hε ht x).le, (continuous_of_isSmooth hs).measurable, ?_⟩
  have hcoef : coeffOf (toFun (rhoC k f t)) = rhoC k f t :=
    coeffOf_toFun _ (rhoC_isReal h.hk hf t) (hf.summable_rhoC h ht)
  have h0 := coeffOf_zero_eq_integral (toFun (rhoC k f t))
  rw [hcoef] at h0
  have h1 : rhoC k f t 0 = 1 := by
    have := rhoC_smul h.hk f t 0
    rw [zero_smul] at this
    rw [this, hf.f_zero ht]
    simp [deltaSeq]
  rw [h1] at h0
  exact_mod_cast h0.symm


/-! ### The weak formulation -/

theorem hasSum_P (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {r : ℝ} (hr : 0 ≤ r) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    HasSum (fun n : ℤ => rhoC k f r (n • k) * coeffOf ψ (-(n • k)))
      (((∫ x, toFun (rhoC k f r) x * ψ x : ℝ)) : ℂ) := by
  have hρc := continuous_of_isSmooth (rho_smooth h hf hr)
  have hcoef : coeffOf (toFun (rhoC k f r)) = rhoC k f r :=
    coeffOf_toFun _ (rhoC_isReal h.hk hf r) (hf.summable_rhoC h hr)
  have h1 := hasSum_pairing hρc hψ
  rw [hcoef] at h1
  have h2 : HasSum (fun j : Lattice d => rhoC k f r j * coeffOf ψ (-j))
      (((∫ x, toFun (rhoC k f r) x * ψ x : ℝ)) : ℂ) := by
    rw [← (Equiv.neg (Lattice d)).hasSum_iff]
    convert h1 using 1
    funext j; simp
  refine hasSum_line h.hk (fun j hj => ?_) h2
  rw [supportedOnLine_rhoC k f r j hj, zero_mul]

theorem hasSum_Q (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {r : ℝ} (hr : 0 ≤ r) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    HasSum (fun n : ℤ => ((Nn d s β k f n r : ℝ) : ℂ) * coeffOf ψ (-(n • k)))
      ((β⁻¹ * (∫ x, toFun (rhoC k f r) x * Torus.laplacian ψ x) -
        ∑ i : Fin d, ∫ x, toFun (rhoC k f r) x * fcomp d s (toFun (rhoC k f r)) i x *
          Torus.partialDeriv i ψ x : ℝ) : ℂ) := by
  have hkey := key_pairing h hf hr hψ
  have h2 : HasSum (fun j : Lattice d => mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f r) j *
      coeffOf ψ (-j)) ((β⁻¹ * (∫ x, toFun (rhoC k f r) x * Torus.laplacian ψ x) -
        ∑ i : Fin d, ∫ x, toFun (rhoC k f r) x * fcomp d s (toFun (rhoC k f r)) i x *
          Torus.partialDeriv i ψ x : ℝ) : ℂ) := by
    rw [← (Equiv.neg (Lattice d)).hasSum_iff]
    convert hkey using 1
    funext j; simp
  have h3 := hasSum_line h.hk (fun j hj => by
    unfold rhoC
    rw [mfRhsCoeff_lineCoeff_off _ j hj, zero_mul]) h2
  convert h3 using 1
  funext n
  rw [rhs_rhoC h hf hr n]
  rfl

theorem transient_isMeanFieldSolution (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ}
    (hf : MildSol d s β k ε f) (hε : 4 * wt 1 * |ε| ≤ 1 / 2) (T : ℝ) :
    IsMeanFieldSolution (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ) T
      (fun t => toFun (rhoC k f t)) := by
  refine ⟨fun t ht => rho_isProb h hf hε ht.1, fun ψ hψ t ht => ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hψ1 : Torus.IsCk 1 ψ := hψ.of_le (by norm_num)
  have hψc : Continuous ψ := Torus.continuous_of_continuous_lift hψ1.continuous
  obtain ⟨S, hSs, hSsum, hSb⟩ := hf.bound
  -- pairings as integrals
  have hP : ∀ r, 0 ≤ r → pair (withDensityReal (toFun (rhoC k f r))) ψ =
      ∫ x, toFun (rhoC k f r) x * ψ x := fun r hr => by
    unfold pair
    exact integral_withDensityReal_eq _ (rho_isProb h hf hε hr).measurable
      (rho_isProb h hf hε hr).nonneg ψ
  -- the integrand
  set W : ℝ → ℝ := fun r => pair (withDensityReal (toFun (rhoC k f r)))
      (fun x => (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).invβ * Torus.laplacian ψ x -
        inner ℝ (Torus.grad (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ).V x) (Torus.grad ψ x)) +
      interactionPairing (mfData d s h.hs0 h.hsd (fun _ => 0) β h.hβ) ψ
        (withDensityReal (toFun (rhoC k f r))) (withDensityReal (toFun (rhoC k f r))) with hW
  have hWeq : ∀ r, 0 ≤ r → W r = β⁻¹ * (∫ x, toFun (rhoC k f r) x * Torus.laplacian ψ x) -
        ∑ i : Fin d, ∫ x, toFun (rhoC k f r) x * fcomp d s (toFun (rhoC k f r)) i x *
          Torus.partialDeriv i ψ x := fun r hr =>
    weak_integrand h (isCk_of_isSmooth (rho_smooth h hf hr) 1)
      (rho_isProb h hf hε hr).nonneg hψ
  have hQ : ∀ r, 0 ≤ r → HasSum (fun n : ℤ => ((Nn d s β k f n r : ℝ) : ℂ) * coeffOf ψ (-(n • k)))
      ((W r : ℝ) : ℂ) := fun r hr => by
    rw [hWeq r hr]; exact hasSum_Q h hf hr hψ
  -- integrated equation, mode by mode
  have hinteg : ∀ n : ℤ, rhoC k f t (n • k) - rhoC k f 0 (n • k) =
      ((∫ σ in (0 : ℝ)..t, Nn d s β k f n σ : ℝ) : ℂ) := fun n => by
    have h1 := (hf.integrated h (n • k) ht0).1
    have h0 := (hf.integrated h (n • k) (le_refl 0)).1
    simp only [intervalIntegral.integral_same, add_zero] at h0
    rw [h1, h0, add_sub_cancel_left, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le ht0] at hσ
    rw [rhs_rhoC h hf hσ.1 n]; rfl
  -- left side
  have hL : HasSum (fun n : ℤ => ((∫ σ in (0 : ℝ)..t, Nn d s β k f n σ : ℝ) : ℂ) *
      coeffOf ψ (-(n • k))) ((((∫ x, toFun (rhoC k f t) x * ψ x : ℝ)) : ℂ) -
        (((∫ x, toFun (rhoC k f 0) x * ψ x : ℝ)) : ℂ)) := by
    have := (hasSum_P h hf ht0 hψc).sub (hasSum_P h hf (le_refl 0) hψc)
    convert this using 1
    funext n
    rw [← hinteg n, sub_mul]
  -- dominated convergence
  set Cψ : ℝ := ∫ x, |ψ x| with hCψ
  set B : ℤ → ℝ := fun n => Cψ * (qk k ^ 2 * (β⁻¹ + rieszCoeff d s k) * S n +
      2 * qk k ^ 2 * rieszCoeff d s k * Tconv S n) with hB
  have hS0 : ∀ n, 0 ≤ S n := fun n => by
    have := hSb n 0 le_rfl
    exact (mul_nonneg (mul_nonneg (wt_pos n).le (Real.exp_pos _).le) (abs_nonneg _)).trans this
  obtain ⟨-, hT0, hTs, -⟩ := Tconv_facts hSs hS0
  have hBs : Summable B := ((hSs.mul_left _).add (hTs.mul_left _)).mul_left _
  have hcont : ∀ n : ℤ, Continuous fun σ => ((Nn d s β k f n σ : ℝ) : ℂ) * coeffOf ψ (-(n • k)) :=
    fun n => (Complex.continuous_ofReal.comp ((continuous_const.mul (hf.cont n)).add
      (hf.contF n))).mul continuous_const
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := t)
    (F := fun n σ => ((Nn d s β k f n σ : ℝ) : ℂ) * coeffOf ψ (-(n • k)))
    (f := fun σ => ((W σ : ℝ) : ℂ)) (fun n _ => B n)
    (fun n => (hcont n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun σ hσ => by
      rw [Set.uIoc_of_le ht0] at hσ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (Nn_bound h hSs hSb n hσ.1.le) (coeffOf_norm_le ψ _) (norm_nonneg _)
        (by have := Nn_bound h hSs hSb n (le_refl 0); exact (abs_nonneg _).trans this) |>.trans_eq
        (by simp only [hB]; ring))
    (Filter.Eventually.of_forall fun σ _ => hBs)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun σ hσ => by
      rw [Set.uIoc_of_le ht0] at hσ
      exact hQ σ hσ.1.le)
  have hfin := hL.unique (by
    convert hdom using 1
    funext n
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal])
  -- conclude
  have hreal : (∫ x, toFun (rhoC k f t) x * ψ x) - (∫ x, toFun (rhoC k f 0) x * ψ x) =
      ∫ σ in (0 : ℝ)..t, W σ := by
    have : ((((∫ x, toFun (rhoC k f t) x * ψ x : ℝ)) - ((∫ x, toFun (rhoC k f 0) x * ψ x : ℝ)) : ℝ) : ℂ) =
        ((∫ σ in (0 : ℝ)..t, W σ : ℝ) : ℂ) := by
      push_cast
      rw [hfin, intervalIntegral.integral_ofReal]
    exact_mod_cast this
  show pair (withDensityReal (toFun (rhoC k f t))) ψ - pair (withDensityReal (toFun (rhoC k f 0))) ψ =
    ∫ r in Set.Icc 0 t, W r
  rw [hP t ht0, hP 0 le_rfl, hreal, intervalIntegral.integral_of_le ht0, integral_Icc_eq_integral_Ioc]


/-! ### Assembly -/

theorem sign_eq_of_abs_sub_lt {A ε : ℝ} (hε : 0 < |ε|) (h : |A - ε| < |ε|) :
    Real.sign A = Real.sign ε := by
  rcases lt_or_gt_of_ne (abs_pos.mp hε) with hneg | hpos
  · rw [abs_of_neg hneg] at h
    have h1 := (abs_lt.mp h).2
    have : A < 0 := by linarith
    rw [Real.sign_of_neg this, Real.sign_of_neg hneg]
  · rw [abs_of_pos hpos] at h
    have h1 := (abs_lt.mp h).1
    have : 0 < A := by linarith
    rw [Real.sign_of_pos this, Real.sign_of_pos hpos]

/-- **The nonlinear transient** (`H:eq:nonlinear-transient`, Proposition `E:prop:mean`):
statement identical to `HRS.PDE.nonlinear_transient` of `HRS/PDE/MeanField.lean`. -/
theorem nonlinear_transient_main {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (hkβ : β * rieszCoeff d s k ≤ 1 / 4) :
    ∃ ε₀ C : ℝ, ∃ Cj : ℕ → ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < |ε| → |ε| ≤ ε₀ →
      ∃ ρ : ℝ → Torus d → ℝ,
        (∀ T, 0 < T → IsMeanFieldSolution (mfData d s hs0 hsd (fun _ => 0) β hβ) T ρ) ∧
        (∀ t, 0 ≤ t → Torus.IsSmooth (ρ t) ∧ ∀ x, 0 < ρ t x) ∧
        ρ 0 = (fun x => 1 + ε * cosTest k x) ∧
        ∃ A : ℝ, |A - ε| ≤ C * ε ^ 2 ∧ Real.sign A = Real.sign ε ∧
          (∀ j : ℕ, ∀ t, 0 ≤ t →
            Torus.cbNorm j (fun x =>
                ρ t x - 1 - A * Real.exp (-transientRate d s β k * t) * cosTest k x) ≤
              Cj j * ε ^ 2 * Real.exp (-3 * transientRate d s β k * t / 2)) ∧
          (∀ t, 0 ≤ t → ∀ l : Lattice d, (∀ n : ℤ, l ≠ n • k) → coeffOf (ρ t) l = 0) ∧
          (∀ t, 0 ≤ t → ∀ n : ℤ, coeffOf (ρ t) (n • k) = coeffOf (ρ t) (-(n • k))) := by
  have h : Hyp d s β k := ⟨hd, hs0, hsd, hβ, hk, hkβ⟩
  obtain ⟨ε₁, hε₁, hex⟩ := exists_transient_coeff h
  obtain ⟨Cj, hCj⟩ := remainder_cbNorm h
  have hw1 := wt_pos 1
  have hCA := CA_nonneg h
  refine ⟨min (min ε₁ (1 / (8 * wt 1))) (1 / (2 * (CA d s β k + 1))), CA d s β k, Cj,
    by positivity, fun ε hε0 hε => ?_⟩
  have hεa : |ε| ≤ ε₁ := (hε.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hεb : |ε| ≤ 1 / (8 * wt 1) := (hε.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hεc : |ε| ≤ 1 / (2 * (CA d s β k + 1)) := hε.trans (min_le_right _ _)
  have hε2 : 4 * wt 1 * |ε| ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hεb
    nlinarith
  obtain ⟨f, hf, h0, -, -, hsupp, hevn, -⟩ := hex ε hεa
  obtain ⟨A, hA, hrem⟩ := hCj ε f hf
  have hcoef : ∀ t, 0 ≤ t → coeffOf (toFun (rhoC k f t)) = rhoC k f t := fun t ht =>
    coeffOf_toFun _ (rhoC_isReal h.hk hf t) (hf.summable_rhoC h ht)
  refine ⟨fun t => toFun (rhoC k f t), fun T _ => transient_isMeanFieldSolution h hf hε2 T,
    fun t ht => ⟨rho_smooth h hf ht, rho_pos h hf hε2 ht⟩, ?_, A, hA, ?_, hrem, ?_, ?_⟩
  · show toFun (rhoC k f 0) = _
    rw [h0]; exact toFun_data h.hk ε
  · refine sign_eq_of_abs_sub_lt hε0 (lt_of_le_of_lt hA ?_)
    have h1 : CA d s β k * |ε| ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hεc
      nlinarith
    have : CA d s β k * ε ^ 2 = (CA d s β k * |ε|) * |ε| := by rw [← sq_abs]; ring
    rw [this]
    nlinarith
  · intro t ht l hl
    show coeffOf (toFun (rhoC k f t)) l = 0
    rw [hcoef t ht]
    exact hsupp t l hl
  · intro t ht n
    show coeffOf (toFun (rhoC k f t)) (n • k) = coeffOf (toFun (rhoC k f t)) (-(n • k))
    rw [hcoef t ht]
    exact hevn t n

end HRS.PDE.MFTransient
