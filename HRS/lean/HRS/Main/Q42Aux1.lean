import HRS.PDE.MeanFieldAux
import HRS.PDE.MeanFieldThermalUnique
import HRS.Kernel.Riesz
import HRS.PDE.MeanFieldDefs

/-!
# Packet Q42: explicit coefficients on the homogeneous torus

Helpers for `HRS.Main.homogeneous_cubic_coefficients`: the response inverse on the torus
`volume` acts diagonally on the real cosine modes `PDE.cosTest k`, and the cubic integrals
of the resulting two-mode functions are computed by product-to-sum identities.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

theorem q42_integrable_cont {f : Torus d → ℝ} (hf : Continuous f) :
    Integrable f (volume : Measure (Torus d)) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem q42_mode_zero_re (x : Torus d) : Torus.cosMode 0 x = 1 := by
  simp [Torus.cosMode, Torus.mode_zero]

/-- Product-to-sum for the real modes. -/
theorem q42_cosMode_mul (a b : Lattice d) (x : Torus d) :
    Torus.cosMode a x * Torus.cosMode b x =
      (Torus.cosMode (a + b) x + Torus.cosMode (a - b) x) / 2 := by
  unfold Torus.cosMode
  rw [Torus.mode_add, sub_eq_add_neg, Torus.mode_add, Torus.mode_neg]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- `∫ cos(2π a·x) dx = 1` if `a = 0`, else `0`. -/
theorem q42_integral_cosMode (a : Lattice d) :
    ∫ x : Torus d, Torus.cosMode a x = if a = 0 then 1 else 0 := by
  have hint : Integrable (Torus.mode a) (volume : Measure (Torus d)) :=
    (Torus.continuous_mode a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_re (μ := (volume : Measure (Torus d))) hint
  simp only [RCLike.re_to_complex] at h
  have h2 := Torus.integral_mode a
  unfold Torus.cosMode
  rw [h, h2]
  split_ifs <;> simp

/-- Complex form of the real mode: `cos = (e_a + e_{-a}) / 2`. -/
theorem q42_cos_complex (a : Lattice d) (x : Torus d) :
    ((Torus.cosMode a x : ℝ) : ℂ) = (Torus.mode a x + Torus.mode (-a) x) / 2 := by
  rw [Torus.mode_neg]
  unfold Torus.cosMode
  apply Complex.ext <;> simp

/-- The real cosine mode `ψ_k = √2 cos(2π k·x)` has mean zero for `k ≠ 0`. -/
theorem q42_int_cosTest {k : Lattice d} (hk : k ≠ 0) :
    ∫ x : Torus d, PDE.cosTest k x = 0 := by
  unfold PDE.cosTest
  rw [integral_const_mul, q42_integral_cosMode, if_neg hk, mul_zero]

/-- Fourier coefficients of `ψ_k`: they vanish off `±k`. -/
theorem q42_fourier_cosTest (k j : Lattice d) :
    Torus.funFourierCoeff (fun x => ((PDE.cosTest k x : ℝ) : ℂ)) j =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
        ((if -j + k = 0 then 1 else 0) + (if -j + -k = 0 then 1 else 0)) := by
  rw [PDE.funFourierCoeff_eq_int]
  have hpt : ∀ x : Torus d, UnitAddTorus.mFourier (-j) x * ((PDE.cosTest k x : ℝ) : ℂ) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (Torus.mode (-j + k) x + Torus.mode (-j + -k) x) := by
    intro x
    rw [Torus.mode_add, Torus.mode_add]
    unfold PDE.cosTest
    push_cast
    rw [q42_cos_complex]
    push_cast
    show Torus.mode (-j) x * _ = _
    ring
  have i1 : ∫ x : Torus d, Torus.mode (-j + k) x = if -j + k = 0 then 1 else 0 :=
    Torus.integral_mode _
  have i2 : ∫ x : Torus d, Torus.mode (-j + -k) x = if -j + -k = 0 then 1 else 0 :=
    Torus.integral_mode _
  have hI1 : Integrable (fun x : Torus d => Torus.mode (-j + k) x) (volume : Measure (Torus d)) :=
    (Torus.continuous_mode _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI2 : Integrable (fun x : Torus d => Torus.mode (-j + -k) x) (volume : Measure (Torus d)) :=
    (Torus.continuous_mode _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [hpt]
  rw [integral_const_mul, integral_add hI1 hI2, i1, i2]

theorem q42_fourier_cosTest_zero {k j : Lattice d} (h1 : j ≠ k) (h2 : j ≠ -k) :
    Torus.funFourierCoeff (fun x => ((PDE.cosTest k x : ℝ) : ℂ)) j = 0 := by
  rw [q42_fourier_cosTest]
  rw [if_neg (fun h => h1 (neg_add_eq_zero.mp h)), if_neg (fun h => h2 (neg_add_eq_zero.mp h))]
  simp

theorem q42_fourier_const_mul (c : ℝ) (f : Torus d → ℝ) (j : Lattice d) :
    Torus.funFourierCoeff (fun x => ((c * f x : ℝ) : ℂ)) j =
      (c : ℂ) * Torus.funFourierCoeff (fun x => (f x : ℂ)) j := by
  rw [PDE.funFourierCoeff_eq_int, PDE.funFourierCoeff_eq_int, ← integral_const_mul]
  congr 1
  funext x
  push_cast
  ring

/-- Eigenfunction property of the periodic Riesz convolution on the torus:
`g * cos(2πk·) = ĝ(k) cos(2πk·)`. -/
theorem q42_convFun_cosTest (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d)
    (hk : k ≠ 0) :
    convFun (periodicRiesz d s) (fun x => PDE.cosTest k x) =
      fun x => rieszCoeff d s k * PDE.cosTest k x := by
  have hg := PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  have hc : Continuous (fun x => PDE.cosTest k x) :=
    continuous_const.mul (Torus.continuous_cosMode k)
  apply PDE.MFAux.eq_of_funFourierCoeff_eq (PDE.MFAux.continuous_convFun hg hc)
    (continuous_const.mul hc)
  intro j
  show Torus.funFourierCoeff (fun x => (convFun (periodicRiesz d s) (fun x => PDE.cosTest k x) x : ℂ)) j
    = Torus.funFourierCoeff (fun x => ((rieszCoeff d s k * PDE.cosTest k x : ℝ) : ℂ)) j
  rw [PDE.MFAux.funFourierCoeff_convFun hg hc j, periodicRiesz_fourierCoeff hd hs0 hsd j,
    q42_fourier_const_mul]
  by_cases h1 : j = k
  · rw [h1]
  by_cases h2 : j = -k
  · rw [h2, rieszCoeff_neg]
  · rw [q42_fourier_cosTest_zero h1 h2]
    simp

/-- Linearity of the convolution in its second argument (integrable kernel, continuous data). -/
theorem q42_convFun_lin {g a b : Torus d → ℝ} (hg : Integrable g) (ha : Continuous a)
    (hb : Continuous b) (α γ : ℝ) (x : Torus d) :
    convFun g (fun y => α * a y + γ * b y) x = α * convFun g a x + γ * convFun g b x := by
  have hgx : Integrable (fun y => g (x - y)) := hg.comp_sub_left x
  have hi : ∀ c : Torus d → ℝ, Continuous c → Integrable (fun y => g (x - y) * c y) := by
    intro c hc
    obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
    exact hgx.mul_bdd hc.aestronglyMeasurable (c := B)
      (Filter.Eventually.of_forall fun y => hB y (Set.mem_univ _))
  unfold convFun
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi a ha).const_mul α)
    ((hi b hb).const_mul γ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- The two-mode function `α ψ_k + γ ψ_{2k}` convolves to a two-mode function. -/
theorem q42_convFun_comb (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d)
    (hk : k ≠ 0) (hk2 : (2 : ℤ) • k ≠ 0) (α γ : ℝ) :
    convFun (periodicRiesz d s) (fun y => α * PDE.cosTest k y + γ * PDE.cosTest ((2 : ℤ) • k) y) =
      fun x => (α * rieszCoeff d s k) * PDE.cosTest k x +
        (γ * rieszCoeff d s ((2 : ℤ) • k)) * PDE.cosTest ((2 : ℤ) • k) x := by
  have hg := PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  have hc1 : Continuous (fun x => PDE.cosTest k x) :=
    continuous_const.mul (Torus.continuous_cosMode k)
  have hc2 : Continuous (fun x => PDE.cosTest ((2 : ℤ) • k) x) :=
    continuous_const.mul (Torus.continuous_cosMode _)
  funext x
  rw [q42_convFun_lin hg hc1 hc2 α γ x]
  rw [congrFun (q42_convFun_cosTest hd hs0 hsd k hk) x,
    congrFun (q42_convFun_cosTest hd hs0 hsd _ hk2) x]
  ring

theorem q42_int_comb (k : Lattice d) (hk : k ≠ 0) (hk2 : (2 : ℤ) • k ≠ 0) (α γ : ℝ) :
    ∫ x : Torus d, (α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) = 0 := by
  have hc1 : Continuous (fun x => PDE.cosTest k x) :=
    continuous_const.mul (Torus.continuous_cosMode k)
  have hc2 : Continuous (fun x => PDE.cosTest ((2 : ℤ) • k) x) :=
    continuous_const.mul (Torus.continuous_cosMode _)
  rw [integral_add (q42_integrable_cont (hc1.const_mul α)) (q42_integrable_cont (hc2.const_mul γ)),
    integral_const_mul, integral_const_mul, q42_int_cosTest hk, q42_int_cosTest hk2]
  simp

theorem q42_rieszCoeff_nonneg (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    0 ≤ rieszCoeff d s k := by
  by_cases h : k = 0
  · simp [rieszCoeff, h]
  · exact (rieszCoeff_pos hd hs0 hsd k h).le

theorem q42_one_add_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) : 0 < 1 + β * rieszCoeff d s k := by
  have := mul_nonneg hβ.le (q42_rieszCoeff_nonneg hd hs0 hsd k)
  linarith

theorem q42_two_smul_ne {k : Lattice d} (hk : k ≠ 0) : (2 : ℤ) • k ≠ 0 :=
  smul_ne_zero two_ne_zero hk

/-! ### The cubic integral of a two-mode function -/

/-- `n ↦ cos(2π (n k)·x)`. -/
def q42_C (k : Lattice d) (n : ℤ) (x : Torus d) : ℝ := Torus.cosMode (n • k) x

theorem q42_C_zero (k : Lattice d) (x : Torus d) : q42_C k 0 x = 1 := by
  unfold q42_C
  rw [zero_smul]
  exact q42_mode_zero_re x

theorem q42_C_neg (k : Lattice d) (n : ℤ) (x : Torus d) : q42_C k (-n) x = q42_C k n x := by
  unfold q42_C
  rw [neg_smul, Torus.cosMode_neg]

theorem q42_C_mul (k : Lattice d) (p q : ℤ) (x : Torus d) :
    q42_C k p x * q42_C k q x = (q42_C k (p + q) x + q42_C k (p - q) x) / 2 := by
  have h := q42_cosMode_mul (p • k) (q • k) x
  rw [← add_smul, ← sub_smul] at h
  exact h

theorem q42_C_integrable (k : Lattice d) (n : ℤ) :
    Integrable (fun x => q42_C k n x) (volume : Measure (Torus d)) :=
  q42_integrable_cont (Torus.continuous_cosMode (n • k))

theorem q42_C_int (k : Lattice d) (hk : k ≠ 0) (n : ℤ) (hn : n ≠ 0) :
    ∫ x : Torus d, q42_C k n x = 0 := by
  unfold q42_C
  rw [q42_integral_cosMode, if_neg (smul_ne_zero hn hk)]


theorem q42_integrable_six (k : Lattice d) (u1 u2 u3 u4 u5 u6 : ℝ) :
    Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x + u3 * q42_C k 3 x +
      u4 * q42_C k 4 x + u5 * q42_C k 5 x + u6 * q42_C k 6 x) (volume : Measure (Torus d)) := by
  have i : ∀ (c : ℝ) (n : ℤ), Integrable (fun x : Torus d => c * q42_C k n x)
      (volume : Measure (Torus d)) := fun c n => (q42_C_integrable k n).const_mul c
  have j2 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x)
      (volume : Measure (Torus d)) := (i u1 1).add (i u2 2)
  have j3 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x +
      u3 * q42_C k 3 x) (volume : Measure (Torus d)) := j2.add (i u3 3)
  have j4 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x +
      u3 * q42_C k 3 x + u4 * q42_C k 4 x) (volume : Measure (Torus d)) := j3.add (i u4 4)
  have j5 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x +
      u3 * q42_C k 3 x + u4 * q42_C k 4 x + u5 * q42_C k 5 x) (volume : Measure (Torus d)) :=
    j4.add (i u5 5)
  exact j5.add (i u6 6)

theorem q42_int_six (k : Lattice d) (hk : k ≠ 0) (u1 u2 u3 u4 u5 u6 : ℝ) :
    ∫ x : Torus d, (u1 * q42_C k 1 x + u2 * q42_C k 2 x + u3 * q42_C k 3 x +
      u4 * q42_C k 4 x + u5 * q42_C k 5 x + u6 * q42_C k 6 x) = 0 := by
  have i : ∀ (c : ℝ) (n : ℤ), Integrable (fun x : Torus d => c * q42_C k n x)
      (volume : Measure (Torus d)) := fun c n => (q42_C_integrable k n).const_mul c
  have j2 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x)
      (volume : Measure (Torus d)) := (i u1 1).add (i u2 2)
  have j3 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x +
      u3 * q42_C k 3 x) (volume : Measure (Torus d)) := j2.add (i u3 3)
  have j4 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x +
      u3 * q42_C k 3 x + u4 * q42_C k 4 x) (volume : Measure (Torus d)) := j3.add (i u4 4)
  have j5 : Integrable (fun x : Torus d => u1 * q42_C k 1 x + u2 * q42_C k 2 x +
      u3 * q42_C k 3 x + u4 * q42_C k 4 x + u5 * q42_C k 5 x) (volume : Measure (Torus d)) :=
    j4.add (i u5 5)
  rw [integral_add j5 (i u6 6), integral_add j4 (i u5 5), integral_add j3 (i u4 4),
    integral_add j2 (i u3 3), integral_add (i u1 1) (i u2 2)]
  simp only [integral_const_mul, q42_C_int k hk 1 one_ne_zero, q42_C_int k hk 2 two_ne_zero,
    q42_C_int k hk 3 (by norm_num), q42_C_int k hk 4 (by norm_num),
    q42_C_int k hk 5 (by norm_num), q42_C_int k hk 6 (by norm_num), mul_zero, add_zero]

theorem q42_cube (k : Lattice d) (hk : k ≠ 0) (a c : ℝ) :
    ∫ x : Torus d, (a * PDE.cosTest k x + c * PDE.cosTest ((2 : ℤ) • k) x) ^ 3 =
      3 * a ^ 2 * c / Real.sqrt 2 := by
  have hT1 : ∀ x : Torus d, PDE.cosTest k x = Real.sqrt 2 * q42_C k 1 x := by
    intro x
    unfold PDE.cosTest q42_C
    rw [one_smul]
  have hT2 : ∀ x : Torus d, PDE.cosTest ((2 : ℤ) • k) x = Real.sqrt 2 * q42_C k 2 x := by
    intro x
    rfl
  have e11 : ∀ x, q42_C k 1 x * q42_C k 1 x = (q42_C k 2 x + 1) / 2 := by
    intro x
    have h := q42_C_mul k 1 1 x
    rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, q42_C_zero] at h
    exact h
  have e12 : ∀ x, q42_C k 1 x * q42_C k 2 x = (q42_C k 3 x + q42_C k 1 x) / 2 := by
    intro x
    have h := q42_C_mul k 1 2 x
    rw [show (1 : ℤ) + 2 = 3 by norm_num, show (1 : ℤ) - 2 = -1 by norm_num, q42_C_neg] at h
    exact h
  have e22 : ∀ x, q42_C k 2 x * q42_C k 2 x = (q42_C k 4 x + 1) / 2 := by
    intro x
    have h := q42_C_mul k 2 2 x
    rw [show (2 : ℤ) + 2 = 4 by norm_num, show (2 : ℤ) - 2 = 0 by norm_num, q42_C_zero] at h
    exact h
  have e14 : ∀ x, q42_C k 1 x * q42_C k 4 x = (q42_C k 5 x + q42_C k 3 x) / 2 := by
    intro x
    have h := q42_C_mul k 1 4 x
    rw [show (1 : ℤ) + 4 = 5 by norm_num, show (1 : ℤ) - 4 = -3 by norm_num, q42_C_neg] at h
    exact h
  have e24 : ∀ x, q42_C k 2 x * q42_C k 4 x = (q42_C k 6 x + q42_C k 2 x) / 2 := by
    intro x
    have h := q42_C_mul k 2 4 x
    rw [show (2 : ℤ) + 4 = 6 by norm_num, show (2 : ℤ) - 4 = -2 by norm_num, q42_C_neg] at h
    exact h
  have p3 : ∀ x, q42_C k 1 x ^ 3 = (3 * q42_C k 1 x + q42_C k 3 x) / 4 := by
    intro x
    linear_combination q42_C k 1 x * e11 x + (1 / 2 : ℝ) * e12 x
  have p21 : ∀ x, q42_C k 1 x ^ 2 * q42_C k 2 x = (q42_C k 4 x + 1 + 2 * q42_C k 2 x) / 4 := by
    intro x
    linear_combination q42_C k 2 x * e11 x + (1 / 2 : ℝ) * e22 x
  have p12 : ∀ x, q42_C k 1 x * q42_C k 2 x ^ 2 =
      (q42_C k 5 x + q42_C k 3 x + 2 * q42_C k 1 x) / 4 := by
    intro x
    linear_combination q42_C k 1 x * e22 x + (1 / 2 : ℝ) * e14 x
  have p03 : ∀ x, q42_C k 2 x ^ 3 = (q42_C k 6 x + 3 * q42_C k 2 x) / 4 := by
    intro x
    linear_combination q42_C k 2 x * e22 x + (1 / 2 : ℝ) * e24 x
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ x : Torus d, (a * PDE.cosTest k x + c * PDE.cosTest ((2 : ℤ) • k) x) ^ 3 =
      2 * Real.sqrt 2 * (a ^ 3 * (3 * q42_C k 1 x + q42_C k 3 x) / 4 +
        3 * a ^ 2 * c * (q42_C k 4 x + 1 + 2 * q42_C k 2 x) / 4 +
        3 * a * c ^ 2 * (q42_C k 5 x + q42_C k 3 x + 2 * q42_C k 1 x) / 4 +
        c ^ 3 * (q42_C k 6 x + 3 * q42_C k 2 x) / 4) := by
    intro x
    rw [hT1, hT2]
    linear_combination (Real.sqrt 2 ^ 3 * a ^ 3) * p3 x +
      (Real.sqrt 2 ^ 3 * (3 * a ^ 2 * c)) * p21 x +
      (Real.sqrt 2 ^ 3 * (3 * a * c ^ 2)) * p12 x + (Real.sqrt 2 ^ 3 * c ^ 3) * p03 x +
      (Real.sqrt 2 * (a ^ 3 * (3 * q42_C k 1 x + q42_C k 3 x) / 4 +
        3 * a ^ 2 * c * (q42_C k 4 x + 1 + 2 * q42_C k 2 x) / 4 +
        3 * a * c ^ 2 * (q42_C k 5 x + q42_C k 3 x + 2 * q42_C k 1 x) / 4 +
        c ^ 3 * (q42_C k 6 x + 3 * q42_C k 2 x) / 4)) * hs
  -- the zero-mean part
  have hmean : ∫ x : Torus d, (a ^ 3 * (3 * q42_C k 1 x + q42_C k 3 x) / 4 +
        3 * a ^ 2 * c * (q42_C k 4 x + 1 + 2 * q42_C k 2 x) / 4 +
        3 * a * c ^ 2 * (q42_C k 5 x + q42_C k 3 x + 2 * q42_C k 1 x) / 4 +
        c ^ 3 * (q42_C k 6 x + 3 * q42_C k 2 x) / 4) = 3 * a ^ 2 * c / 4 := by
    have hfun : (fun x : Torus d => a ^ 3 * (3 * q42_C k 1 x + q42_C k 3 x) / 4 +
        3 * a ^ 2 * c * (q42_C k 4 x + 1 + 2 * q42_C k 2 x) / 4 +
        3 * a * c ^ 2 * (q42_C k 5 x + q42_C k 3 x + 2 * q42_C k 1 x) / 4 +
        c ^ 3 * (q42_C k 6 x + 3 * q42_C k 2 x) / 4) =
        fun x => (3 * a ^ 2 * c / 4 + ((3 * a ^ 3 / 4 + 6 * a * c ^ 2 / 4) * q42_C k 1 x +
          (6 * a ^ 2 * c / 4 + 3 * c ^ 3 / 4) * q42_C k 2 x +
          (a ^ 3 / 4 + 3 * a * c ^ 2 / 4) * q42_C k 3 x + (3 * a ^ 2 * c / 4) * q42_C k 4 x +
          (3 * a * c ^ 2 / 4) * q42_C k 5 x + (c ^ 3 / 4) * q42_C k 6 x)) := by
      funext x
      ring
    rw [hfun, integral_add (integrable_const _) (q42_integrable_six k _ _ _ _ _ _),
      q42_int_six k hk, integral_const]
    simp
  have hint : ∫ x : Torus d, (a * PDE.cosTest k x + c * PDE.cosTest ((2 : ℤ) • k) x) ^ 3 =
      ∫ x : Torus d, 2 * Real.sqrt 2 * (a ^ 3 * (3 * q42_C k 1 x + q42_C k 3 x) / 4 +
        3 * a ^ 2 * c * (q42_C k 4 x + 1 + 2 * q42_C k 2 x) / 4 +
        3 * a * c ^ 2 * (q42_C k 5 x + q42_C k 3 x + 2 * q42_C k 1 x) / 4 +
        c ^ 3 * (q42_C k 6 x + 3 * q42_C k 2 x) / 4) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hint, integral_const_mul, hmean]
  rw [eq_div_iff (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne']
  linear_combination (3 * a ^ 2 * c / 2) * hs

/-- The explicit two-mode function solves the response equation on the torus. -/
theorem q42_isResponse (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (α γ : ℝ) :
    IsResponse (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x)
      (fun x => (α * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
        (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) := by
  have hk2 : (2 : ℤ) • k ≠ 0 := q42_two_smul_ne hk
  have hne1 : (1 + β * rieszCoeff d s k) ≠ 0 := (q42_one_add_pos hd hs0 hsd hβ k).ne'
  have hne2 : (1 + β * rieszCoeff d s ((2 : ℤ) • k)) ≠ 0 :=
    (q42_one_add_pos hd hs0 hsd hβ _).ne'
  have hv1 : (1 + β * rieszCoeff d s k) * (1 + β * rieszCoeff d s k)⁻¹ = 1 :=
    mul_inv_cancel₀ hne1
  have hv2 : (1 + β * rieszCoeff d s ((2 : ℤ) • k)) *
      (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹ = 1 :=
    mul_inv_cancel₀ hne2
  have hc1 : Continuous (fun x => PDE.cosTest k x) :=
    continuous_const.mul (Torus.continuous_cosMode k)
  have hc2 : Continuous (fun x => PDE.cosTest ((2 : ℤ) • k) x) :=
    continuous_const.mul (Torus.continuous_cosMode _)
  have hcand : Continuous (fun x => (α * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
      (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) :=
    (continuous_const.mul hc1).add (continuous_const.mul hc2)
  have hconv := q42_convFun_comb hd hs0 hsd k hk hk2 (α * (1 + β * rieszCoeff d s k)⁻¹)
    (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹)
  have hmean : ∫ x : Torus d, convFun (periodicRiesz d s) (fun x => (α * (1 + β * rieszCoeff d s k)⁻¹) *
      PDE.cosTest k x + (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) *
      PDE.cosTest ((2 : ℤ) • k) x) x = 0 := by
    rw [hconv]
    exact q42_int_comb k hk hk2 _ _
  have hKop : ∀ x : Torus d, Kop (periodicRiesz d s) (volume : Measure (Torus d))
      (fun x => (α * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
        (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x) x =
      convFun (periodicRiesz d s) (fun x => (α * (1 + β * rieszCoeff d s k)⁻¹) *
        PDE.cosTest k x + (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) *
        PDE.cosTest ((2 : ℤ) • k) x) x := by
    intro x
    show convFun (periodicRiesz d s) _ x - HRS.pair (volume : Measure (Torus d))
      (convFun (periodicRiesz d s) _) = _
    unfold HRS.pair
    rw [hmean, sub_zero]
  refine ⟨hcand.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_, ?_⟩
  · unfold HRS.pair
    exact q42_int_comb k hk hk2 _ _
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [hKop x, congrFun hconv x]
    have hψm : HRS.pair (volume : Measure (Torus d))
        (fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) = 0 := by
      unfold HRS.pair
      exact q42_int_comb k hk hk2 α γ
    unfold projMean
    rw [hψm, sub_zero]
    dsimp only
    linear_combination (α * PDE.cosTest k x) * hv1 + (γ * PDE.cosTest ((2 : ℤ) • k) x) * hv2

/-- The response inverse on the torus is the explicit two-mode function, almost everywhere. -/
theorem q42_responseInverse_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ψ : Torus d → ℝ) (α γ : ℝ)
    (hψ : ∀ x, ψ x = α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) :
    ∀ᵐ x ∂(volume : Measure (Torus d)),
      responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β ψ x =
        (α * (1 + β * rieszCoeff d s k)⁻¹) * PDE.cosTest k x +
        (γ * (1 + β * rieszCoeff d s ((2 : ℤ) • k))⁻¹) * PDE.cosTest ((2 : ℤ) • k) x := by
  have hk2 : (2 : ℤ) • k ≠ 0 := q42_two_smul_ne hk
  have hfun : ψ = fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x := funext hψ
  subst hfun
  have hvol : (withDensityReal (fun _ : Torus d => (1 : ℝ))) = (volume : Measure (Torus d)) := by
    unfold withDensityReal
    simp
  have hρ : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  have hc1 : Continuous (fun x => PDE.cosTest k x) :=
    continuous_const.mul (Torus.continuous_cosMode k)
  have hc2 : Continuous (fun x => PDE.cosTest ((2 : ℤ) • k) x) :=
    continuous_const.mul (Torus.continuous_cosMode _)
  have hcomb : Continuous (fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) :=
    (continuous_const.mul hc1).add (continuous_const.mul hc2)
  have hψL : MemLp (fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) 2
      (withDensityReal (fun _ : Torus d => (1 : ℝ))) := by
    rw [hvol]
    exact hcomb.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨w, hw, huniq⟩ := exists_unique_response hd hs0 hsd (fun _ : Torus d => (1 : ℝ)) hρ 1
    (fun _ => le_rfl) β hβ.le _ hψL
  rw [hvol] at hw huniq
  have hex : ∃ h, IsResponse (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) h := ⟨w, hw⟩
  have hR : responseInverse (periodicRiesz d s) (volume : Measure (Torus d)) β
      (fun x => α * PDE.cosTest k x + γ * PDE.cosTest ((2 : ℤ) • k) x) = hex.choose := by
    unfold responseInverse
    rw [dif_pos hex]
  have hc := hex.choose_spec
  have hcand := q42_isResponse hd hs0 hsd hβ k hk α γ
  filter_upwards [huniq _ hc, huniq _ hcand] with x hx1 hx2
  rw [hR]
  exact hx1.trans hx2.symm

end HRS
