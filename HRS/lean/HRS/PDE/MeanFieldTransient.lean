import HRS.PDE.MeanFieldDefs

/-!
# The nonlinear transient, Fourier side (package MF-01, packet P10a)

For `V = 0`, `M = -I`, `ν = β⁻¹` and data `1 + ε√2 cos(2πk·x)` the mean-field equation has a
solution whose coefficients are supported on the line `ℤk`.  This file contains the
one-dimensional reduction (`mfRhsCoeff` on sequences `ℤ → ℂ`), the elementary estimates of the
rates `λ_n = transientRate d s β (n • k)`, and a global existence statement for small `ε` by a
contraction in the space `ℓ¹(ℤ; C_b([0,∞)))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate BoundedContinuousFunction

namespace HRS.PDE.MFTransient

open HRS

variable {d : ℕ} {s β : ℝ} {k : Lattice d}

/-! ### The line `ℤ k` -/

/-- Coefficients supported on the line `ℤ k`. -/
def SupportedOnLine (k : Lattice d) (c : Coeff d) : Prop := ∀ j, (∀ n : ℤ, j ≠ n • k) → c j = 0

theorem mulCoeff_supportedOnLine' (k : Lattice d) (a c : Coeff d)
    (ha : SupportedOnLine k a) (hc : SupportedOnLine k c) : SupportedOnLine k (mulCoeff a c) := by
  intro j hj
  have : ∀ l, a (j - l) * c l = 0 := by
    intro l
    by_cases hl : ∃ m : ℤ, l = m • k
    · obtain ⟨m, rfl⟩ := hl
      by_cases hl' : ∃ n : ℤ, j - m • k = n • k
      · obtain ⟨n, hn⟩ := hl'
        exact absurd (by rw [← sub_add_cancel j (m • k), hn, ← add_smul]) (hj (n + m))
      · push Not at hl'
        rw [ha _ hl', zero_mul]
    · push Not at hl
      rw [hc _ hl, mul_zero]
  unfold mulCoeff
  simp [this]

theorem mulCoeff_supportedOnLine (k : Lattice d) (a c : Coeff d)
    (ha : SupportedOnLine k a) (hc : SupportedOnLine k c) (_hs : Summable fun j => ‖a j‖)
    (_hs' : Summable fun j => ‖c j‖) : SupportedOnLine k (mulCoeff a c) :=
  mulCoeff_supportedOnLine' k a c ha hc

/-- The lift of a sequence `a : ℤ → ℂ` to the line: `c (n • k) = a n`, `c = 0` off the line. -/
def lineCoeff (k : Lattice d) (a : ℤ → ℂ) : Coeff d :=
  Function.extend (fun n : ℤ => n • k) a (fun _ => 0)

theorem smul_injective_of_ne_zero {k : Lattice d} (hk : k ≠ 0) :
    Function.Injective (fun n : ℤ => n • k) := by
  intro n n' h
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hk (funext hcon)
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hi this

theorem lineCoeff_smul {k : Lattice d} (hk : k ≠ 0) (a : ℤ → ℂ) (n : ℤ) :
    lineCoeff k a (n • k) = a n :=
  (smul_injective_of_ne_zero hk).extend_apply a _ n

theorem lineCoeff_of_not_mem {k : Lattice d} (a : ℤ → ℂ) (j : Lattice d)
    (hj : ∀ n : ℤ, j ≠ n • k) : lineCoeff k a j = 0 := by
  unfold lineCoeff
  rw [Function.extend_apply']
  rintro ⟨n, hn⟩
  exact hj n hn.symm

theorem supportedOnLine_lineCoeff (k : Lattice d) (a : ℤ → ℂ) :
    SupportedOnLine k (lineCoeff k a) := fun j hj => lineCoeff_of_not_mem a j hj

theorem lineCoeff_add {k : Lattice d} (hk : k ≠ 0) (a b : ℤ → ℂ) :
    lineCoeff k (a + b) = lineCoeff k a + lineCoeff k b := by
  funext j
  by_cases h : ∃ n : ℤ, j = n • k
  · obtain ⟨n, rfl⟩ := h
    simp only [Pi.add_apply, lineCoeff_smul hk]
  · push Not at h
    simp [lineCoeff_of_not_mem _ j h]

/-- Convolution of two line-supported coefficient sequences, read on the line. -/
theorem mulCoeff_lineCoeff {k : Lattice d} (hk : k ≠ 0) (a b : ℤ → ℂ) (n : ℤ) :
    mulCoeff (lineCoeff k a) (lineCoeff k b) (n • k) = ∑' m : ℤ, a (n - m) * b m := by
  unfold mulCoeff
  rw [← (smul_injective_of_ne_zero hk).tsum_eq (f := fun j => lineCoeff k a (n • k - j) *
    lineCoeff k b j)]
  · refine tsum_congr fun m => ?_
    rw [← sub_smul, lineCoeff_smul hk, lineCoeff_smul hk]
  · intro j hj
    by_contra hcon
    exact hj (by
      show lineCoeff k a (n • k - j) * lineCoeff k b j = 0
      rw [lineCoeff_of_not_mem _ j (fun n hn => hcon ⟨n, hn.symm⟩), mul_zero])


/-! ### The rates `λ_n` and the force coefficients along the line -/

/-- The standing hypotheses of Proposition `E:prop:mean`. -/
structure Hyp (d : ℕ) (s β : ℝ) (k : Lattice d) : Prop where
  hd : 2 ≤ d
  hs0 : 0 ≤ s
  hsd : s < d
  hβ : 0 < β
  hk : k ≠ 0
  hkβ : β * rieszCoeff d s k ≤ 1 / 4

/-- `q = 2π|k|`. -/
def qk (k : Lattice d) : ℝ := 2 * Real.pi * Lattice.enorm k

/-- The rate `λ_n = λ_{β, nk} = (2πn|k|)²(β⁻¹ + ĝ(nk))` of the `n`-th mode. -/
def lam (d : ℕ) (s β : ℝ) (k : Lattice d) (n : ℤ) : ℝ := transientRate d s β (n • k)

theorem enorm_zsmul (k : Lattice d) (n : ℤ) : Lattice.enorm (n • k) = |(n : ℝ)| * Lattice.enorm k := by
  have : Lattice.toEuc (n • k) = (n : ℝ) • Lattice.toEuc k := by
    ext i
    simp [Lattice.toEuc]
  rw [Lattice.enorm, this, norm_smul, Real.norm_eq_abs]
  rfl

theorem qk_pos (h : Hyp d s β k) : 0 < qk k := by
  have h1 := one_le_enorm k h.hk
  unfold qk
  positivity

theorem rieszCoeff_zsmul (h : Hyp d s β k) {n : ℤ} (hn : n ≠ 0) :
    rieszCoeff d s (n • k) = |(n : ℝ)| ^ (s - (d : ℝ)) * rieszCoeff d s k := by
  have hnk : n • k ≠ 0 := by
    intro h0
    exact hn ((smul_injective_of_ne_zero h.hk) (h0.trans (zero_smul ℤ k).symm))
  have hn' : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have h1 := one_le_enorm k h.hk
  unfold rieszCoeff
  simp only [hnk, h.hk, ite_false]
  rw [enorm_zsmul, ← mul_assoc, mul_comm (2 * Real.pi), mul_assoc, Real.mul_rpow hn'.le (by positivity)]
  ring

theorem rieszCoeff_nonneg' (h : Hyp d s β k) (j : Lattice d) : 0 ≤ rieszCoeff d s j := by
  by_cases hj : j = 0
  · simp [rieszCoeff, hj]
  · exact (rieszCoeff_pos h.hd h.hs0 h.hsd j hj).le

theorem rieszCoeff_zsmul_le (h : Hyp d s β k) (n : ℤ) :
    rieszCoeff d s (n • k) ≤ rieszCoeff d s k := by
  by_cases hn : n = 0
  · subst hn
    have : rieszCoeff d s ((0 : ℤ) • k) = 0 := by simp [rieszCoeff]
    rw [this]
    exact rieszCoeff_nonneg' h k
  rw [rieszCoeff_zsmul h hn]
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using this
  have h2 : |(n : ℝ)| ^ (s - (d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith [h.hsd])
  have h3 := rieszCoeff_nonneg' h k
  nlinarith

theorem lam_eq (n : ℤ) : lam d s β k n =
    (qk k) ^ 2 * (n : ℝ) ^ 2 * (β⁻¹ + rieszCoeff d s (n • k)) := by
  unfold lam transientRate qk
  rw [enorm_zsmul]
  have : (|(n : ℝ)| * Lattice.enorm k) ^ 2 = (n : ℝ) ^ 2 * Lattice.enorm k ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [mul_pow (2 * Real.pi), this]
  ring

theorem lam_one : lam d s β k 1 = transientRate d s β k := by simp [lam]

theorem lam_neg (n : ℤ) : lam d s β k (-n) = lam d s β k n := by
  rw [lam_eq, lam_eq, neg_smul, rieszCoeff_neg]
  push_cast
  ring

theorem lam_zero : lam d s β k 0 = 0 := by simp [lam_eq]

theorem transientRate_eq : transientRate d s β k = (qk k) ^ 2 * (β⁻¹ + rieszCoeff d s k) := by
  unfold transientRate qk; rfl

theorem lam_pos (h : Hyp d s β k) : 0 < transientRate d s β k := by
  rw [transientRate_eq]
  have := qk_pos h
  have := rieszCoeff_nonneg' h k
  have : 0 < β⁻¹ := inv_pos.mpr h.hβ
  positivity

/-- `λ_n ≥ (4/5) n² λ` (uses `β ĝ(k) ≤ 1/4` and `ĝ(nk) ≥ 0`). -/
theorem lam_ge (h : Hyp d s β k) (n : ℤ) :
    (4 / 5) * (n : ℝ) ^ 2 * transientRate d s β k ≤ lam d s β k n := by
  rw [lam_eq, transientRate_eq]
  have hq := qk_pos h
  have hg := rieszCoeff_nonneg' h (n • k)
  have hb : 0 < β⁻¹ := inv_pos.mpr h.hβ
  have h4 : β⁻¹ + rieszCoeff d s k ≤ (5 / 4) * β⁻¹ := by
    have := h.hkβ
    have : rieszCoeff d s k ≤ (1 / 4) * β⁻¹ := by
      rw [show (1 / 4 : ℝ) * β⁻¹ = (1 / 4) / β by ring, le_div_iff₀ h.hβ]; linarith
    linarith
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hq2 : 0 ≤ qk k ^ 2 := sq_nonneg _
  have : (4 / 5) * (β⁻¹ + rieszCoeff d s k) ≤ β⁻¹ + rieszCoeff d s (n • k) := by linarith
  calc (4 / 5) * (n : ℝ) ^ 2 * (qk k ^ 2 * (β⁻¹ + rieszCoeff d s k))
      = (qk k ^ 2 * (n : ℝ) ^ 2) * ((4 / 5) * (β⁻¹ + rieszCoeff d s k)) := by ring
    _ ≤ (qk k ^ 2 * (n : ℝ) ^ 2) * (β⁻¹ + rieszCoeff d s (n • k)) :=
        mul_le_mul_of_nonneg_left this (by positivity)

/-- `λ_n ≥ λ` for `|n| ≥ 1`. -/
theorem lam_ge_lam (h : Hyp d s β k) {n : ℤ} (hn : n ≠ 0) :
    transientRate d s β k ≤ lam d s β k n := by
  have hl := lam_pos h
  rcases eq_or_ne |n| 1 with h1 | h1
  · rcases abs_eq (zero_le_one) |>.mp h1 with rfl | rfl
    · rw [lam_one]
    · rw [lam_neg, lam_one]
  · have h2 : (2 : ℤ) ≤ |n| := by have := Int.one_le_abs hn; omega
    have h3 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : ((2 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h2
      have h4 : (2 : ℝ) ≤ |(n : ℝ)| := by simpa using this
      nlinarith [sq_abs (n : ℝ)]
    have := lam_ge h n
    nlinarith

/-- `λ_n ≥ (16/5) λ ≥ 3λ/2` for `|n| ≥ 2`. -/
theorem lam_ge_two (h : Hyp d s β k) {n : ℤ} (hn : 2 ≤ |n|) :
    (3 / 2) * transientRate d s β k ≤ lam d s β k n := by
  have hl := lam_pos h
  have h3 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : ((2 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn
    have h4 : (2 : ℝ) ≤ |(n : ℝ)| := by simpa using this
    nlinarith [sq_abs (n : ℝ)]
  have := lam_ge h n
  nlinarith

/-- `λ_n - 3λ/4 ≥ n²λ/4` for `n ≠ 0`: the denominators of the Duhamel integrals. -/
theorem lam_sub_ge (h : Hyp d s β k) {n : ℤ} (hn : n ≠ 0) :
    (1 / 4) * (n : ℝ) ^ 2 * transientRate d s β k ≤ lam d s β k n - (3 / 4) * transientRate d s β k := by
  have hl := lam_pos h
  rcases eq_or_ne |n| 1 with h1 | h1
  · have : lam d s β k n = transientRate d s β k := by
      rcases abs_eq (zero_le_one) |>.mp h1 with rfl | rfl
      · rw [lam_one]
      · rw [lam_neg, lam_one]
    have hn2 : (n : ℝ) ^ 2 = 1 := by
      rcases abs_eq (zero_le_one) |>.mp h1 with rfl | rfl <;> simp
    rw [this, hn2]; linarith
  · have h2 : (2 : ℤ) ≤ |n| := by have := Int.one_le_abs hn; omega
    have h3 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : ((2 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h2
      have h4 : (2 : ℝ) ≤ |(n : ℝ)| := by simpa using this
      nlinarith [sq_abs (n : ℝ)]
    have := lam_ge h n
    nlinarith


/-! ### The reduced system on the line -/

/-- The bilinear form `B(f,h)_n = -q² n ∑_m m ĝ(mk) f_{n-m} h_m` of `E:eq:bilinear`
(`B(f,h) = Div(f ∇g*h)` along the line `ℤ k`). -/
def Bform (d : ℕ) (s : ℝ) (k : Lattice d) (f h : ℤ → ℂ) (n : ℤ) : ℂ :=
  -(((qk k) ^ 2 : ℝ) : ℂ) * (n : ℂ) *
    ∑' m : ℤ, (m : ℂ) * ((rieszCoeff d s (m • k) : ℝ) : ℂ) * f (n - m) * h m

/-- The right-hand side `mfRhsCoeff d s 0 β⁻¹` restricted to the line, as a map on sequences:
`a ↦ -β⁻¹ q² n² a_n + B(a,a)_n`.  (For `a = δ_0 + f` this is `-λ_n f_n + B(f,f)_n`, see
`reducedRhs_delta_add`.) -/
def reducedRhs (d : ℕ) (s β : ℝ) (k : Lattice d) (a : ℤ → ℂ) (n : ℤ) : ℂ :=
  -((β⁻¹ * (qk k) ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ) * a n + Bform d s k a a n

theorem coeffOf_zero_fun : coeffOf (fun _ : Torus d => (0 : ℝ)) = fun _ => 0 := by
  funext j
  simp [coeffOf, Torus.funFourierCoeff, UnitAddTorus.mFourierCoeff]

theorem sum_sq_lattice (k : Lattice d) : ∑ i, ((k i : ℤ) : ℂ) ^ 2 = ((Lattice.enorm k ^ 2 : ℝ) : ℂ) := by
  rw [enorm_sq_eq_sum]
  push_cast
  rfl

theorem mfRhsCoeff_lineCoeff (hk : k ≠ 0) (c : ℤ → ℂ) (n : ℤ) :
    mfRhsCoeff d s (fun _ => 0) β⁻¹ (lineCoeff k c) (n • k) = reducedRhs d s β k c n := by
  set u : ℂ := 2 * Real.pi * Complex.I with hu
  -- the inner coefficient sequences
  have hG : ∀ i : Fin d, (fun k' => derivCoeff i (coeffOf (fun _ : Torus d => (0 : ℝ))) k' +
      gradRieszCoeff d s i (lineCoeff k c) k') =
      lineCoeff k (fun m : ℤ => u * ((m : ℂ) * (k i : ℂ)) *
        (((rieszCoeff d s (m • k) : ℝ) : ℂ) * c m)) := by
    intro i
    funext k'
    rw [coeffOf_zero_fun]
    by_cases hk' : ∃ m : ℤ, k' = m • k
    · obtain ⟨m, rfl⟩ := hk'
      simp only [derivCoeff, gradRieszCoeff, rieszMult, lineCoeff_smul hk, Pi.smul_apply,
        smul_eq_mul, Int.cast_mul]
      ring
    · push Not at hk'
      simp [derivCoeff, gradRieszCoeff, rieszMult, lineCoeff_of_not_mem _ _ hk']
  have hterm : ∀ i : Fin d, derivCoeff i (mulCoeff (lineCoeff k c) (fun k' =>
      derivCoeff i (coeffOf (fun _ : Torus d => (0 : ℝ))) k' +
        gradRieszCoeff d s i (lineCoeff k c) k')) (n • k) =
      (u ^ 2 * (k i : ℂ) ^ 2 * (n : ℂ)) *
        ∑' m : ℤ, (m : ℂ) * ((rieszCoeff d s (m • k) : ℝ) : ℂ) * c (n - m) * c m := by
    intro i
    rw [hG i]
    simp only [derivCoeff]
    rw [mulCoeff_lineCoeff hk]
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    ring
  unfold mfRhsCoeff reducedRhs Bform
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have e1 : ∑ i : Fin d, u ^ 2 * (k i : ℂ) ^ 2 = - (((qk k) ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.mul_sum, sum_sq_lattice]
    have : u ^ 2 = -((4 * Real.pi ^ 2 : ℝ) : ℂ) := by
      rw [hu]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [this, qk]
    push_cast
    ring
  rw [e1]
  simp only [laplaceCoeff, enorm_zsmul, lineCoeff_smul hk]
  have : (|(n : ℝ)| * Lattice.enorm k) ^ 2 = (n : ℝ) ^ 2 * Lattice.enorm k ^ 2 := by
    rw [mul_pow, sq_abs]
  rw [this, qk]
  push_cast
  ring


theorem mfRhsCoeff_lineCoeff_off (c : ℤ → ℂ) (j : Lattice d)
    (hj : ∀ n : ℤ, j ≠ n • k) :
    mfRhsCoeff d s (fun _ => 0) β⁻¹ (lineCoeff k c) j = 0 := by
  have hρ := supportedOnLine_lineCoeff k c
  have hG : ∀ i : Fin d, SupportedOnLine k (fun k' =>
      derivCoeff i (coeffOf (fun _ : Torus d => (0 : ℝ))) k' +
      gradRieszCoeff d s i (lineCoeff k c) k') := by
    intro i k' hk'
    rw [coeffOf_zero_fun]
    simp [derivCoeff, gradRieszCoeff, rieszMult, hρ k' hk']
  unfold mfRhsCoeff
  rw [laplaceCoeff, hρ j hj]
  simp only [mul_zero, zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := mulCoeff_supportedOnLine' k _ _ hρ (hG i) j hj
  change (2 * Real.pi * Complex.I * (j i : ℂ)) * mulCoeff _ _ j = 0
  rw [this, mul_zero]


/-! ### Convolution on `ℤ` -/

/-- The shear `(n, m) ↦ (n - m, m)` of `ℤ × ℤ`. -/
def shear : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 - p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem summable_conv {x y : ℤ → ℝ} (hx : Summable x) (hy : Summable y) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) : Summable (fun p : ℤ × ℤ => x (p.1 - p.2) * y p.2) := by
  have := hx.mul_of_nonneg hy hx0 hy0
  exact (shear.summable_iff (f := fun p : ℤ × ℤ => x p.1 * y p.2)).mpr this

theorem tsum_conv {x y : ℤ → ℝ} (hx : Summable x) (hy : Summable y) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) : ∑' p : ℤ × ℤ, x (p.1 - p.2) * y p.2 = (∑' n, x n) * (∑' n, y n) := by
  have h1 : ∑' p : ℤ × ℤ, x p.1 * y p.2 = (∑' n, x n) * (∑' n, y n) :=
    (tsum_mul_tsum_of_summable_norm (by simpa [Real.norm_eq_abs, abs_of_nonneg (hx0 _)] using hx)
      (by simpa [Real.norm_eq_abs, abs_of_nonneg (hy0 _)] using hy)).symm
  rw [← h1]
  exact shear.tsum_eq (fun p : ℤ × ℤ => x p.1 * y p.2)

/-- Weighted convolution estimate: a kernel dominated by `K x(n-m) y(m)` has summable
row sums with total at most `K (∑ x)(∑ y)`. -/
theorem conv_kernel_le {x y : ℤ → ℝ} (hx : Summable x) (hy : Summable y) (hx0 : 0 ≤ x)
    (hy0 : 0 ≤ y) {K : ℝ} {a : ℤ → ℤ → ℝ} (ha0 : ∀ n m, 0 ≤ a n m)
    (ha : ∀ n m, a n m ≤ K * (x (n - m) * y m)) :
    (∀ n, Summable (a n)) ∧ Summable (fun n => ∑' m, a n m) ∧
      ∑' n, ∑' m, a n m ≤ K * ((∑' n, x n) * (∑' n, y n)) := by
  have hc := (summable_conv hx hy hx0 hy0).mul_left K
  have hP : Summable (fun p : ℤ × ℤ => a p.1 p.2) :=
    Summable.of_nonneg_of_le (fun p => ha0 _ _) (fun p => ha p.1 p.2) hc
  refine ⟨fun n => hP.prod_factor n, hP.prod, ?_⟩
  rw [← hP.tsum_prod, ← tsum_conv hx hy hx0 hy0, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun p => ha p.1 p.2) hP hc


theorem norm_rieszCoeff_zsmul_le (h : Hyp d s β k) (n : ℤ) :
    ‖((rieszCoeff d s (n • k) : ℝ) : ℂ)‖ ≤ rieszCoeff d s k := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rieszCoeff_nonneg' h _)]
  exact rieszCoeff_zsmul_le h n

/-- The Bform summand is summable when the first factor is bounded and the second has a first
moment. -/
theorem summable_Bterm (h : Hyp d s β k) (n : ℤ) {f g : ℤ → ℂ} {F : ℝ}
    (hF : ∀ j, ‖f j‖ ≤ F) (hg : Summable fun m : ℤ => (1 + |(m : ℝ)|) * ‖g m‖) :
    Summable fun m : ℤ => (m : ℂ) * ((rieszCoeff d s (m • k) : ℝ) : ℂ) * f (n - m) * g m := by
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0)
  refine Summable.of_norm_bounded (hg.mul_left (rieszCoeff d s k * F)) fun m => ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_intCast]
  have h1 := norm_rieszCoeff_zsmul_le h m
  have h2 := hF (n - m)
  have h3 : (|(m : ℝ)|) ≤ 1 + |(m : ℝ)| := by linarith
  have hg0 := norm_nonneg (g m)
  have hr := rieszCoeff_nonneg' h k
  calc |(m : ℝ)| * ‖((rieszCoeff d s (m • k) : ℝ) : ℂ)‖ * ‖f (n - m)‖ * ‖g m‖
      ≤ (1 + |(m : ℝ)|) * rieszCoeff d s k * F * ‖g m‖ := by
        gcongr
    _ = rieszCoeff d s k * F * ((1 + |(m : ℝ)|) * ‖g m‖) := by ring


/-- The sequence `δ_0`. -/
def deltaSeq : ℤ → ℂ := fun n => if n = 0 then 1 else 0

/-- The summability class of the perturbation `f = a - δ_0`: a first moment. -/
def Moment1 (f : ℤ → ℂ) : Prop := Summable fun m : ℤ => (1 + |(m : ℝ)|) * ‖f m‖

theorem Moment1.bdd {f : ℤ → ℂ} (hf : Moment1 f) (j : ℤ) :
    ‖f j‖ ≤ ∑' m : ℤ, (1 + |(m : ℝ)|) * ‖f m‖ := by
  refine le_trans ?_ (hf.le_tsum j (fun m _ => mul_nonneg (by positivity) (norm_nonneg _)))
  have : (1 : ℝ) ≤ 1 + |(j : ℝ)| := by linarith [abs_nonneg (j : ℝ)]
  nlinarith [norm_nonneg (f j)]

/-- On `a = δ_0 + f` the reduced right-hand side is `-λ_n f_n + B(f,f)_n`. -/
theorem reducedRhs_delta_add (h : Hyp d s β k) {f : ℤ → ℂ} (hf : Moment1 f) (n : ℤ) :
    reducedRhs d s β k (deltaSeq + f) n = -((lam d s β k n : ℝ) : ℂ) * f n + Bform d s k f f n := by
  set gm : ℤ → ℂ := fun m => ((rieszCoeff d s (m • k) : ℝ) : ℂ) with hgm
  have hT : ∀ m : ℤ, (m : ℂ) * gm m * (deltaSeq + f) (n - m) * (deltaSeq + f) m =
      (if m = n then (n : ℂ) * gm n * (deltaSeq + f) n else 0) +
        (m : ℂ) * gm m * f (n - m) * f m := by
    intro m
    by_cases hm : m = 0
    · subst hm
      by_cases h0 : (0 : ℤ) = n
      · subst h0; simp
      · simp [h0]
    · by_cases hmn : m = n
      · subst hmn
        simp [deltaSeq, hm]
        ring
      · have : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
        simp [deltaSeq, hm, hmn, this]
  have hV : Summable fun m : ℤ => (m : ℂ) * gm m * f (n - m) * f m :=
    summable_Bterm h n (fun j => hf.bdd j) hf
  have hU : HasSum (fun m : ℤ => if m = n then (n : ℂ) * gm n * (deltaSeq + f) n else 0)
      ((n : ℂ) * gm n * (deltaSeq + f) n) := hasSum_ite_eq n _
  have hsum : ∑' m : ℤ, (m : ℂ) * gm m * (deltaSeq + f) (n - m) * (deltaSeq + f) m =
      (n : ℂ) * gm n * (deltaSeq + f) n + ∑' m : ℤ, (m : ℂ) * gm m * f (n - m) * f m := by
    simp_rw [hT]
    rw [(hU.summable.hasSum.add hV.hasSum).tsum_eq, hU.tsum_eq]
  unfold reducedRhs Bform
  rw [hsum, lam_eq]
  by_cases hn : n = 0
  · subst hn; simp
  · have : (deltaSeq + f) n = f n := by simp [deltaSeq, hn]
    rw [this]
    push_cast
    ring


/-! ### The Duhamel operator on bounded continuous functions of time -/

/-- Bounded continuous real functions of time. -/
abbrev Bc := ℝ →ᵇ ℝ

theorem integral_exp_mul_real (c τ : ℝ) (hc : c ≠ 0) :
    ∫ σ in (0 : ℝ)..τ, Real.exp (c * σ) = (Real.exp (c * τ) - 1) / c := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun σ => Real.exp (c * σ) / c)]
  · simp [sub_div]
  · intro σ _
    have h := ((hasDerivAt_id σ).const_mul c).exp.div_const c
    simp only [id, mul_one] at h
    rwa [mul_div_cancel_right₀ _ hc] at h
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

/-- The damped Duhamel integral, clipped to `t ≥ 0`:
`(duhF c ω φ)(t) = e^{-c t⁺} ∫_0^{t⁺} e^{(c-ω)σ} φ(σ) dσ
  = ∫_0^{t⁺} e^{-c(t⁺-σ)} e^{-ωσ} φ(σ) dσ`. -/
def duhF (c ω : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(c * max t 0)) * ∫ σ in (0 : ℝ)..max t 0, Real.exp ((c - ω) * σ) * φ σ

theorem duhF_continuous (c ω : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) : Continuous (duhF c ω φ) := by
  unfold duhF
  have h1 : Continuous fun u : ℝ => ∫ σ in (0 : ℝ)..u, Real.exp ((c - ω) * σ) * φ σ :=
    intervalIntegral.continuous_primitive (fun a b => (Continuous.intervalIntegrable
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hφ) _ _)) 0
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.max continuous_const)).neg).mul
    (h1.comp (continuous_id.max continuous_const))

theorem duhF_bound {c ω : ℝ} (hc : 0 < c) (hω : 0 ≤ ω) {φ : ℝ → ℝ} {M : ℝ}
    (hM : ∀ σ, |φ σ| ≤ M) (t : ℝ) : |duhF c ω φ t| ≤ M / c := by
  unfold duhF
  set τ := max t 0 with hτ
  have hτ0 : 0 ≤ τ := le_max_right _ _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |∫ σ in (0 : ℝ)..τ, Real.exp ((c - ω) * σ) * φ σ| ≤
      ∫ σ in (0 : ℝ)..τ, M * Real.exp (c * σ) := by
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hτ0
      (Filter.Eventually.of_forall fun σ hσ => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp ((c - ω) * σ) * |φ σ| ≤ Real.exp (c * σ) * M := by
            refine mul_le_mul (Real.exp_le_exp.mpr ?_) (hM σ) (abs_nonneg _) (Real.exp_pos _).le
            nlinarith [hσ.1]
        _ = M * Real.exp (c * σ) := by ring
    · exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have h2 : ∫ σ in (0 : ℝ)..τ, M * Real.exp (c * σ) = M * ((Real.exp (c * τ) - 1) / c) := by
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_real c τ hc.ne']
  calc Real.exp (-(c * τ)) * |∫ σ in (0 : ℝ)..τ, Real.exp ((c - ω) * σ) * φ σ|
      ≤ Real.exp (-(c * τ)) * (M * ((Real.exp (c * τ) - 1) / c)) := by
        gcongr; exact h1.trans h2.le
    _ = M / c * (1 - Real.exp (-(c * τ))) := by
        have : Real.exp (-(c * τ)) * Real.exp (c * τ) = 1 := by rw [← Real.exp_add]; simp
        field_simp
        nlinarith [this]
    _ ≤ M / c := by
        have : 0 ≤ M / c := div_nonneg hM0 hc.le
        have := Real.exp_pos (-(c * τ))
        nlinarith

theorem duhF_add (c ω : ℝ) {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (t : ℝ) :
    duhF c ω (fun σ => φ σ + ψ σ) t = duhF c ω φ t + duhF c ω ψ t := by
  unfold duhF
  rw [← mul_add, ← intervalIntegral.integral_add]
  · simp only [mul_add]
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hφ).intervalIntegrable _ _
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hψ).intervalIntegrable _ _

theorem duhF_smul (c ω a : ℝ) (φ : ℝ → ℝ) (t : ℝ) :
    duhF c ω (fun σ => a * φ σ) t = a * duhF c ω φ t := by
  unfold duhF
  have : ∀ σ, Real.exp ((c - ω) * σ) * (a * φ σ) = a * (Real.exp ((c - ω) * σ) * φ σ) := fun σ => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The Duhamel operator as a bounded continuous function, for `c > 0`, `ω ≥ 0`. -/
def duhB (c ω : ℝ) (hc : 0 < c) (hω : 0 ≤ ω) (φ : Bc) : Bc :=
  BoundedContinuousFunction.ofNormedAddCommGroup (duhF c ω φ) (duhF_continuous c ω φ.continuous)
    (‖φ‖ / c) (fun t => by
      rw [Real.norm_eq_abs]
      exact duhF_bound hc hω (fun σ => by rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm σ) t)

theorem duhB_apply (c ω : ℝ) (hc : 0 < c) (hω : 0 ≤ ω) (φ : Bc) (t : ℝ) :
    duhB c ω hc hω φ t = duhF c ω φ t := rfl

/-- The Duhamel operator as a continuous linear map `C_b(ℝ) → C_b(ℝ)`. -/
def duhL (c ω : ℝ) (hc : 0 < c) (hω : 0 ≤ ω) : Bc →L[ℝ] Bc :=
  LinearMap.mkContinuous
    { toFun := duhB c ω hc hω
      map_add' := fun φ ψ => by
        ext t
        simp only [duhB_apply, BoundedContinuousFunction.coe_add, Pi.add_apply]
        exact duhF_add c ω φ.continuous ψ.continuous t
      map_smul' := fun a φ => by
        ext t
        simp only [duhB_apply, BoundedContinuousFunction.coe_smul, smul_eq_mul, RingHom.id_apply]
        exact duhF_smul c ω a φ t }
    (1 / c) (fun φ => by
      show ‖duhB c ω hc hω φ‖ ≤ 1 / c * ‖φ‖
      have : ‖duhB c ω hc hω φ‖ ≤ ‖φ‖ / c := by
        refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun t => ?_
        rw [duhB_apply, Real.norm_eq_abs]
        exact duhF_bound hc hω (fun σ => by rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm σ) t
      calc ‖duhB c ω hc hω φ‖ ≤ ‖φ‖ / c := this
        _ = 1 / c * ‖φ‖ := by ring)

open Classical in
/-- The Duhamel operator for arbitrary `c, ω` (zero unless `c > 0`, `ω ≥ 0`). -/
def duhLg (c ω : ℝ) : Bc →L[ℝ] Bc :=
  if h : 0 < c ∧ 0 ≤ ω then duhL c ω h.1 h.2 else 0

theorem duhLg_apply {c ω : ℝ} (hc : 0 < c) (hω : 0 ≤ ω) (φ : Bc) (t : ℝ) :
    duhLg c ω φ t = duhF c ω φ t := by
  unfold duhLg
  split_ifs with h
  · rfl
  · exact absurd ⟨hc, hω⟩ h

theorem norm_duhLg_le {c ω : ℝ} (hc : 0 < c) (hω : 0 ≤ ω) (φ : Bc) :
    ‖duhLg c ω φ‖ ≤ ‖φ‖ / c := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun t => ?_
  rw [duhLg_apply hc hω, Real.norm_eq_abs]
  exact duhF_bound hc hω (fun σ => by rw [← Real.norm_eq_abs]; exact φ.norm_coe_le_norm σ) t


/-! ### Weights and the kernel of the bilinear map -/

/-- The weight `w(n) = e^{|n|}(1+|n|)` of the analytic-type norm. -/
def wt (n : ℤ) : ℝ := Real.exp |(n : ℝ)| * (1 + |(n : ℝ)|)

theorem wt_pos (n : ℤ) : 0 < wt n := by unfold wt; positivity

theorem one_add_le_wt (n : ℤ) : 1 + |(n : ℝ)| ≤ wt n := by
  unfold wt
  have : 1 ≤ Real.exp |(n : ℝ)| := Real.one_le_exp (abs_nonneg _)
  nlinarith [abs_nonneg (n : ℝ)]

theorem wt_neg (n : ℤ) : wt (-n) = wt n := by simp [wt]

theorem abs_cast_sub_le (n m : ℤ) : |(n : ℝ)| ≤ |((n - m : ℤ) : ℝ)| + |(m : ℝ)| := by
  push_cast
  calc |(n : ℝ)| = |((n : ℝ) - m) + m| := by ring_nf
    _ ≤ _ := abs_add_le _ _

/-- Key weight inequality: `w(n)|m| ≤ 2|n| w(n-m) w(m)` for `n ≠ 0`. -/
theorem wt_mul_abs_le {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    wt n * |(m : ℝ)| ≤ 2 * |(n : ℝ)| * (wt (n - m) * wt m) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using this
  have h1 : Real.exp |(n : ℝ)| ≤ Real.exp |((n - m : ℤ) : ℝ)| * Real.exp |(m : ℝ)| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (abs_cast_sub_le n m)
  have h2 : (1 + |(n : ℝ)|) ≤ 2 * |(n : ℝ)| := by linarith
  have hm0 := abs_nonneg (m : ℝ)
  have hnm0 := abs_nonneg (((n - m : ℤ) : ℝ))
  unfold wt
  have e0 := Real.exp_pos |(n : ℝ)|
  have e1 := Real.exp_pos |((n - m : ℤ) : ℝ)|
  have e2 := Real.exp_pos |(m : ℝ)|
  calc Real.exp |(n : ℝ)| * (1 + |(n : ℝ)|) * |(m : ℝ)|
      ≤ Real.exp |(n : ℝ)| * (2 * |(n : ℝ)|) * |(m : ℝ)| := by gcongr
    _ = 2 * |(n : ℝ)| * (Real.exp |(n : ℝ)| * |(m : ℝ)|) := by ring
    _ ≤ 2 * |(n : ℝ)| * ((Real.exp |((n - m : ℤ) : ℝ)| * Real.exp |(m : ℝ)|) * (1 + |(m : ℝ)|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h1 (by linarith) hm0 (by positivity)
    _ ≤ 2 * |(n : ℝ)| * (Real.exp |((n - m : ℤ) : ℝ)| * (1 + |((n - m : ℤ) : ℝ)|) *
          (Real.exp |(m : ℝ)| * (1 + |(m : ℝ)|))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h3 : 0 ≤ Real.exp |((n - m : ℤ) : ℝ)| * Real.exp |(m : ℝ)| * (1 + |(m : ℝ)|) :=
          by positivity
        nlinarith [mul_nonneg h3 hnm0]

/-- The kernel `k(n,m) = -q² n m ĝ(mk) / (w(n-m) w(m))` of the weighted bilinear map. -/
def kc (s : ℝ) (k : Lattice d) (n m : ℤ) : ℝ :=
  -(qk k ^ 2) * (n : ℝ) * (m : ℝ) * rieszCoeff d s (m • k) / (wt (n - m) * wt m)

theorem kc_zero_left (s : ℝ) (k : Lattice d) (m : ℤ) : kc s k 0 m = 0 := by simp [kc]

theorem kc_neg (s : ℝ) (k : Lattice d) (n m : ℤ) : kc s k (-n) (-m) = kc s k n m := by
  unfold kc
  have h1 : -n - -m = -(n - m) := by ring
  rw [h1, wt_neg, wt_neg, neg_smul, rieszCoeff_neg]
  push_cast
  ring

theorem abs_kc_le (h : Hyp d s β k) (n m : ℤ) :
    |kc s k n m| ≤ qk k ^ 2 * rieszCoeff d s k := by
  unfold kc
  have hg0 := rieszCoeff_nonneg' h (m • k)
  have hg1 := rieszCoeff_zsmul_le h m
  have hg := rieszCoeff_nonneg' h k
  have hq : 0 ≤ qk k ^ 2 := sq_nonneg _
  have hden : 0 < wt (n - m) * wt m := mul_pos (wt_pos _) (wt_pos _)
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have e : |-(qk k ^ 2) * (n : ℝ) * (m : ℝ) * rieszCoeff d s (m • k)| =
      qk k ^ 2 * (|(n : ℝ)| * |(m : ℝ)|) * rieszCoeff d s (m • k) := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hq, abs_of_nonneg hg0]
    ring
  rw [e]
  -- |n||m| ≤ w(n-m) w(m)
  have hnm : |(n : ℝ)| * |(m : ℝ)| ≤ wt (n - m) * wt m := by
    have h1 : Real.exp |(n : ℝ)| ≤ Real.exp |((n - m : ℤ) : ℝ)| * Real.exp |(m : ℝ)| := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (abs_cast_sub_le n m)
    have h2 : |(n : ℝ)| ≤ Real.exp |(n : ℝ)| := by
      have := Real.add_one_le_exp |(n : ℝ)|; linarith
    have hm0 := abs_nonneg (m : ℝ)
    have hnm0 := abs_nonneg (((n - m : ℤ) : ℝ))
    unfold wt
    have e1 := Real.exp_pos |((n - m : ℤ) : ℝ)|
    have e2 := Real.exp_pos |(m : ℝ)|
    calc |(n : ℝ)| * |(m : ℝ)| ≤ Real.exp |(n : ℝ)| * (1 + |(m : ℝ)|) := by
          apply mul_le_mul h2 (by linarith) hm0 (Real.exp_pos _).le
      _ ≤ (Real.exp |((n - m : ℤ) : ℝ)| * Real.exp |(m : ℝ)|) * (1 + |(m : ℝ)|) := by gcongr
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg e1.le e2.le) (mul_nonneg hnm0 (by linarith : (0:ℝ) ≤ 1 + |(m : ℝ)|))]
  calc qk k ^ 2 * (|(n : ℝ)| * |(m : ℝ)|) * rieszCoeff d s (m • k)
      ≤ qk k ^ 2 * (wt (n - m) * wt m) * rieszCoeff d s k := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hnm hq) hg1 hg0 (by positivity)
    _ = qk k ^ 2 * rieszCoeff d s k * (wt (n - m) * wt m) := by ring

theorem wt_abs_kc_le (h : Hyp d s β k) {n : ℤ} (hn : n ≠ 0) (m : ℤ) :
    wt n * |kc s k n m| ≤ 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 := by
  unfold kc
  have hg0 := rieszCoeff_nonneg' h (m • k)
  have hg1 := rieszCoeff_zsmul_le h m
  have hg := rieszCoeff_nonneg' h k
  have hq : 0 ≤ qk k ^ 2 := sq_nonneg _
  have hden : 0 < wt (n - m) * wt m := mul_pos (wt_pos _) (wt_pos _)
  have key := wt_mul_abs_le hn m
  rw [abs_div, abs_of_pos hden]
  have e : |-(qk k ^ 2) * (n : ℝ) * (m : ℝ) * rieszCoeff d s (m • k)| =
      qk k ^ 2 * |(n : ℝ)| * |(m : ℝ)| * rieszCoeff d s (m • k) := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hq, abs_of_nonneg hg0]
  rw [e, ← mul_div_assoc, div_le_iff₀ hden]
  have hn0 := abs_nonneg (n : ℝ)
  calc wt n * (qk k ^ 2 * |(n : ℝ)| * |(m : ℝ)| * rieszCoeff d s (m • k))
      = (qk k ^ 2 * |(n : ℝ)| * rieszCoeff d s (m • k)) * (wt n * |(m : ℝ)|) := by ring
    _ ≤ (qk k ^ 2 * |(n : ℝ)| * rieszCoeff d s k) * (2 * |(n : ℝ)| * (wt (n - m) * wt m)) := by
        apply mul_le_mul _ key (mul_nonneg (wt_pos n).le (abs_nonneg _))
          (mul_nonneg (mul_nonneg hq hn0) hg)
        exact mul_le_mul_of_nonneg_left hg1 (mul_nonneg hq hn0)
    _ = 2 * qk k ^ 2 * rieszCoeff d s k * (|(n : ℝ)| * |(n : ℝ)|) * (wt (n - m) * wt m) := by ring
    _ = 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 * (wt (n - m) * wt m) := by
        rw [← sq, sq_abs]


/-! ### The bilinear map `Q` on `ℓ¹(ℤ; C_b)` -/

/-- The damping exponent `ω = 3λ/4`. -/
def omg (d : ℕ) (s β : ℝ) (k : Lattice d) : ℝ := (3 / 4) * transientRate d s β k

/-- `P(x,y)_n = ∑_m k(n,m) x_{n-m} y_m` (pointwise product of bounded continuous functions). -/
def Pseq (s : ℝ) (k : Lattice d) (x y : ℤ → Bc) (n : ℤ) : Bc :=
  ∑' m : ℤ, kc s k n m • (x (n - m) * y m)

/-- `Q(x,y)_n = w(n) D_n P(x,y)_n`. -/
def Qseq (d : ℕ) (s β : ℝ) (k : Lattice d) (x y : ℤ → Bc) (n : ℤ) : Bc :=
  wt n • duhLg (lam d s β k n - omg d s β k) (omg d s β k) (Pseq s k x y n)

/-- The bilinear constant. -/
def Kc (d : ℕ) (s β : ℝ) (k : Lattice d) : ℝ :=
  8 * qk k ^ 2 * rieszCoeff d s k / transientRate d s β k

theorem Kc_nonneg (h : Hyp d s β k) : 0 ≤ Kc d s β k := by
  have := rieszCoeff_nonneg' h k
  have := lam_pos h
  unfold Kc
  positivity

theorem omg_nonneg (h : Hyp d s β k) : 0 ≤ omg d s β k := by
  unfold omg; have := lam_pos h; positivity

theorem lam_sub_omg_pos (h : Hyp d s β k) {n : ℤ} (hn : n ≠ 0) :
    0 < lam d s β k n - omg d s β k := by
  have h1 := lam_sub_ge h hn
  have h2 := lam_pos h
  have h3 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  unfold omg
  nlinarith

theorem summable_conv_norm {x y : ℤ → Bc} (hx : Summable fun j => ‖x j‖) (hy : Summable fun j => ‖y j‖)
    (n : ℤ) : Summable fun m => ‖x (n - m)‖ * ‖y m‖ :=
  (conv_kernel_le (a := fun n m => ‖x (n - m)‖ * ‖y m‖) (K := 1) hx hy (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (fun _ _ => by positivity) (fun _ _ => by simp)).1 n

theorem summable_P_terms (h : Hyp d s β k) {x y : ℤ → Bc} (hx : Summable fun j => ‖x j‖)
    (hy : Summable fun j => ‖y j‖) (n : ℤ) :
    Summable fun m => ‖kc s k n m • (x (n - m) * y m)‖ := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
    ((summable_conv_norm hx hy n).mul_left (qk k ^ 2 * rieszCoeff d s k))
  rw [norm_smul, Real.norm_eq_abs]
  calc |kc s k n m| * ‖x (n - m) * y m‖
      ≤ (qk k ^ 2 * rieszCoeff d s k) * (‖x (n - m)‖ * ‖y m‖) :=
        mul_le_mul (abs_kc_le h n m) (norm_mul_le _ _) (norm_nonneg _)
          (mul_nonneg (sq_nonneg _) (rieszCoeff_nonneg' h k))
    _ = _ := rfl

theorem norm_Pseq_le (h : Hyp d s β k) {x y : ℤ → Bc} (hx : Summable fun j => ‖x j‖)
    (hy : Summable fun j => ‖y j‖) (n : ℤ) :
    ‖Pseq s k x y n‖ ≤ ∑' m, |kc s k n m| * (‖x (n - m)‖ * ‖y m‖) := by
  unfold Pseq
  refine (norm_tsum_le_tsum_norm (summable_P_terms h hx hy n)).trans ?_
  refine Summable.tsum_le_tsum (fun m => ?_) (summable_P_terms h hx hy n) ?_
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)
  · refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_conv_norm hx hy n).mul_left (qk k ^ 2 * rieszCoeff d s k))
    exact mul_le_mul (abs_kc_le h n m) le_rfl (by positivity)
      (mul_nonneg (sq_nonneg _) (rieszCoeff_nonneg' h k)) |>.trans_eq rfl

theorem Pseq_zero (x y : ℤ → Bc) : Pseq s k x y 0 = 0 := by
  unfold Pseq
  simp [kc_zero_left]

theorem norm_Qseq_le (h : Hyp d s β k) {x y : ℤ → Bc} (hx : Summable fun j => ‖x j‖)
    (hy : Summable fun j => ‖y j‖) (n : ℤ) :
    ‖Qseq d s β k x y n‖ ≤ Kc d s β k * ∑' m, ‖x (n - m)‖ * ‖y m‖ := by
  have hK := Kc_nonneg h
  have hsum := summable_conv_norm hx hy n
  by_cases hn : n = 0
  · subst hn
    unfold Qseq
    rw [Pseq_zero]
    simp only [map_zero, smul_zero, norm_zero]
    exact mul_nonneg hK (tsum_nonneg fun m => by positivity)
  · have hc := lam_sub_omg_pos h hn
    have hl := lam_pos h
    unfold Qseq
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (wt_pos n)]
    have h1 := norm_duhLg_le hc (omg_nonneg h) (Pseq s k x y n)
    have h2 := norm_Pseq_le h hx hy n
    have hterm : ∀ m, wt n * |kc s k n m| / (lam d s β k n - omg d s β k) ≤ Kc d s β k := by
      intro m
      rw [div_le_iff₀ hc]
      have h3 := wt_abs_kc_le h hn m
      have h4 := lam_sub_ge h hn
      have h5 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      unfold Kc
      rw [div_mul_eq_mul_div, le_div_iff₀ hl]
      have hg := rieszCoeff_nonneg' h k
      calc wt n * |kc s k n m| * transientRate d s β k
          ≤ 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 * transientRate d s β k :=
            mul_le_mul_of_nonneg_right h3 hl.le
        _ = 8 * qk k ^ 2 * rieszCoeff d s k * ((1 / 4) * (n : ℝ) ^ 2 * transientRate d s β k) := by ring
        _ ≤ 8 * qk k ^ 2 * rieszCoeff d s k * (lam d s β k n - omg d s β k) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            unfold omg; linarith
    calc wt n * ‖duhLg (lam d s β k n - omg d s β k) (omg d s β k) (Pseq s k x y n)‖
        ≤ wt n * (‖Pseq s k x y n‖ / (lam d s β k n - omg d s β k)) :=
          mul_le_mul_of_nonneg_left h1 (wt_pos n).le
      _ ≤ wt n * ((∑' m, |kc s k n m| * (‖x (n - m)‖ * ‖y m‖)) /
            (lam d s β k n - omg d s β k)) := by
          apply mul_le_mul_of_nonneg_left _ (wt_pos n).le
          exact div_le_div_of_nonneg_right h2 hc.le
      _ = ∑' m, (wt n * |kc s k n m| / (lam d s β k n - omg d s β k)) * (‖x (n - m)‖ * ‖y m‖) := by
          rw [← tsum_div_const, ← tsum_mul_left]
          refine tsum_congr fun m => ?_
          ring
      _ ≤ ∑' m, Kc d s β k * (‖x (n - m)‖ * ‖y m‖) := by
          refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hsum.mul_left _)
          · exact mul_le_mul_of_nonneg_right (hterm m) (by positivity)
          · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hsum.mul_left (Kc d s β k))
            · exact mul_nonneg (div_nonneg (mul_nonneg (wt_pos n).le (abs_nonneg _)) hc.le) (by positivity)
            · exact mul_le_mul_of_nonneg_right (hterm m) (by positivity)
      _ = Kc d s β k * ∑' m, ‖x (n - m)‖ * ‖y m‖ := tsum_mul_left


/-! ### A fixed-point lemma for quadratic equations -/

theorem exists_fixed_point_bilinear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (S : Set E) (hS : IsClosed S) (Q : E → E → E) (κ : ℝ) (hκ : 0 ≤ κ)
    (hQ : ∀ x y, ‖Q x y‖ ≤ κ * ‖x‖ * ‖y‖)
    (hQl : ∀ x x' y, Q (x - x') y = Q x y - Q x' y)
    (hQr : ∀ x y y', Q x (y - y') = Q x y - Q x y')
    (L : E) (R : ℝ) (hR0 : 0 ≤ R) (hL : ‖L‖ ≤ R / 2) (hLS : L ∈ S) (hR : 4 * κ * R ≤ 1)
    (hT : ∀ x ∈ S, L + Q x x ∈ S) :
    ∃ x ∈ S, ‖x‖ ≤ R ∧ x = L + Q x x := by
  set X : Set E := S ∩ Metric.closedBall 0 R with hX
  have hXc : IsClosed X := hS.inter Metric.isClosed_closedBall
  have : CompleteSpace X := hXc.completeSpace_coe
  have hLX : L ∈ X := ⟨hLS, by rw [mem_closedBall_zero_iff]; linarith⟩
  have : Nonempty X := ⟨⟨L, hLX⟩⟩
  have hmaps : ∀ x ∈ X, L + Q x x ∈ X := by
    intro x hx
    refine ⟨hT x hx.1, ?_⟩
    have hx2 : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx.2
    rw [mem_closedBall_zero_iff]
    calc ‖L + Q x x‖ ≤ ‖L‖ + ‖Q x x‖ := norm_add_le _ _
      _ ≤ R / 2 + κ * R * R := by
          have := hQ x x
          have h1 : κ * ‖x‖ * ‖x‖ ≤ κ * R * R := by
            gcongr
          linarith
      _ ≤ R := by nlinarith
  let T : X → X := fun x => ⟨L + Q x x, hmaps x x.2⟩
  have hTc : ContractingWith (1 / 2 : NNReal) T := by
    refine ⟨by rw [show (1 / 2 : NNReal) = 2⁻¹ from one_div 2]; exact_mod_cast (by norm_num : (2:NNReal)⁻¹ < 1), ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    show ‖(L + Q x x) - (L + Q y y)‖ ≤ ((1 / 2 : NNReal) : ℝ) * ‖(x : E) - y‖
    have e : (L + Q x x) - (L + Q y y) = Q (x - y) x + Q y (x - y) := by
      rw [hQl, hQr]; abel
    rw [e]
    have hx : ‖(x : E)‖ ≤ R := by simpa using x.2.2
    have hy : ‖(y : E)‖ ≤ R := by simpa using y.2.2
    calc ‖Q ((x : E) - y) x + Q y ((x : E) - y)‖ ≤ ‖Q ((x : E) - y) x‖ + ‖Q y ((x : E) - y)‖ :=
          norm_add_le _ _
      _ ≤ κ * ‖(x : E) - y‖ * ‖(x : E)‖ + κ * ‖(y : E)‖ * ‖(x : E) - y‖ := add_le_add (hQ _ _) (hQ _ _)
      _ ≤ κ * ‖(x : E) - y‖ * R + κ * R * ‖(x : E) - y‖ := by
          gcongr
      _ ≤ ((1 / 2 : NNReal) : ℝ) * ‖(x : E) - y‖ := by
          have : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
          rw [this]
          nlinarith [norm_nonneg ((x : E) - y), mul_nonneg hκ hR0]
  obtain ⟨fp, hfp⟩ : ∃ fp : X, T fp = fp := ⟨ContractingWith.fixedPoint T hTc,
    ContractingWith.fixedPoint_isFixedPt (f := T) (hf := hTc)⟩
  refine ⟨fp, fp.2.1, mem_closedBall_zero_iff.mp fp.2.2, ?_⟩
  exact (congrArg Subtype.val hfp).symm


/-! ### The Banach space `ℓ¹(ℤ; C_b)` and the bilinear map on it -/

/-- The Banach space `ℓ¹(ℤ; C_b(ℝ))`. -/
abbrev E1 := lp (fun _ : ℤ => Bc) 1

theorem memlp1_iff (f : ∀ _ : ℤ, Bc) : Memℓp f 1 ↔ Summable fun i => ‖f i‖ := by
  rw [memℓp_gen_iff (by simp)]; simp

theorem lp1_norm (x : E1) : ‖x‖ = ∑' i, ‖x i‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp)]; simp

theorem lp1_summable (x : E1) : Summable fun i => ‖x i‖ := (memlp1_iff _).mp x.2

theorem summable_rows {x y : ℤ → Bc} (hx : Summable fun j => ‖x j‖)
    (hy : Summable fun j => ‖y j‖) :
    Summable (fun n => ∑' m, ‖x (n - m)‖ * ‖y m‖) ∧
      ∑' n, ∑' m, ‖x (n - m)‖ * ‖y m‖ ≤ (∑' j, ‖x j‖) * (∑' j, ‖y j‖) := by
  have := conv_kernel_le (a := fun n m => ‖x (n - m)‖ * ‖y m‖) (K := 1) hx hy
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ _ => by positivity) (fun _ _ => by simp)
  refine ⟨this.2.1, ?_⟩
  simpa using this.2.2

theorem summable_Qseq (h : Hyp d s β k) (x y : E1) :
    Summable fun n => ‖Qseq d s β k x y n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_Qseq_le h (lp1_summable x) (lp1_summable y) n)
    ((summable_rows (lp1_summable x) (lp1_summable y)).1.mul_left _)

/-- The bilinear map `Q` on `ℓ¹(ℤ; C_b)`. -/
def Qlp (h : Hyp d s β k) (x y : E1) : E1 :=
  ⟨Qseq d s β k x y, (memlp1_iff _).mpr (summable_Qseq h x y)⟩

theorem Qlp_apply (h : Hyp d s β k) (x y : E1) (n : ℤ) :
    Qlp h x y n = Qseq d s β k x y n := rfl

theorem norm_Qlp_le (h : Hyp d s β k) (x y : E1) : ‖Qlp h x y‖ ≤ Kc d s β k * ‖x‖ * ‖y‖ := by
  have hK := Kc_nonneg h
  have hr := summable_rows (lp1_summable x) (lp1_summable y)
  rw [lp1_norm (Qlp h x y)]
  calc ∑' n, ‖Qlp h x y n‖ ≤ ∑' n, Kc d s β k * ∑' m, ‖x (n - m)‖ * ‖y m‖ :=
        Summable.tsum_le_tsum (fun n => norm_Qseq_le h (lp1_summable x) (lp1_summable y) n)
          (summable_Qseq h x y) (hr.1.mul_left _)
    _ = Kc d s β k * ∑' n, ∑' m, ‖x (n - m)‖ * ‖y m‖ := tsum_mul_left
    _ ≤ Kc d s β k * ((∑' j, ‖x j‖) * (∑' j, ‖y j‖)) := mul_le_mul_of_nonneg_left hr.2 hK
    _ = Kc d s β k * ‖x‖ * ‖y‖ := by rw [lp1_norm x, lp1_norm y]; ring


theorem Pseq_sub_left (h : Hyp d s β k) {x x' y : ℤ → Bc} (hx : Summable fun j => ‖x j‖)
    (hx' : Summable fun j => ‖x' j‖) (hy : Summable fun j => ‖y j‖) (n : ℤ) :
    Pseq s k (x - x') y n = Pseq s k x y n - Pseq s k x' y n := by
  unfold Pseq
  rw [← Summable.tsum_sub (summable_P_terms h hx hy n).of_norm
    (summable_P_terms h hx' hy n).of_norm]
  refine tsum_congr fun m => ?_
  simp [sub_mul, smul_sub]

theorem Pseq_sub_right (h : Hyp d s β k) {x y y' : ℤ → Bc} (hx : Summable fun j => ‖x j‖)
    (hy : Summable fun j => ‖y j‖) (hy' : Summable fun j => ‖y' j‖) (n : ℤ) :
    Pseq s k x (y - y') n = Pseq s k x y n - Pseq s k x y' n := by
  unfold Pseq
  rw [← Summable.tsum_sub (summable_P_terms h hx hy n).of_norm
    (summable_P_terms h hx hy' n).of_norm]
  refine tsum_congr fun m => ?_
  simp [mul_sub, smul_sub]

theorem Qlp_sub_left (h : Hyp d s β k) (x x' y : E1) :
    Qlp h (x - x') y = Qlp h x y - Qlp h x' y := by
  refine lp.ext (funext fun n => ?_)
  simp only [Qlp_apply, Qseq, lp.coeFn_sub, Pi.sub_apply]
  rw [Pseq_sub_left h (lp1_summable x) (lp1_summable x') (lp1_summable y), map_sub, smul_sub]

theorem Qlp_sub_right (h : Hyp d s β k) (x y y' : E1) :
    Qlp h x (y - y') = Qlp h x y - Qlp h x y' := by
  refine lp.ext (funext fun n => ?_)
  simp only [Qlp_apply, Qseq, lp.coeFn_sub, Pi.sub_apply]
  rw [Pseq_sub_right h (lp1_summable x) (lp1_summable y) (lp1_summable y'), map_sub, smul_sub]


/-! ### Evenness -/

/-- Evenness of a sequence of functions: `x_{-n} = x_n`. -/
def EvenSeq (x : ℤ → Bc) : Prop := ∀ n, x (-n) = x n

theorem Pseq_even {x y : ℤ → Bc} (hx : EvenSeq x) (hy : EvenSeq y) (n : ℤ) :
    Pseq s k x y (-n) = Pseq s k x y n := by
  unfold Pseq
  rw [← (Equiv.neg ℤ).tsum_eq (fun m => kc s k (-n) m • (x (-n - m) * y m))]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply]
  have h1 : -n - -m = -(n - m) := by ring
  rw [kc_neg, h1, hx, hy]

theorem Qseq_even {x y : ℤ → Bc} (hx : EvenSeq x) (hy : EvenSeq y) (n : ℤ) :
    Qseq d s β k x y (-n) = Qseq d s β k x y n := by
  unfold Qseq
  rw [Pseq_even hx hy, wt_neg, lam_neg]

theorem Qlp_even (h : Hyp d s β k) {x y : E1} (hx : EvenSeq x) (hy : EvenSeq y) :
    EvenSeq (Qlp h x y) := fun n => Qseq_even hx hy n


/-! ### The initial datum and the fixed point -/

/-- The decaying exponential `t ↦ e^{-a t⁺}` as a bounded continuous function. -/
def expDec (a : ℝ) (ha : 0 ≤ a) : Bc :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t : ℝ => Real.exp (-(a * max t 0)))
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const)).neg) 1
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have : 0 ≤ a * max t 0 := mul_nonneg ha (le_max_right _ _)
      exact Real.exp_le_one_iff.mpr (by linarith))

theorem expDec_apply (a : ℝ) (ha : 0 ≤ a) (t : ℝ) : expDec a ha t = Real.exp (-(a * max t 0)) := rfl

theorem norm_expDec_le (a : ℝ) (ha : 0 ≤ a) : ‖expDec a ha‖ ≤ 1 := by
  refine (BoundedContinuousFunction.norm_le zero_le_one).mpr fun t => ?_
  rw [expDec_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : 0 ≤ a * max t 0 := mul_nonneg ha (le_max_right _ _)
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- The initial coefficients `f0_n = (ε/√2)(δ_1 + δ_{-1})` of `ε ψ_k`. -/
def f0 (ε : ℝ) (n : ℤ) : ℝ := if n = 1 ∨ n = -1 then ε / Real.sqrt 2 else 0

theorem lam_div_four_nonneg (h : Hyp d s β k) : 0 ≤ transientRate d s β k / 4 := by
  have := lam_pos h; positivity

/-- The one-mode piece of the initial datum. -/
def Lbc (h : Hyp d s β k) (ε : ℝ) : Bc :=
  (wt 1 * (ε / Real.sqrt 2)) • expDec (transientRate d s β k / 4) (lam_div_four_nonneg h)

/-- The linear part `L` of the fixed-point equation: the initial datum, damped. -/
def Linit (h : Hyp d s β k) (ε : ℝ) : E1 := lp.single 1 1 (Lbc h ε) + lp.single 1 (-1) (Lbc h ε)

theorem Linit_apply_one (h : Hyp d s β k) (ε : ℝ) : Linit h ε 1 = Lbc h ε := by
  simp [Linit, lp.single_apply]

theorem Linit_apply_neg_one (h : Hyp d s β k) (ε : ℝ) : Linit h ε (-1) = Lbc h ε := by
  simp [Linit, lp.single_apply]

theorem Linit_apply_other (h : Hyp d s β k) (ε : ℝ) {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ -1) :
    Linit h ε n = 0 := by
  simp [Linit, lp.single_apply, h1, h2]

theorem Linit_even (h : Hyp d s β k) (ε : ℝ) : EvenSeq (Linit h ε) := by
  intro n
  by_cases h1 : n = 1
  · subst h1; rw [Linit_apply_neg_one, Linit_apply_one]
  by_cases h2 : n = -1
  · subst h2; rw [neg_neg, Linit_apply_neg_one, Linit_apply_one]
  rw [Linit_apply_other h ε h1 h2, Linit_apply_other h ε (by omega) (by omega)]

theorem norm_Lbc_le (h : Hyp d s β k) (ε : ℝ) : ‖Lbc h ε‖ ≤ wt 1 * |ε| := by
  have h1 := norm_expDec_le (transientRate d s β k / 4) (lam_div_four_nonneg h)
  have h2 : |ε| / Real.sqrt 2 ≤ |ε| := by
    apply div_le_self (abs_nonneg _)
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h3 := wt_pos 1
  have h4 : ‖wt 1 * (ε / Real.sqrt 2)‖ ≤ wt 1 * |ε| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos h3, abs_div, abs_of_pos
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    exact mul_le_mul_of_nonneg_left h2 h3.le
  unfold Lbc
  calc ‖(wt 1 * (ε / Real.sqrt 2)) • expDec (transientRate d s β k / 4) (lam_div_four_nonneg h)‖
      ≤ ‖wt 1 * (ε / Real.sqrt 2)‖ * ‖expDec (transientRate d s β k / 4) (lam_div_four_nonneg h)‖ :=
        (norm_smul _ _).le
    _ ≤ (wt 1 * |ε|) * 1 := mul_le_mul h4 h1 (norm_nonneg _) (by positivity)
    _ = wt 1 * |ε| := mul_one _

theorem norm_Linit_le (h : Hyp d s β k) (ε : ℝ) : ‖Linit h ε‖ ≤ 2 * wt 1 * |ε| := by
  have hb := norm_Lbc_le h ε
  have e1 : ‖(lp.single 1 (1 : ℤ) (Lbc h ε) : E1)‖ = ‖Lbc h ε‖ := lp.norm_single zero_lt_one _ _
  have e2 : ‖(lp.single 1 (-1 : ℤ) (Lbc h ε) : E1)‖ = ‖Lbc h ε‖ := lp.norm_single zero_lt_one _ _
  calc ‖Linit h ε‖ ≤ ‖(lp.single 1 (1 : ℤ) (Lbc h ε) : E1)‖ + ‖(lp.single 1 (-1 : ℤ) (Lbc h ε) : E1)‖ :=
        norm_add_le _ _
    _ ≤ 2 * wt 1 * |ε| := by rw [e1, e2]; linarith

/-- Coordinate evaluation is continuous on `ℓ¹(ℤ; C_b)`. -/
theorem continuous_lp_apply (n : ℤ) : Continuous fun x : E1 => x n := by
  have : LipschitzWith 1 fun x : E1 => x n := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have := lp.norm_apply_le_norm (by simp : (1 : ℝ≥0∞) ≠ 0) (x - y) n
    simpa using this
  exact this.continuous

theorem isClosed_even : IsClosed {x : E1 | EvenSeq x} := by
  have : {x : E1 | EvenSeq x} = ⋂ n : ℤ, {x : E1 | x (-n) = x n} := by
    ext x; simp [EvenSeq]
  rw [this]
  exact isClosed_iInter fun n => isClosed_eq (continuous_lp_apply (-n)) (continuous_lp_apply n)

/-- Existence of the fixed point `x = L + Q(x,x)` for small `ε`. -/
theorem exists_fixed_point (h : Hyp d s β k) (ε : ℝ)
    (hε : |ε| ≤ 1 / (16 * Kc d s β k * wt 1 + 1)) :
    ∃ x : E1, EvenSeq x ∧ ‖x‖ ≤ 4 * wt 1 * |ε| ∧ x = Linit h ε + Qlp h x x := by
  have hK := Kc_nonneg h
  have hw := wt_pos 1
  refine exists_fixed_point_bilinear {x : E1 | EvenSeq x} isClosed_even (Qlp h) (Kc d s β k) hK
    (norm_Qlp_le h) (Qlp_sub_left h) (Qlp_sub_right h) (Linit h ε) (4 * wt 1 * |ε|)
    (by positivity) ?_ (Linit_even h ε) ?_ ?_
  · have := norm_Linit_le h ε; linarith
  · have hpos : 0 < 16 * Kc d s β k * wt 1 + 1 := by positivity
    have : |ε| * (16 * Kc d s β k * wt 1 + 1) ≤ 1 := by
      rwa [le_div_iff₀ hpos] at hε
    nlinarith [abs_nonneg ε, mul_nonneg hK hw.le, mul_nonneg (mul_nonneg hK hw.le) (abs_nonneg ε)]
  · intro x hx n
    have : (Linit h ε + Qlp h x x) (-n) = (Linit h ε + Qlp h x x) n := by
      simp only [lp.coeFn_add, Pi.add_apply]
      rw [Linit_even h ε n, Qlp_even h hx hx n]
    exact this


/-! ### From the fixed point to the mild solution -/

/-- The nonlinear term of the reduced system in real variables:
`Fnl(g,h)_n = -q² n ∑_m m ĝ(mk) g_{n-m} h_m`. -/
def Fnl (d : ℕ) (s : ℝ) (k : Lattice d) (g h : ℤ → ℝ) (n : ℤ) : ℝ :=
  -(qk k ^ 2) * (n : ℝ) * ∑' m : ℤ, (m : ℝ) * rieszCoeff d s (m • k) * g (n - m) * h m

/-- Recover the coefficients `f_n(t) = x_n(t) / (w(n) e^{ωt})` from the fixed point. -/
def fOf (d : ℕ) (s β : ℝ) (k : Lattice d) (x : E1) (n : ℤ) (t : ℝ) : ℝ :=
  x n t / (wt n * Real.exp (omg d s β k * t))

theorem x_eq_fOf (x : E1) (n : ℤ) (t : ℝ) :
    x n t = wt n * Real.exp (omg d s β k * t) * fOf d s β k x n t := by
  unfold fOf
  have := wt_pos n
  have := Real.exp_pos (omg d s β k * t)
  field_simp

theorem fOf_continuous (x : E1) (n : ℤ) : Continuous (fOf d s β k x n) := by
  unfold fOf
  refine (x n).continuous.div (continuous_const.mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))) fun t => ?_
  have := wt_pos n
  have := Real.exp_pos (omg d s β k * t)
  positivity

theorem fOf_even {x : E1} (hx : EvenSeq x) (n : ℤ) (t : ℝ) :
    fOf d s β k x (-n) t = fOf d s β k x n t := by
  unfold fOf
  rw [hx n, wt_neg]

theorem Pseq_apply (h : Hyp d s β k) (x : E1) (n : ℤ) (σ : ℝ) :
    Pseq s k x x n σ = Real.exp (omg d s β k * σ) ^ 2 *
      Fnl d s k (fun j => fOf d s β k x j σ) (fun j => fOf d s β k x j σ) n := by
  have hsum := (summable_P_terms h (lp1_summable x) (lp1_summable x) n).of_norm
  unfold Pseq Fnl
  have e1 : (∑' m : ℤ, kc s k n m • (x (n - m) * x m)) σ =
      ∑' m : ℤ, (kc s k n m • (x (n - m) * x m)) σ := by
    have := (BoundedContinuousFunction.evalCLM ℝ σ).map_tsum hsum
    simpa using this
  rw [e1, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
    Pi.mul_apply, smul_eq_mul]
  rw [x_eq_fOf (s := s) (β := β) (k := k) x (n - m) σ, x_eq_fOf (s := s) (β := β) (k := k) x m σ]
  unfold kc
  have h1 := wt_pos (n - m)
  have h2 := wt_pos m
  field_simp


theorem Linit_div (h : Hyp d s β k) (ε : ℝ) (n : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    Linit h ε n t / (wt n * Real.exp (omg d s β k * t)) =
      f0 ε n * Real.exp (-(lam d s β k n * t)) := by
  by_cases h1 : n = 1 ∨ n = -1
  · have hwt : wt n = wt 1 := by rcases h1 with rfl | rfl <;> simp [wt]
    have hlam : lam d s β k n = transientRate d s β k := by
      rcases h1 with rfl | rfl
      · exact lam_one
      · rw [lam_neg, lam_one]
    have hL : Linit h ε n = Lbc h ε := by
      rcases h1 with rfl | rfl
      · exact Linit_apply_one h ε
      · exact Linit_apply_neg_one h ε
    rw [hL, hwt, hlam]
    unfold Lbc f0
    simp only [h1, ↓reduceIte, BoundedContinuousFunction.coe_smul, smul_eq_mul, expDec_apply,
      max_eq_left ht]
    have h2 := wt_pos 1
    have h3 : Real.exp (-(transientRate d s β k / 4 * t)) =
        Real.exp (-(transientRate d s β k * t)) * Real.exp (omg d s β k * t) := by
      rw [← Real.exp_add]; congr 1; unfold omg; ring
    rw [h3]
    have h4 := Real.exp_pos (omg d s β k * t)
    field_simp
  · push Not at h1
    rw [Linit_apply_other h ε h1.1 h1.2]
    simp [f0, h1.1, h1.2]

theorem fOf_zero {x : E1} (h : Hyp d s β k) {ε : ℝ} (hx : x = Linit h ε + Qlp h x x) (t : ℝ) :
    fOf d s β k x 0 t = 0 := by
  have h0 : x 0 = 0 := by
    have := congrArg (fun z : E1 => z 0) hx
    simp only [lp.coeFn_add, Pi.add_apply, Qlp_apply, Qseq, Pseq_zero, map_zero, smul_zero,
      add_zero] at this
    rw [this]
    exact Linit_apply_other h ε (by norm_num) (by norm_num)
  unfold fOf
  rw [h0]
  simp


theorem fOf_mild (h : Hyp d s β k) {x : E1} {ε : ℝ} (hx : x = Linit h ε + Qlp h x x) (n : ℤ)
    {t : ℝ} (ht : 0 ≤ t) :
    fOf d s β k x n t = f0 ε n * Real.exp (-(lam d s β k n * t)) +
      ∫ σ in (0 : ℝ)..t, Real.exp (-(lam d s β k n * (t - σ))) *
        Fnl d s k (fun j => fOf d s β k x j σ) (fun j => fOf d s β k x j σ) n := by
  by_cases hn : n = 0
  · subst hn
    rw [fOf_zero h hx]
    simp [f0, Fnl]
  have hc := lam_sub_omg_pos h hn
  have hω := omg_nonneg h
  set c := lam d s β k n - omg d s β k with hcdef
  have hcoord : x n t = Linit h ε n t + wt n * duhF c (omg d s β k) (Pseq s k x x n) t := by
    have := congrArg (fun z : E1 => z n t) hx
    simp only [lp.coeFn_add, Pi.add_apply, BoundedContinuousFunction.coe_add, Qlp_apply, Qseq,
      BoundedContinuousFunction.coe_smul, smul_eq_mul] at this
    rw [duhLg_apply hc hω] at this
    exact this
  have hE := Real.exp_pos (omg d s β k * t)
  have hw := wt_pos n
  have hduh : duhF c (omg d s β k) (Pseq s k x x n) t =
      Real.exp (-(c * t)) * ∫ σ in (0 : ℝ)..t, Real.exp (lam d s β k n * σ) *
        Fnl d s k (fun j => fOf d s β k x j σ) (fun j => fOf d s β k x j σ) n := by
    unfold duhF
    rw [max_eq_left ht]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [Pseq_apply h x n σ]
    have e : Real.exp ((c - omg d s β k) * σ) * Real.exp (omg d s β k * σ) ^ 2 =
        Real.exp (lam d s β k n * σ) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; simp only [hcdef]; ring
    rw [← mul_assoc, e]
  have hf : fOf d s β k x n t = x n t / (wt n * Real.exp (omg d s β k * t)) := rfl
  rw [hf, hcoord, hduh, add_div, Linit_div h ε n ht]
  congr 1
  have e2 : Real.exp (-(c * t)) / Real.exp (omg d s β k * t) = Real.exp (-(lam d s β k n * t)) := by
    rw [← Real.exp_sub]; congr 1; simp only [hcdef]; ring
  have e3 : ∫ σ in (0 : ℝ)..t, Real.exp (-(lam d s β k n * (t - σ))) *
        Fnl d s k (fun j => fOf d s β k x j σ) (fun j => fOf d s β k x j σ) n =
      Real.exp (-(lam d s β k n * t)) * ∫ σ in (0 : ℝ)..t, Real.exp (lam d s β k n * σ) *
        Fnl d s k (fun j => fOf d s β k x j σ) (fun j => fOf d s β k x j σ) n := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    show _ = Real.exp (-(lam d s β k n * t)) * (Real.exp (lam d s β k n * σ) * _)
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  rw [e3, ← e2]
  field_simp


/-- A mild solution of the reduced system with data `ε`: coefficients `f_n(t)`, `n ∈ ℤ`, of the
perturbation `ρ - 1` along the line `ℤ k`, with the exponential-weighted `ℓ¹` bound
`∑_n sup_t w(n) e^{ωt} |f_n(t)| ≤ 4 w(1) |ε|` (`ω = 3λ/4`). -/
structure MildSol (d : ℕ) (s β : ℝ) (k : Lattice d) (ε : ℝ) (f : ℤ → ℝ → ℝ) : Prop where
  cont : ∀ n, Continuous (f n)
  contF : ∀ n, Continuous fun σ => Fnl d s k (fun j => f j σ) (fun j => f j σ) n
  even : ∀ n t, f (-n) t = f n t
  bound : ∃ S : ℤ → ℝ, Summable S ∧ ∑' n, S n ≤ 4 * wt 1 * |ε| ∧
    ∀ n t, 0 ≤ t → wt n * Real.exp (omg d s β k * t) * |f n t| ≤ S n
  mild : ∀ n t, 0 ≤ t → f n t = f0 ε n * Real.exp (-(lam d s β k n * t)) +
    ∫ σ in (0 : ℝ)..t, Real.exp (-(lam d s β k n * (t - σ))) *
      Fnl d s k (fun j => f j σ) (fun j => f j σ) n

/-- **Global existence** (small data): for `|ε| ≤ ε₀` the reduced system has a global mild
solution in the weighted `ℓ¹(ℤ; C_b)` space, with `f_0 = 0`. -/
theorem exists_mildSol (h : Hyp d s β k) (ε : ℝ) (hε : |ε| ≤ 1 / (16 * Kc d s β k * wt 1 + 1)) :
    ∃ f : ℤ → ℝ → ℝ, MildSol d s β k ε f ∧ ∀ t, f 0 t = 0 := by
  obtain ⟨x, hxe, hxn, hx⟩ := exists_fixed_point h ε hε
  refine ⟨fOf d s β k x, ⟨fOf_continuous x, ?_, fun n t => fOf_even hxe n t, ?_, ?_⟩,
    fOf_zero h hx⟩
  · intro n
    have hE : ∀ σ, Real.exp (omg d s β k * σ) ^ 2 ≠ 0 := fun σ => by positivity
    have : (fun σ => Fnl d s k (fun j => fOf d s β k x j σ) (fun j => fOf d s β k x j σ) n) =
        fun σ => Pseq s k x x n σ / Real.exp (omg d s β k * σ) ^ 2 := by
      funext σ; rw [Pseq_apply h x n σ]; field_simp [hE σ]
    rw [this]
    exact (Pseq s k x x n).continuous.div (by fun_prop) hE
  · refine ⟨fun n => ‖x n‖, lp1_summable x, ?_, fun n t ht => ?_⟩
    · rw [← lp1_norm x]; exact hxn
    · rw [← abs_of_pos (mul_pos (wt_pos n) (Real.exp_pos (omg d s β k * t))), ← abs_mul,
        ← x_eq_fOf]
      exact x.1 n |>.norm_coe_le_norm t
  · intro n t ht
    exact fOf_mild h hx n ht


/-! ### The initial coefficients -/

theorem integrable_cont_torus {g : Torus d → ℂ} (hg : Continuous g) : Integrable g :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem coeffOf_data (k : Lattice d) (ε : ℝ) (j : Lattice d) :
    coeffOf (fun x => 1 + ε * cosTest k x) j =
      (if j = 0 then 1 else 0) + ((ε / Real.sqrt 2 : ℝ) : ℂ) *
        ((if j = k then 1 else 0) + (if j = -k then 1 else 0)) := by
  have hc : ∀ a b : Lattice d, Continuous fun x : Torus d => Torus.mode a x * Torus.mode b x :=
    fun a b => (Torus.continuous_mode a).mul (Torus.continuous_mode b)
  have hint : ∀ a b : Lattice d, Integrable fun x : Torus d => Torus.mode a x * Torus.mode b x :=
    fun a b => integrable_cont_torus (hc a b)
  have h1 : ∫ x : Torus d, Torus.mode (-j) x * 1 = if j = 0 then 1 else 0 := by
    have := Torus.integral_mode_mul (-j) (0 : Lattice d)
    simp only [Torus.mode_zero, mul_one] at this ⊢
    rw [this]
    simp
  have h2 : ∫ x : Torus d, Torus.mode (-j) x * Torus.mode k x = if j = k then 1 else 0 := by
    rw [Torus.integral_mode_mul]
    have : (-j + k = 0) ↔ (j = k) := by rw [neg_add_eq_zero, eq_comm]
    simp only [this]
  have h3 : ∫ x : Torus d, Torus.mode (-j) x * Torus.mode (-k) x = if j = -k then 1 else 0 := by
    rw [Torus.integral_mode_mul]
    have : (-j + -k = 0) ↔ (j = -k) := by
      constructor
      · intro h; have := eq_neg_of_add_eq_zero_right h; simpa using this.symm
      · intro h; rw [h]; simp
    simp only [this]
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs2; simp at hs2
  have key : ∀ x : Torus d, UnitAddTorus.mFourier (-j) x * ((1 + ε * cosTest k x : ℝ) : ℂ) =
      Torus.mode (-j) x * 1 + ((ε / Real.sqrt 2 : ℝ) : ℂ) *
        (Torus.mode (-j) x * Torus.mode k x + Torus.mode (-j) x * Torus.mode (-k) x) := by
    intro x
    have hre : ((Torus.cosMode k x : ℝ) : ℂ) = (Torus.mode k x + Torus.mode (-k) x) / 2 := by
      rw [Torus.mode_neg]; exact Complex.re_eq_add_conj _
    have : ((1 + ε * cosTest k x : ℝ) : ℂ) = 1 + (ε : ℂ) * (Real.sqrt 2 : ℂ) *
        ((Torus.mode k x + Torus.mode (-k) x) / 2) := by
      unfold cosTest
      push_cast
      rw [hre]
      ring
    rw [this]
    show Torus.mode (-j) x * _ = _
    push_cast
    field_simp
    linear_combination (ε : ℂ) * Torus.mode (-j) x * (Torus.mode k x + Torus.mode (-k) x) * hs2
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  simp_rw [key]
  rw [integral_add, integral_const_mul, integral_add, h1, h2, h3]
  · exact hint _ _
  · exact hint _ _
  · exact integrable_cont_torus ((Torus.continuous_mode _).mul continuous_const)
  · exact (((hint _ _).add (hint _ _))).const_mul _


theorem coeffOf_data_line (hk : k ≠ 0) (ε : ℝ) :
    coeffOf (fun x => 1 + ε * cosTest k x) =
      lineCoeff k (deltaSeq + fun n => ((f0 ε n : ℝ) : ℂ)) := by
  funext j
  rw [coeffOf_data]
  by_cases hj : ∃ n : ℤ, j = n • k
  · obtain ⟨n, rfl⟩ := hj
    rw [lineCoeff_smul hk]
    have inj := smul_injective_of_ne_zero hk
    have e0 : (n • k = 0) ↔ n = 0 := by
      constructor
      · intro h; exact inj (h.trans (zero_smul ℤ k).symm)
      · intro h; rw [h, zero_smul]
    have e1 : (n • k = k) ↔ n = 1 := by
      constructor
      · intro h; exact inj (h.trans (one_smul ℤ k).symm)
      · intro h; rw [h, one_smul]
    have e2 : (n • k = -k) ↔ n = -1 := by
      constructor
      · intro h; exact inj (h.trans (by show -k = (-1 : ℤ) • k; rw [neg_smul, one_smul]))
      · intro h; rw [h, neg_smul, one_smul]
    simp only [e0, e1, e2, Pi.add_apply, deltaSeq, f0]
    by_cases h0 : n = 0
    · subst h0; simp
    by_cases h1 : n = 1
    · subst h1; simp
    by_cases h2 : n = -1
    · subst h2; simp
    simp [h0, h1, h2]
  · push Not at hj
    rw [lineCoeff_of_not_mem _ j hj]
    have h0 : j ≠ 0 := by simpa using hj 0
    have h1 : j ≠ k := by simpa using hj 1
    have h2 : j ≠ -k := by simpa using hj (-1)
    simp [h0, h1, h2]


/-! ### The integrated equation, mode by mode -/

/-- A scalar mild solution `f(t) = f₀e^{-λt} + ∫_0^t e^{-λ(t-σ)}F(σ)dσ` with continuous forcing
satisfies the integrated equation `f(t) = f₀ + ∫_0^t (-λ f + F)`. -/
theorem integrated_of_mild {F fn : ℝ → ℝ} (hF : Continuous F) (lam f₀ : ℝ)
    (hmild : ∀ t : ℝ, 0 ≤ t → fn t = f₀ * Real.exp (-(lam * t)) +
      ∫ σ in (0 : ℝ)..t, Real.exp (-(lam * (t - σ))) * F σ) {t : ℝ} (ht : 0 ≤ t) :
    fn t = f₀ + ∫ σ in (0 : ℝ)..t, (-lam * fn σ + F σ) := by
  set G : ℝ → ℝ := fun u => ∫ σ in (0 : ℝ)..u, Real.exp (lam * σ) * F σ with hG
  set g : ℝ → ℝ := fun u => Real.exp (-(lam * u)) * (f₀ + G u) with hg
  have hcont : Continuous fun σ => Real.exp (lam * σ) * F σ :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF
  have hgfn : ∀ u : ℝ, 0 ≤ u → fn u = g u := by
    intro u hu
    rw [hmild u hu]
    have : ∫ σ in (0 : ℝ)..u, Real.exp (-(lam * (u - σ))) * F σ =
        Real.exp (-(lam * u)) * G u := by
      rw [hG, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      show _ = Real.exp (-(lam * u)) * (Real.exp (lam * σ) * F σ)
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [this, hg]
    ring
  have hderiv : ∀ u : ℝ, HasDerivAt g (-lam * g u + F u) u := by
    intro u
    have hG' : HasDerivAt G (Real.exp (lam * u) * F u) u :=
      (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(lam * u)))
        (Real.exp (-(lam * u)) * (-lam)) u := by
      have := ((hasDerivAt_id u).const_mul lam).neg.exp
      simpa using this
    have := h1.mul ((hasDerivAt_const u f₀).add hG')
    convert this using 1
    simp only [hg]
    have : Real.exp (-(lam * u)) * Real.exp (lam * u) = 1 := by
      rw [← Real.exp_add]; simp
    calc -lam * (Real.exp (-(lam * u)) * (f₀ + G u)) + F u
        = Real.exp (-(lam * u)) * (-lam) * (f₀ + G u) + (Real.exp (-(lam * u)) * Real.exp (lam * u)) * F u := by
          rw [this]; ring
      _ = _ := by simp; ring
  have hint : ∫ σ in (0 : ℝ)..t, (-lam * g σ + F σ) = g t - g 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) ?_
    exact (((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg |>.mul
      (continuous_const.add (by
        exact intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0)))).add hF)).intervalIntegrable _ _
  have hcongr : ∫ σ in (0 : ℝ)..t, (-lam * fn σ + F σ) = ∫ σ in (0 : ℝ)..t, (-lam * g σ + F σ) := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    have : 0 ≤ σ := by rw [Set.uIcc_of_le ht] at hσ; exact hσ.1
    simp only [hgfn σ this]
  rw [hcongr, hint, hgfn t ht]
  have : g 0 = f₀ := by simp [hg, hG]
  rw [this]; ring


/-- The coefficient path of the transient: `ρ̂(t) = δ_0 + f(t)` on the line `ℤ k`, zero elsewhere. -/
def rhoC (k : Lattice d) (f : ℤ → ℝ → ℝ) (t : ℝ) : Coeff d :=
  lineCoeff k (deltaSeq + fun n => ((f n t : ℝ) : ℂ))

theorem MildSol.moment1 (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    {t : ℝ} (ht : 0 ≤ t) : Moment1 (fun n => ((f n t : ℝ) : ℂ)) := by
  obtain ⟨S, hS, -, hb⟩ := hf.bound
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hS
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ Real.exp (omg d s β k * t) :=
    Real.one_le_exp (mul_nonneg (omg_nonneg h) ht)
  calc (1 + |(m : ℝ)|) * |f m t| ≤ wt m * Real.exp (omg d s β k * t) * |f m t| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have := one_add_le_wt m
        nlinarith [wt_pos m]
    _ ≤ S m := hb m t ht

theorem Bform_ofReal (g g' : ℤ → ℝ) (n : ℤ) :
    Bform d s k (fun j => (g j : ℂ)) (fun j => (g' j : ℂ)) n = ((Fnl d s k g g' n : ℝ) : ℂ) := by
  unfold Bform Fnl
  push_cast
  rfl

theorem rhs_rhoC (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f) {t : ℝ}
    (ht : 0 ≤ t) (n : ℤ) :
    mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f t) (n • k) =
      ((-(lam d s β k n) * f n t + Fnl d s k (fun j => f j t) (fun j => f j t) n : ℝ) : ℂ) := by
  unfold rhoC
  rw [mfRhsCoeff_lineCoeff h.hk, reducedRhs_delta_add h (hf.moment1 h ht) n,
    Bform_ofReal (fun j => f j t) (fun j => f j t) n]
  push_cast
  ring

theorem MildSol.integrated (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f)
    (j : Lattice d) {t : ℝ} (ht : 0 ≤ t) :
    rhoC k f t j = coeffOf (fun x => 1 + ε * cosTest k x) j +
        ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) j ∧
      IntegrableOn (fun σ => mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) j) (Set.Icc 0 t) := by
  rw [coeffOf_data_line h.hk]
  by_cases hj : ∃ n : ℤ, j = n • k
  · obtain ⟨n, rfl⟩ := hj
    set φ : ℝ → ℝ := fun σ => -(lam d s β k n) * f n σ +
      Fnl d s k (fun j => f j σ) (fun j => f j σ) n with hφ
    have hφc : Continuous φ :=
      (continuous_const.mul (hf.cont n)).add (hf.contF n)
    have hcongr : ∀ σ ∈ Set.Icc (0 : ℝ) t,
        mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) (n • k) = (φ σ : ℂ) := fun σ hσ =>
      rhs_rhoC h hf hσ.1 n
    constructor
    · have hint : ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) (n • k) =
          ((∫ σ in (0 : ℝ)..t, φ σ : ℝ) : ℂ) := by
        rw [intervalIntegral.integral_ofReal.symm]
        refine intervalIntegral.integral_congr fun σ hσ => ?_
        rw [Set.uIcc_of_le ht] at hσ
        exact hcongr σ hσ
      have hm := integrated_of_mild (fn := f n) (hf.contF n) (lam d s β k n) (f0 ε n)
        (hf.mild n) ht
      have hm' : ((f n t : ℝ) : ℂ) = ((f0 ε n : ℝ) : ℂ) + ((∫ σ in (0 : ℝ)..t, φ σ : ℝ) : ℂ) := by
        exact_mod_cast hm
      rw [hint]
      unfold rhoC
      rw [lineCoeff_smul h.hk, lineCoeff_smul h.hk]
      simp only [Pi.add_apply]
      rw [hm']
      ring
    · refine IntegrableOn.congr_fun (f := fun σ => (φ σ : ℂ)) ?_ (fun σ hσ => (hcongr σ hσ).symm)
        measurableSet_Icc
      exact (Complex.continuous_ofReal.comp hφc).integrableOn_Icc
  · push Not at hj
    have h0 : ∀ σ, mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) j = 0 := fun σ =>
      mfRhsCoeff_lineCoeff_off _ j hj
    simp only [h0, intervalIntegral.integral_zero, add_zero]
    refine ⟨?_, integrableOn_zero⟩
    unfold rhoC
    rw [lineCoeff_of_not_mem _ j hj, lineCoeff_of_not_mem _ j hj]


/-! ### Structure of the coefficient path -/

theorem supportedOnLine_rhoC (k : Lattice d) (f : ℤ → ℝ → ℝ) (t : ℝ) :
    SupportedOnLine k (rhoC k f t) := supportedOnLine_lineCoeff k _

theorem rhoC_smul (hk : k ≠ 0) (f : ℤ → ℝ → ℝ) (t : ℝ) (n : ℤ) :
    rhoC k f t (n • k) = deltaSeq n + ((f n t : ℝ) : ℂ) := by
  unfold rhoC
  rw [lineCoeff_smul hk]
  rfl

/-- Evenness `ρ̂(t, nk) = ρ̂(t, -nk)`. -/
theorem rhoC_even (hk : k ≠ 0) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f) (t : ℝ)
    (n : ℤ) : rhoC k f t (n • k) = rhoC k f t (-(n • k)) := by
  rw [← neg_smul, rhoC_smul hk, rhoC_smul hk, hf.even]
  simp [deltaSeq]

/-- The coefficient path is that of a real function. -/
theorem rhoC_isReal (hk : k ≠ 0) {ε : ℝ} {f : ℤ → ℝ → ℝ} (hf : MildSol d s β k ε f) (t : ℝ) :
    IsRealCoeff (rhoC k f t) := by
  intro j
  by_cases hj : ∃ n : ℤ, j = n • k
  · obtain ⟨n, rfl⟩ := hj
    rw [← rhoC_even hk hf t n, rhoC_smul hk]
    simp [deltaSeq]
  · push Not at hj
    have hj' : ∀ n : ℤ, -j ≠ n • k := fun n h => hj (-n) (by
      rw [neg_smul, ← h]; simp)
    unfold rhoC
    rw [lineCoeff_of_not_mem _ j hj, lineCoeff_of_not_mem _ (-j) hj']
    simp

theorem summable_norm_lineCoeff (hk : k ≠ 0) {a : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Summable fun j => ‖lineCoeff k a j‖ := by
  rw [← (smul_injective_of_ne_zero hk).summable_iff (f := fun j => ‖lineCoeff k a j‖)]
  · have : (fun j => ‖lineCoeff k a j‖) ∘ (fun n : ℤ => n • k) = fun n => ‖a n‖ := by
      funext n; simp only [Function.comp, lineCoeff_smul hk]
    rw [this]; exact ha
  · intro j hj
    rw [lineCoeff_of_not_mem _ j (fun n hn => hj ⟨n, hn.symm⟩)]
    simp

theorem MildSol.summable_rhoC (h : Hyp d s β k) {ε : ℝ} {f : ℤ → ℝ → ℝ}
    (hf : MildSol d s β k ε f) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun j => ‖rhoC k f t j‖ := by
  refine summable_norm_lineCoeff h.hk ?_
  have h1 := hf.moment1 h ht
  have h2 : Summable fun n : ℤ => ‖deltaSeq n‖ := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := by simpa using hn
    simp [deltaSeq, this]
  refine (h2.add (h1.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => norm_add_le _ _)
  have : (1 : ℝ) ≤ 1 + |(n : ℝ)| := by linarith [abs_nonneg (n : ℝ)]
  nlinarith [norm_nonneg (((f n t : ℝ)) : ℂ)]

/-- The weighted norm of `P(x,x)_n` (the forcing, before the Duhamel integral). -/
theorem wt_norm_Pseq_le (h : Hyp d s β k) (x : E1) {n : ℤ} (hn : n ≠ 0) :
    wt n * ‖Pseq s k x x n‖ ≤ 2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2 *
      ∑' m, ‖x (n - m)‖ * ‖x m‖ := by
  have hsum := summable_conv_norm (lp1_summable x) (lp1_summable x) n
  have h2 := norm_Pseq_le h (lp1_summable x) (lp1_summable x) n
  calc wt n * ‖Pseq s k x x n‖
      ≤ wt n * ∑' m, |kc s k n m| * (‖x (n - m)‖ * ‖x m‖) :=
        mul_le_mul_of_nonneg_left h2 (wt_pos n).le
    _ = ∑' m, wt n * |kc s k n m| * (‖x (n - m)‖ * ‖x m‖) := by
        rw [← tsum_mul_left]; exact tsum_congr fun m => by ring
    _ ≤ ∑' m, (2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2) * (‖x (n - m)‖ * ‖x m‖) := by
        refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hsum.mul_left _)
        · exact mul_le_mul_of_nonneg_right (wt_abs_kc_le h hn m) (by positivity)
        · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hsum.mul_left
            (2 * qk k ^ 2 * rieszCoeff d s k * (n : ℝ) ^ 2))
          · exact mul_nonneg (mul_nonneg (wt_pos n).le (abs_nonneg _)) (by positivity)
          · exact mul_le_mul_of_nonneg_right (wt_abs_kc_le h hn m) (by positivity)
    _ = _ := tsum_mul_left

/-- **Fourier-side global existence** (the content of P10a): for `|ε| ≤ ε₀` there is a mild
solution, and its coefficient path `ρ̂(t) = rhoC k f t` is supported on the line `ℤ k`, even,
real, satisfies `ρ̂(0) = coeffOf (1 + ε ψ_k)` and the integrated equation of `IsMFSolutionHK.eq`
for every mode. -/
theorem exists_transient_coeff (h : Hyp d s β k) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| ≤ ε₀ → ∃ f : ℤ → ℝ → ℝ,
      MildSol d s β k ε f ∧
      rhoC k f 0 = coeffOf (fun x => 1 + ε * cosTest k x) ∧
      (∀ j : Lattice d, ∀ t : ℝ, 0 ≤ t →
        rhoC k f t j = coeffOf (fun x => 1 + ε * cosTest k x) j +
          ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) j) ∧
      (∀ j : Lattice d, ∀ t : ℝ, 0 ≤ t →
        IntegrableOn (fun σ => mfRhsCoeff d s (fun _ => 0) β⁻¹ (rhoC k f σ) j) (Set.Icc 0 t)) ∧
      (∀ t : ℝ, SupportedOnLine k (rhoC k f t)) ∧
      (∀ t : ℝ, ∀ n : ℤ, rhoC k f t (n • k) = rhoC k f t (-(n • k))) ∧
      (∀ t : ℝ, IsRealCoeff (rhoC k f t)) := by
  have hK := Kc_nonneg h
  have hw := wt_pos 1
  refine ⟨1 / (16 * Kc d s β k * wt 1 + 1), by positivity, fun ε hε => ?_⟩
  obtain ⟨f, hf, -⟩ := exists_mildSol h ε hε
  refine ⟨f, hf, ?_, fun j t ht => (hf.integrated h j ht).1, fun j t ht => (hf.integrated h j ht).2,
    supportedOnLine_rhoC k f, fun t n => rhoC_even h.hk hf t n, rhoC_isReal h.hk hf⟩
  funext j
  have := (hf.integrated h j (le_refl 0)).1
  simpa using this

end HRS.PDE.MFTransient

