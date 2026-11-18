import HRS.PDE.EnergyTransport

/-!
# Bounds for the symbols `2πi k_i ĝ(k)` and `(2πi)² k_i k_j ĝ(k)` of the nonlocal term
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- `rad k = 2π|k|`. -/
def rad (k : Lattice d) : ℝ := 2 * Real.pi * Lattice.enorm k

theorem rad_nonneg (k : Lattice d) : 0 ≤ rad k :=
  mul_nonneg (by positivity) (norm_nonneg _)

theorem rad_sq (k : Lattice d) : rad k ^ 2 = 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  unfold rad; ring

theorem abs_two_pi_le_rad (k : Lattice d) (i : Fin d) : |2 * Real.pi * (k i : ℝ)| ≤ rad k := by
  have h : (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ rad k ^ 2 := by
    rw [rad_sq, four_pi_enorm_sq]
    exact Finset.single_le_sum (f := fun i => (2 * Real.pi * (k i : ℝ)) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : |2 * Real.pi * (k i : ℝ)| ^ 2 ≤ rad k ^ 2 := by rwa [sq_abs]
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (rad_nonneg k) two_ne_zero).mp h2

theorem one_le_rad (k : Lattice d) (hk : k ≠ 0) : 1 ≤ rad k := by
  have := one_le_enorm k hk
  unfold rad
  nlinarith [Real.pi_gt_three]

theorem rad_sq_le (k : Lattice d) : rad k ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  rw [rad_sq]; linarith

theorem abs_rieszCoeff_le (s : ℝ) (k : Lattice d) (hk : k ≠ 0) :
    |rieszCoeff d s k| ≤ |rieszConst d s| * rad k ^ (s - (d : ℝ)) := by
  unfold rieszCoeff
  simp only [hk, ite_false]
  have e : (2 * Real.pi * Lattice.enorm k) = rad k := rfl
  rw [e, abs_mul, abs_of_nonneg (Real.rpow_nonneg (rad_nonneg k) _)]

theorem norm_symS_le (s : ℝ) (i : Fin d) (k : Lattice d) (hk : k ≠ 0) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)‖ ≤
      |rieszConst d s| * rad k ^ (s - (d : ℝ) + 1) := by
  have hr : 0 < rad k := lt_of_lt_of_le one_pos (one_le_rad k hk)
  rw [norm_mul, norm_symbol_factor, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_add_one hr.ne']
  calc |2 * Real.pi * (k i : ℝ)| * |rieszCoeff d s k|
      ≤ rad k * (|rieszConst d s| * rad k ^ (s - (d : ℝ))) :=
        mul_le_mul (abs_two_pi_le_rad k i) (abs_rieszCoeff_le s k hk) (abs_nonneg _) hr.le
    _ = _ := by ring

theorem norm_symT_le (s : ℝ) (i j : Fin d) (k : Lattice d) (hk : k ≠ 0) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * (2 * Real.pi * Complex.I * (k j : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)‖ ≤
      |rieszConst d s| * rad k ^ (s - (d : ℝ) + 2) := by
  have hr : 0 < rad k := lt_of_lt_of_le one_pos (one_le_rad k hk)
  rw [norm_mul, norm_mul, norm_symbol_factor, norm_symbol_factor, Complex.norm_real,
    Real.norm_eq_abs, Real.rpow_add hr, Real.rpow_two]
  calc |2 * Real.pi * (k i : ℝ)| * |2 * Real.pi * (k j : ℝ)| * |rieszCoeff d s k|
      ≤ rad k * rad k * (|rieszConst d s| * rad k ^ (s - (d : ℝ))) :=
        mul_le_mul (mul_le_mul (abs_two_pi_le_rad k i) (abs_two_pi_le_rad k j) (abs_nonneg _)
          hr.le) (abs_rieszCoeff_le s k hk) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- Regime R1: both symbols are bounded. -/
theorem norm_symS_R1 (s : ℝ) (hs : s ≤ (d : ℝ) - 2) (i : Fin d) (k : Lattice d) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)‖ ≤ |rieszConst d s| := by
  by_cases hk : k = 0
  · subst hk; simp [rieszCoeff]
  · refine (norm_symS_le s i k hk).trans ?_
    have : rad k ^ (s - (d : ℝ) + 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_rad k hk) (by linarith)
    calc _ ≤ |rieszConst d s| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := mul_one _

theorem norm_symT_R1 (s : ℝ) (hs : s ≤ (d : ℝ) - 2) (i j : Fin d) (k : Lattice d) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * (2 * Real.pi * Complex.I * (k j : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)‖ ≤ |rieszConst d s| := by
  by_cases hk : k = 0
  · subst hk; simp [rieszCoeff]
  · refine (norm_symT_le s i j k hk).trans ?_
    have : rad k ^ (s - (d : ℝ) + 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (one_le_rad k hk) (by linarith)
    calc _ ≤ |rieszConst d s| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := mul_one _

theorem rad_rpow_le_sobWeight (k : Lattice d) (e : ℝ) (he : 0 ≤ e) :
    rad k ^ (2 * e) ≤ sobWeight e k := by
  have h1 : rad k ^ (2 * e) = (rad k ^ 2) ^ e := by
    rw [Real.rpow_mul (rad_nonneg k)]; norm_cast
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (rad_sq_le k) he

/-- Regime R3 (`0 < θ < 2`): `|2πi k_i ĝ(k)| ≤ c ⟨k⟩^{θ/2}`, i.e. weight `(1+4π²|k|²)^{θ/4}`. -/
theorem norm_symS_R3 (s : ℝ) (hθ0 : 0 < s + 2 - d) (hθ2 : s + 2 - d < 2) (i : Fin d)
    (k : Lattice d) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)‖ ≤
      |rieszConst d s| * sobWeight ((s + 2 - d) / 4) k := by
  by_cases hk : k = 0
  · subst hk; simp only [rieszCoeff, ite_true, Complex.ofReal_zero, mul_zero, norm_zero]
    exact mul_nonneg (abs_nonneg _) (sobWeight_nonnegE _ _)
  · refine (norm_symS_le s i k hk).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    calc rad k ^ (s - (d : ℝ) + 1) ≤ rad k ^ (2 * ((s + 2 - d) / 4)) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_rad k hk) (by linarith)
      _ ≤ _ := rad_rpow_le_sobWeight k _ (by linarith)

theorem norm_symT_R3 (s : ℝ) (hθ0 : 0 < s + 2 - d) (i j : Fin d) (k : Lattice d) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * (2 * Real.pi * Complex.I * (k j : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)‖ ≤
      |rieszConst d s| * sobWeight ((s + 2 - d) / 2) k := by
  by_cases hk : k = 0
  · subst hk; simp only [rieszCoeff, ite_true, Complex.ofReal_zero, mul_zero, norm_zero]
    exact mul_nonneg (abs_nonneg _) (sobWeight_nonnegE _ _)
  · refine (norm_symT_le s i j k hk).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    calc rad k ^ (s - (d : ℝ) + 2) = rad k ^ (2 * ((s + 2 - d) / 2)) := by
          congr 1; ring
      _ ≤ _ := rad_rpow_le_sobWeight k _ (by linarith)


/-! ### Structural lemmas for convolutions -/

theorem derivCoeff_mulCoeff {n : ℕ} (j : Fin d) (a c : Coeff d) (hc : IsTrigPoly n c)
    (k : Lattice d) :
    derivCoeff j (mulCoeff a c) k =
      mulCoeff (derivCoeff j a) c k + mulCoeff a (derivCoeff j c) k := by
  have hc' : IsTrigPoly n (derivCoeff j c) := by
    rw [derivCoeff_eq_multi]; exact isTrigPoly_multiDerivCoeff hc _
  have e1 : mulCoeff (derivCoeff j a) c k = ∑ l ∈ boxFin d n, derivCoeff j a (k - l) * c l :=
    mulCoeff_of_trig hc _ _
  have e2 : mulCoeff a (derivCoeff j c) k = ∑ l ∈ boxFin d n, a (k - l) * derivCoeff j c l :=
    mulCoeff_of_trig hc' _ _
  have e3 : mulCoeff a c k = ∑ l ∈ boxFin d n, a (k - l) * c l := mulCoeff_of_trig hc _ _
  show 2 * Real.pi * Complex.I * (k j : ℂ) * mulCoeff a c k = _
  rw [e1, e2, e3, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [derivCoeff, Pi.sub_apply]
  push_cast
  ring

theorem sum_sq_le_of_terms {ι κ : Type*} (T : Finset ι) (S : Finset κ) (g : ι → κ → ℂ)
    (K : ι → ℝ) (h : ∀ t ∈ T, ∑ k ∈ S, ‖g t k‖ ^ 2 ≤ K t) :
    ∑ k ∈ S, ‖∑ t ∈ T, g t k‖ ^ 2 ≤ (T.card : ℝ) * ∑ t ∈ T, K t := by
  calc ∑ k ∈ S, ‖∑ t ∈ T, g t k‖ ^ 2
      ≤ ∑ k ∈ S, (T.card : ℝ) * ∑ t ∈ T, ‖g t k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ‖∑ t ∈ T, g t k‖ ^ 2 ≤ (∑ t ∈ T, ‖g t k‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
          _ ≤ _ := sq_sum_le_card_mul_sum_sq
    _ = (T.card : ℝ) * ∑ t ∈ T, ∑ k ∈ S, ‖g t k‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (T.card : ℝ) * ∑ t ∈ T, K t :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (Nat.cast_nonneg _)

/-- `ℓ²` bound for `D_α (a * F)` when all derivatives `D_β a`, `β ≤ α`, are coefficients of
bounded continuous functions. -/
theorem leibniz_l2_bound (m : ℕ) (K : ℝ) (α : Fin d → ℕ) (hα : ∑ i, α i ≤ m) (a : Coeff d)
    (ha : ∀ β ∈ leibnizSet α, ∃ φ : Torus d → ℝ, Continuous φ ∧
      coeffOf φ = multiDerivCoeff β a ∧ ∀ x, |φ x| ≤ K)
    {n : ℕ} (F : Coeff d) (hF : IsTrigPoly n F) (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖multiDerivCoeff α (mulCoeff a F) k‖ ^ 2 ≤
      (((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, (binomW α β : ℝ) ^ 2 * K ^ 2) *
        hsNormSq (m : ℝ) F := by
  classical
  have hMem : MemHs (m : ℝ) F := memHs_of_isTrigPolyE hF _
  simp_rw [multiDerivCoeff_mulCoeff α a F hF]
  refine sum_sq_le_of_terms (leibnizSet α) S _ (fun β => (binomW α β : ℝ) ^ 2 * K ^ 2 *
    hsNormSq (m : ℝ) F) (fun β hβ => ?_) |>.trans_eq (by rw [mul_assoc, Finset.sum_mul])
  obtain ⟨φ, hφc, hφ, hφK⟩ := ha β hβ
  have hβα := mem_leibnizSet.mp hβ
  have hc' : IsTrigPoly n (multiDerivCoeff (α - β) F) := isTrigPoly_multiDerivCoeff hF _
  have h1 := l2_mul_le φ hφc K hφK n _ hc' S
  rw [hφ] at h1
  have h2 : ∑ k ∈ boxFin d n, ‖multiDerivCoeff (α - β) F k‖ ^ 2 ≤ hsNormSq (m : ℝ) F := by
    refine sum_sq_multiDeriv_le (α - β) m ?_ F hMem _
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) hα
    simp
  calc ∑ k ∈ S, ‖(binomW α β : ℂ) * mulCoeff (multiDerivCoeff β a) (multiDerivCoeff (α - β) F) k‖ ^ 2
      = (binomW α β : ℝ) ^ 2 *
        ∑ k ∈ S, ‖mulCoeff (multiDerivCoeff β a) (multiDerivCoeff (α - β) F) k‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, Complex.norm_natCast, mul_pow]
    _ ≤ (binomW α β : ℝ) ^ 2 * (K ^ 2 * hsNormSq (m : ℝ) F) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

end HRS.PDE
