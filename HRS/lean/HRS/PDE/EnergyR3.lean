import HRS.PDE.EnergyNonlocal

/-!
# Regime R3: interpolation and Young inequalities, weighted pairing bounds
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- Weighted Cauchy–Schwarz: `‖∑ conj(w) σ a‖ ≤ c₀ A₁ A₂` when `‖σ‖ ≤ c₀ ρ₁ ρ₂`,
`∑ ρ₁²‖w‖² ≤ A₁²`, `∑ ρ₂²‖a‖² ≤ A₂²`. -/
theorem weighted_pairing_bound {ι : Type*} (S : Finset ι) (w σ a : ι → ℂ) (ρ₁ ρ₂ : ι → ℝ)
    (hρ₁ : ∀ k, 0 ≤ ρ₁ k) (hρ₂ : ∀ k, 0 ≤ ρ₂ k) (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (hσ : ∀ k, ‖σ k‖ ≤ c₀ * (ρ₁ k * ρ₂ k)) (A₁ A₂ : ℝ) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h₁ : ∑ k ∈ S, ρ₁ k ^ 2 * ‖w k‖ ^ 2 ≤ A₁ ^ 2) (h₂ : ∑ k ∈ S, ρ₂ k ^ 2 * ‖a k‖ ^ 2 ≤ A₂ ^ 2) :
    ‖∑ k ∈ S, conj (w k) * (σ k * a k)‖ ≤ c₀ * (A₁ * A₂) := by
  have hcs := cs_bound S (fun k => (ρ₁ k : ℂ) * w k) (fun k => (ρ₂ k : ℂ) * a k) A₁ A₂ hA₁ hA₂
    (by simpa [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (hρ₁ _), sq_abs] using h₁)
    (by simpa [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (hρ₂ _), sq_abs] using h₂)
  calc ‖∑ k ∈ S, conj (w k) * (σ k * a k)‖
      ≤ ∑ k ∈ S, ‖conj (w k) * (σ k * a k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ S, c₀ * (‖(ρ₁ k : ℂ) * w k‖ * ‖(ρ₂ k : ℂ) * a k‖) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul, norm_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_of_nonneg (hρ₁ k), Real.norm_of_nonneg (hρ₂ k)]
        have := hσ k
        nlinarith [norm_nonneg (w k), norm_nonneg (a k), norm_nonneg (σ k), hρ₁ k, hρ₂ k,
          mul_nonneg (norm_nonneg (w k)) (norm_nonneg (a k)),
          mul_le_mul_of_nonneg_left this (mul_nonneg (norm_nonneg (w k)) (norm_nonneg (a k)))]
    _ = c₀ * ∑ k ∈ S, ‖(ρ₁ k : ℂ) * w k‖ * ‖(ρ₂ k : ℂ) * a k‖ := by rw [Finset.mul_sum]
    _ ≤ c₀ * (A₁ * A₂) := mul_le_mul_of_nonneg_left hcs hc₀


theorem sobWeight_zeroE (k : Lattice d) : sobWeight 0 k = 1 := by
  unfold sobWeight; rw [Real.rpow_zero]

theorem sobWeight_oneE (k : Lattice d) : sobWeight 1 k = 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  unfold sobWeight; rw [Real.rpow_one]

/-- Interpolation `‖c‖²_{H^λ} ≤ a₀^{1-λ} a₁^λ` from the black-box Hölder inequality. -/
theorem interp_bound (c : Coeff d) (lam a₀ a₁ : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (h0 : MemHs 0 c) (h1 : MemHs 1 c) (hc0 : hsNormSq 0 c ≤ a₀) (hc1 : hsNormSq 1 c ≤ a₁) :
    MemHs lam c ∧ hsNormSq lam c ≤ a₀ ^ (1 - lam) * a₁ ^ lam := by
  obtain ⟨hm, hle⟩ := hsNormSq_interpolation 0 1 lam hl0 hl1 c h0 h1
  have e : (1 - lam) * 0 + lam * 1 = lam := by ring
  rw [e] at hm hle
  refine ⟨hm, hle.trans ?_⟩
  have p0 := hsNormSq_nonnegE 0 c
  have p1 := hsNormSq_nonnegE 1 c
  exact mul_le_mul (Real.rpow_le_rpow p0 hc0 (by linarith)) (Real.rpow_le_rpow p1 hc1 hl0)
    (Real.rpow_nonneg p1 _) (Real.rpow_nonneg (p0.trans hc0) _)

theorem le_rpow_mix (A B lam : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    A ≤ A ^ (1 - lam) * B ^ lam := by
  calc A = A ^ (1 - lam) * A ^ lam := by
        rw [← Real.rpow_add' hA (by linarith)]; simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hA hAB hl0)
          (Real.rpow_nonneg hA _)

theorem rpow_mix_mul (C A B lam : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (C * A) ^ (1 - lam) * (C * B) ^ lam = C * (A ^ (1 - lam) * B ^ lam) := by
  rw [Real.mul_rpow hC hA, Real.mul_rpow hC hB]
  have : C ^ (1 - lam) * C ^ lam = C := by
    by_cases hC0 : C = 0
    · subst hC0
      by_cases h1 : 1 - lam = 0
      · have : lam = 1 := by linarith
        subst this; simp
      · by_cases h2 : lam = 0
        · subst h2; simp
        · simp [Real.zero_rpow h1, Real.zero_rpow h2]
    · rw [← Real.rpow_add (lt_of_le_of_ne hC (Ne.symm hC0))]; simp
  calc C ^ (1 - lam) * A ^ (1 - lam) * (C ^ lam * B ^ lam)
      = (C ^ (1 - lam) * C ^ lam) * (A ^ (1 - lam) * B ^ lam) := by ring
    _ = _ := by rw [this]

/-- Young's inequality in the form `P^{1-λ} Q^λ ≤ ε Q + ε^{-λ/(1-λ)} P`. -/
theorem young_mix (P Q ε lam : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hε : 0 < ε) (hl0 : 0 < lam)
    (hl1 : lam < 1) : P ^ (1 - lam) * Q ^ lam ≤ ε * Q + ε ^ (-(lam / (1 - lam))) * P := by
  have hw := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - lam) (w₂ := lam)
    (p₁ := ε ^ (-(lam / (1 - lam))) * P) (p₂ := ε * Q) (by linarith) hl0.le
    (by positivity) (by positivity) (by ring)
  have e : (ε ^ (-(lam / (1 - lam))) * P) ^ (1 - lam) * (ε * Q) ^ lam = P ^ (1 - lam) * Q ^ lam := by
    rw [Real.mul_rpow (by positivity) hP, Real.mul_rpow hε.le hQ]
    have : (ε ^ (-(lam / (1 - lam)))) ^ (1 - lam) * ε ^ lam = 1 := by
      rw [← Real.rpow_mul hε.le, ← Real.rpow_add hε]
      have h1 : (1 - lam) ≠ 0 := by linarith
      have : -(lam / (1 - lam)) * (1 - lam) + lam = 0 := by field_simp; ring
      rw [this]; simp
    calc (ε ^ (-(lam / (1 - lam)))) ^ (1 - lam) * P ^ (1 - lam) * (ε ^ lam * Q ^ lam)
        = ((ε ^ (-(lam / (1 - lam)))) ^ (1 - lam) * ε ^ lam) * (P ^ (1 - lam) * Q ^ lam) := by ring
      _ = _ := by rw [this, one_mul]
  rw [e] at hw
  have hpos : 0 ≤ ε ^ (-(lam / (1 - lam))) * P := by positivity
  nlinarith [mul_nonneg hε.le hQ]


/-! ### Facts about `w = ∂^α F` -/

theorem sobWeight_one_mul_le (α : Fin d → ℕ) (m : ℕ) (hα : ∑ i, α i ≤ m) (F : Coeff d)
    (k : Lattice d) :
    sobWeight 1 k * ‖multiDerivCoeff α F k‖ ^ 2 ≤ sobWeight ((m + 1 : ℕ) : ℝ) k * ‖F k‖ ^ 2 := by
  rw [norm_sq_multiDerivCoeff, sobWeight_oneE, sobWeight_natCast]
  have h1 := weight_le_pow α k
  have h2 : (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (∑ i, α i) ≤
      (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m := pow_le_pow_right₀ (one_le_sobBaseE k) hα
  calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) *
        ((∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖F k‖ ^ 2)
      = ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) *
          ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) * ‖F k‖ ^ 2 := by ring
    _ ≤ ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) *
          (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m) * ‖F k‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith [one_le_sobBaseE k])
    _ = _ := by rw [pow_succ]; ring

theorem hsNormSq_one_multiDeriv_le {n : ℕ} (α : Fin d → ℕ) (m : ℕ) (hα : ∑ i, α i ≤ m)
    (F : Coeff d) (hF : IsTrigPoly n F) :
    hsNormSq 1 (multiDerivCoeff α F) ≤ hsNormSq ((m + 1 : ℕ) : ℝ) F := by
  rw [hsNormSq_of_isTrigPoly (isTrigPoly_multiDerivCoeff hF α), hsNormSq_of_isTrigPoly hF]
  exact Finset.sum_le_sum fun k _ => sobWeight_one_mul_le α m hα F k

theorem hsNormSq_zero_multiDeriv_le {n : ℕ} (α : Fin d → ℕ) (m : ℕ) (hα : ∑ i, α i ≤ m)
    (F : Coeff d) (hF : IsTrigPoly n F) :
    hsNormSq 0 (multiDerivCoeff α F) ≤ hsNormSq (m : ℝ) F := by
  rw [hsNormSq_of_isTrigPoly (isTrigPoly_multiDerivCoeff hF α), hsNormSq_of_isTrigPoly hF]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_sq_multiDerivCoeff, sobWeight_zeroE, sobWeight_natCast, one_mul]
  exact mul_le_mul_of_nonneg_right ((weight_le_pow α k).trans
    (pow_le_pow_right₀ (one_le_sobBaseE k) hα)) (sq_nonneg _)

theorem hsNormSq_mono_nat {n : ℕ} (m : ℕ) (F : Coeff d) (hF : IsTrigPoly n F) :
    hsNormSq (m : ℝ) F ≤ hsNormSq ((m + 1 : ℕ) : ℝ) F := by
  rw [hsNormSq_of_isTrigPoly hF, hsNormSq_of_isTrigPoly hF]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (sobWeight_monoE (by push_cast; linarith) k) (sq_nonneg _)

/-- `‖D_i D_α F‖²` is controlled by the `H^{m+1}` norm. -/
theorem sum_sq_deriv_multiDeriv_le {n : ℕ} (α : Fin d → ℕ) (m : ℕ) (hα : ∑ i, α i ≤ m)
    (F : Coeff d) (hF : IsTrigPoly n F) (i : Fin d) (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖derivCoeff i (multiDerivCoeff α F) k‖ ^ 2 ≤ hsNormSq ((m + 1 : ℕ) : ℝ) F := by
  rw [derivCoeff_eq_multi, ← multiDerivCoeff_add]
  refine sum_sq_multiDeriv_le _ (m + 1) ?_ F (memHs_of_isTrigPolyE hF _) S
  have : ∑ j, (Pi.single i 1 + α : Fin d → ℕ) j = 1 + ∑ j, α j := by
    simp [Finset.sum_add_distrib]
  omega

/-- `H^λ` bound for `w = ∂^α F` by interpolation. -/
theorem hsNormSq_lam_multiDeriv_le {n : ℕ} (α : Fin d → ℕ) (m : ℕ) (hα : ∑ i, α i ≤ m)
    (F : Coeff d) (hF : IsTrigPoly n F) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    hsNormSq lam (multiDerivCoeff α F) ≤
      hsNormSq (m : ℝ) F ^ (1 - lam) * hsNormSq ((m + 1 : ℕ) : ℝ) F ^ lam := by
  have hw := isTrigPoly_multiDerivCoeff hF α
  exact (interp_bound _ lam _ _ hl0 hl1 (memHs_of_isTrigPolyE hw _) (memHs_of_isTrigPolyE hw _)
    (hsNormSq_zero_multiDeriv_le α m hα F hF) (hsNormSq_one_multiDeriv_le α m hα F hF)).2

/-! ### `H¹` bound for a product -/

theorem sobWeight_one_mul_norm_sq (u : Coeff d) (k : Lattice d) :
    sobWeight 1 k * ‖u k‖ ^ 2 = ‖u k‖ ^ 2 + ∑ i, ‖derivCoeff i u k‖ ^ 2 := by
  have : ∀ i, ‖derivCoeff i u k‖ ^ 2 = (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖u k‖ ^ 2 := by
    intro i
    show ‖(2 * Real.pi * Complex.I * (k i : ℂ)) * u k‖ ^ 2 = _
    rw [norm_mul, mul_pow, norm_symbol_factor, sq_abs]
  simp_rw [this]
  rw [← Finset.sum_mul, ← four_pi_enorm_sq, sobWeight_oneE]
  ring

theorem conv_H1_bound (a : Coeff d) (Λ : ℝ)
    (ha0 : ∃ φ : Torus d → ℝ, Continuous φ ∧ coeffOf φ = a ∧ ∀ x, |φ x| ≤ Λ)
    (ha1 : ∀ i : Fin d, ∃ φ : Torus d → ℝ, Continuous φ ∧ coeffOf φ = derivCoeff i a ∧
      ∀ x, |φ x| ≤ Λ)
    {n : ℕ} (w : Coeff d) (hw : IsTrigPoly n w) (A Bq : ℝ)
    (hA : ∑ k ∈ boxFin d n, ‖w k‖ ^ 2 ≤ A)
    (hB : ∀ i, ∑ k ∈ boxFin d n, ‖derivCoeff i w k‖ ^ 2 ≤ Bq) (hAB : A ≤ Bq) :
    MemHs 0 (mulCoeff a w) ∧ MemHs 1 (mulCoeff a w) ∧
      hsNormSq 0 (mulCoeff a w) ≤ Λ ^ 2 * A ∧
      hsNormSq 1 (mulCoeff a w) ≤ ((1 + 4 * (d : ℝ)) * Λ ^ 2) * Bq := by
  classical
  obtain ⟨φ0, hφ0c, hφ0, hφ0K⟩ := ha0
  have hbdd0 : ∀ S : Finset (Lattice d), ∑ k ∈ S, ‖mulCoeff a w k‖ ^ 2 ≤ Λ ^ 2 * A := by
    intro S
    have := l2_mul_le φ0 hφ0c Λ hφ0K n w hw S
    rw [hφ0] at this
    exact this.trans (mul_le_mul_of_nonneg_left hA (sq_nonneg _))
  have hbddi : ∀ i, ∀ S : Finset (Lattice d),
      ∑ k ∈ S, ‖derivCoeff i (mulCoeff a w) k‖ ^ 2 ≤ 2 * (Λ ^ 2 * A) + 2 * (Λ ^ 2 * Bq) := by
    intro i S
    obtain ⟨φ1, hφ1c, hφ1, hφ1K⟩ := ha1 i
    have hwi : IsTrigPoly n (derivCoeff i w) := by
      rw [derivCoeff_eq_multi]; exact isTrigPoly_multiDerivCoeff hw _
    have e1 := l2_mul_le φ1 hφ1c Λ hφ1K n w hw S
    have e2 := l2_mul_le φ0 hφ0c Λ hφ0K n (derivCoeff i w) hwi S
    rw [hφ1] at e1
    rw [hφ0] at e2
    have hpt : ∀ k, ‖derivCoeff i (mulCoeff a w) k‖ ^ 2 ≤
        2 * ‖mulCoeff (derivCoeff i a) w k‖ ^ 2 + 2 * ‖mulCoeff a (derivCoeff i w) k‖ ^ 2 := by
      intro k
      rw [derivCoeff_mulCoeff i a w hw k]
      have := norm_add_le (mulCoeff (derivCoeff i a) w k) (mulCoeff a (derivCoeff i w) k)
      nlinarith [norm_nonneg (mulCoeff (derivCoeff i a) w k),
        norm_nonneg (mulCoeff a (derivCoeff i w) k),
        sq_nonneg (‖mulCoeff (derivCoeff i a) w k‖ - ‖mulCoeff a (derivCoeff i w) k‖),
        norm_nonneg (mulCoeff (derivCoeff i a) w k + mulCoeff a (derivCoeff i w) k)]
    calc ∑ k ∈ S, ‖derivCoeff i (mulCoeff a w) k‖ ^ 2
        ≤ ∑ k ∈ S, (2 * ‖mulCoeff (derivCoeff i a) w k‖ ^ 2 +
            2 * ‖mulCoeff a (derivCoeff i w) k‖ ^ 2) := Finset.sum_le_sum fun k _ => hpt k
      _ = 2 * ∑ k ∈ S, ‖mulCoeff (derivCoeff i a) w k‖ ^ 2 +
            2 * ∑ k ∈ S, ‖mulCoeff a (derivCoeff i w) k‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * (Λ ^ 2 * A) + 2 * (Λ ^ 2 * Bq) := by
          refine add_le_add (mul_le_mul_of_nonneg_left (e1.trans
            (mul_le_mul_of_nonneg_left hA (sq_nonneg _))) (by norm_num))
            (mul_le_mul_of_nonneg_left (e2.trans (mul_le_mul_of_nonneg_left (hB i)
              (sq_nonneg _))) (by norm_num))
  have hbdd1 : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight 1 k * ‖mulCoeff a w k‖ ^ 2 ≤
      ((1 + 4 * (d : ℝ)) * Λ ^ 2) * Bq := by
    intro S
    simp_rw [sobWeight_one_mul_norm_sq]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have hA0 : 0 ≤ A := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans hA
    calc ∑ k ∈ S, ‖mulCoeff a w k‖ ^ 2 +
          ∑ i : Fin d, ∑ k ∈ S, ‖derivCoeff i (mulCoeff a w) k‖ ^ 2
        ≤ Λ ^ 2 * A + ∑ _i : Fin d, (2 * (Λ ^ 2 * A) + 2 * (Λ ^ 2 * Bq)) :=
          add_le_add (hbdd0 S) (Finset.sum_le_sum fun i _ => hbddi i S)
      _ = Λ ^ 2 * A + (d : ℝ) * (2 * (Λ ^ 2 * A) + 2 * (Λ ^ 2 * Bq)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((1 + 4 * (d : ℝ)) * Λ ^ 2) * Bq := by
          have h1 : Λ ^ 2 * A ≤ Λ ^ 2 * Bq := mul_le_mul_of_nonneg_left hAB (sq_nonneg _)
          have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          nlinarith [mul_nonneg h2 (mul_nonneg (sq_nonneg Λ) (sub_nonneg.mpr hAB))]
  have hs0 : Summable fun k => sobWeight 0 k * ‖mulCoeff a w k‖ ^ 2 := by
    simp_rw [sobWeight_zeroE, one_mul]
    exact summable_of_sum_le (fun k => sq_nonneg _) hbdd0
  have hs1 : Summable fun k => sobWeight 1 k * ‖mulCoeff a w k‖ ^ 2 :=
    summable_of_sum_le (fun k => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)) hbdd1
  refine ⟨hs0, hs1, ?_, ?_⟩
  · unfold hsNormSq
    simp_rw [sobWeight_zeroE, one_mul]
    exact Real.tsum_le_of_sum_le (fun k => sq_nonneg _) hbdd0
  · exact Real.tsum_le_of_sum_le (fun k => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)) hbdd1


theorem sobWeight_sq (r : ℝ) (k : Lattice d) : sobWeight r k ^ 2 = sobWeight (2 * r) k := by
  unfold sobWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [one_le_sobBaseE k])]
  congr 1
  push_cast; ring

theorem nonlocalCoeff_apply (D : DynData d) (μ : Torus d → ℝ) (F : Coeff d) (k : Lattice d) :
    nonlocalCoeff D μ F k = ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
      (((2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d D.s k : ℝ) : ℂ)) *
        mulCoeff (coeffOf μ) (derivCoeff j F) k) := by
  unfold nonlocalCoeff
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [gradRieszCoeff, derivCoeff, rieszMult]
  ring

/-- The constant of the key R3 estimate for a fixed multi-index. -/
def r3Const (d : ℕ) (s : ℝ) (MB Λ : ℝ) (α : Fin d → ℕ) : ℝ :=
  (d : ℝ) ^ 2 * |MB| * (|rieszConst d s| * Real.sqrt ((1 + 4 * (d : ℝ)) * Λ ^ 2) +
    |rieszConst d s| * |Λ| * (1 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ)))

theorem r3Const_nonneg (s MB Λ : ℝ) (α : Fin d → ℕ) : 0 ≤ r3Const d s MB Λ α := by
  unfold r3Const
  positivity


theorem nonlocal_R3_key (s : ℝ) (hθ0 : 0 < s + 2 - d) (hθ2 : s + 2 - d < 2) (m : ℕ) (MB Λ : ℝ)
    (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (μ : Torus d → ℝ)
    (hμ : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (Torus.lift μ))
    (hΛ : Torus.cbNorm (m + 3) μ ≤ Λ)
    (α : Fin d → ℕ) (hα : ∑ i, α i ≤ m) {n : ℕ} (F : Coeff d) (hF : IsTrigPoly n F) :
    |(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (nonlocalCoeff D μ F) F).re| ≤
      r3Const d s MB Λ α * (hsNormSq (m : ℝ) F ^ (1 - (s + 2 - d) / 2) *
        hsNormSq ((m + 1 : ℕ) : ℝ) F ^ ((s + 2 - d) / 2)) := by
  classical
  subst hDs
  set s := D.s with hs
  set lam : ℝ := (s + 2 - d) / 2 with hlam
  have hl0 : 0 < lam := by rw [hlam]; linarith
  have hl1 : lam < 1 := by rw [hlam]; linarith
  set A := hsNormSq (m : ℝ) F with hAdef
  set Bq := hsNormSq ((m + 1 : ℕ) : ℝ) F with hBdef
  have hAB : A ≤ Bq := hsNormSq_mono_nat m F hF
  have hA0 : 0 ≤ A := hsNormSq_nonnegE _ _
  set R := A ^ (1 - lam) * Bq ^ lam with hRdef
  have hR0 : 0 ≤ R := mul_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg (hA0.trans hAB) _)
  have hAR : A ≤ R := le_rpow_mix A Bq lam hA0 hAB hl0.le hl1.le
  have hMem : MemHs (m : ℝ) F := memHs_of_isTrigPolyE hF _
  set w := multiDerivCoeff α F with hwdef
  have hw : IsTrigPoly n w := isTrigPoly_multiDerivCoeff hF α
  have hwA : ∑ k ∈ boxFin d n, ‖w k‖ ^ 2 ≤ A := sum_sq_multiDeriv_le α m hα F hMem _
  have hwB : ∀ i, ∑ k ∈ boxFin d n, ‖derivCoeff i w k‖ ^ 2 ≤ Bq :=
    fun i => sum_sq_deriv_multiDeriv_le α m hα F hF i _
  have hwlam : hsNormSq lam w ≤ R := hsNormSq_lam_multiDeriv_le α m hα F hF lam hl0.le hl1.le
  have hder : ∀ j, IsTrigPoly n (derivCoeff j F) := fun j => by
    rw [derivCoeff_eq_multi]; exact isTrigPoly_multiDerivCoeff hF _
  -- function data for μ
  have hμ0 : ∃ φ : Torus d → ℝ, Continuous φ ∧ coeffOf φ = coeffOf μ ∧ ∀ x, |φ x| ≤ Λ := by
    obtain ⟨φ, hc, hφ, hb⟩ := exists_derivFun μ (m + 3) hμ 0 (by simp)
    exact ⟨φ, hc, by rw [hφ, multiDerivCoeff_zero], fun x => (hb x).trans hΛ⟩
  have hμi : ∀ i : Fin d, ∃ φ : Torus d → ℝ, Continuous φ ∧
      coeffOf φ = derivCoeff i (coeffOf μ) ∧ ∀ x, |φ x| ≤ Λ := by
    intro i
    obtain ⟨φ, hc, hφ, hb⟩ := exists_derivFun μ (m + 3) hμ (Pi.single i 1) (by simp)
    exact ⟨φ, hc, by rw [hφ, derivCoeff_eq_multi], fun x => (hb x).trans hΛ⟩
  obtain ⟨hu0, hu1, hu0b, hu1b⟩ := conv_H1_bound (coeffOf μ) Λ hμ0 hμi w hw A Bq hwA hwB hAB
  set u := mulCoeff (coeffOf μ) w with hudef
  set C₁ : ℝ := (1 + 4 * (d : ℝ)) * Λ ^ 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hulam : MemHs lam u ∧ hsNormSq lam u ≤ C₁ * R := by
    have hΛC : Λ ^ 2 ≤ C₁ := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith [sq_nonneg Λ]
    obtain ⟨h1, h2⟩ := interp_bound u lam (C₁ * A) (C₁ * Bq) hl0.le hl1.le hu0 hu1
      (hu0b.trans (mul_le_mul_of_nonneg_right hΛC hA0)) hu1b
    refine ⟨h1, h2.trans ?_⟩
    rw [rpow_mix_mul C₁ A Bq lam hC₁0 hA0 (hA0.trans hAB)]
  set c₀ : ℝ := |rieszConst d s| with hc₀
  have hc₀0 : 0 ≤ c₀ := abs_nonneg _
  set ρ : Lattice d → ℝ := fun k => sobWeight ((s + 2 - d) / 4) k with hρdef
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => sobWeight_nonnegE _ _
  have hρsq : ∀ k, ρ k ^ 2 = sobWeight lam k := fun k => by
    simp only [hρdef]; rw [sobWeight_sq]; congr 1; rw [hlam]; ring
  have hρρ : ∀ k, ρ k * ρ k = sobWeight lam k := fun k => by rw [← sq]; exact hρsq k
  have hwρ : ∑ k ∈ boxFin d n, ρ k ^ 2 * ‖w k‖ ^ 2 ≤ (Real.sqrt R) ^ 2 := by
    rw [Real.sq_sqrt hR0]
    simp_rw [hρsq]
    rw [← hsNormSq_of_isTrigPoly hw lam]
    exact hwlam
  have hsqrtR : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR0
  -- bounds for `β ≠ 0` and `Y'`
  have hUbound : ∀ (i j : Fin d), ∀ β ∈ (leibnizSet α).erase 0,
      ‖∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) *
        mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖
        ≤ c₀ * (|Λ| * R) := by
    intro i j β hβ
    have hβ0 : β ≠ 0 := (Finset.mem_erase.mp hβ).1
    have hβα := mem_leibnizSet.mp (Finset.mem_erase.mp hβ).2
    have hsβ : 1 ≤ ∑ i, β i := by
      by_contra h
      apply hβ0
      funext i
      have : ∑ i, β i = 0 := by omega
      simpa using (Finset.sum_eq_zero_iff.mp this) i (Finset.mem_univ i)
    have hsβ' : ∑ i, β i ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => hβα i
    obtain ⟨φ, hφc, hφ, hφK⟩ := exists_derivFun μ (m + 3) hμ β (by omega)
    have hφK' : ∀ x, |φ x| ≤ Λ := fun x => (hφK x).trans hΛ
    have hc' : IsTrigPoly n (multiDerivCoeff (α - β) (derivCoeff j F)) :=
      isTrigPoly_multiDerivCoeff (hder j) _
    have hcN : ∑ k ∈ boxFin d n, ‖multiDerivCoeff (α - β) (derivCoeff j F) k‖ ^ 2 ≤ A := by
      rw [derivCoeff_eq_multi, ← multiDerivCoeff_add]
      refine sum_sq_multiDeriv_le _ m ?_ F hMem _
      have := sum_sub_add_single α β hβα j
      omega
    have h1 := l2_mul_le φ hφc Λ hφK' n _ hc' (boxFin d n)
    rw [hφ] at h1
    have h2 : ∑ k ∈ boxFin d n, (fun _ => (1 : ℝ)) k ^ 2 *
        ‖mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k‖ ^ 2
        ≤ (|Λ| * Real.sqrt R) ^ 2 := by
      simp only [one_pow, one_mul]
      calc _ ≤ Λ ^ 2 * ∑ k ∈ boxFin d n, ‖multiDerivCoeff (α - β) (derivCoeff j F) k‖ ^ 2 := h1
        _ ≤ Λ ^ 2 * R := mul_le_mul_of_nonneg_left (hcN.trans hAR) (sq_nonneg _)
        _ = _ := by rw [mul_pow, sq_abs, Real.sq_sqrt hR0]
    have := weighted_pairing_bound (boxFin d n) w
      (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ))
      (fun k => mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)
      ρ (fun _ => 1) hρ0 (fun _ => zero_le_one) c₀ hc₀0
      (fun k => by simpa [hρdef] using norm_symS_R3 s hθ0 hθ2 i k)
      (Real.sqrt R) (|Λ| * Real.sqrt R) (Real.sqrt_nonneg _) (by positivity) hwρ h2
    calc _ ≤ c₀ * (Real.sqrt R * (|Λ| * Real.sqrt R)) := this
      _ = c₀ * (|Λ| * (Real.sqrt R * Real.sqrt R)) := by ring
      _ = c₀ * (|Λ| * R) := by rw [hsqrtR]
  have hV2bound : ∀ (i j : Fin d),
      ‖∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) * mulCoeff (derivCoeff j (coeffOf μ)) w k)‖
        ≤ c₀ * (|Λ| * R) := by
    intro i j
    obtain ⟨φ, hφc, hφ, hφK⟩ := hμi j
    have h1 := l2_mul_le φ hφc Λ hφK n w hw (boxFin d n)
    rw [hφ] at h1
    have h2 : ∑ k ∈ boxFin d n, (fun _ => (1 : ℝ)) k ^ 2 *
        ‖mulCoeff (derivCoeff j (coeffOf μ)) w k‖ ^ 2 ≤ (|Λ| * Real.sqrt R) ^ 2 := by
      simp only [one_pow, one_mul]
      calc _ ≤ Λ ^ 2 * ∑ k ∈ boxFin d n, ‖w k‖ ^ 2 := h1
        _ ≤ Λ ^ 2 * R := mul_le_mul_of_nonneg_left (hwA.trans hAR) (sq_nonneg _)
        _ = _ := by rw [mul_pow, sq_abs, Real.sq_sqrt hR0]
    have := weighted_pairing_bound (boxFin d n) w
      (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ))
      (fun k => mulCoeff (derivCoeff j (coeffOf μ)) w k)
      ρ (fun _ => 1) hρ0 (fun _ => zero_le_one) c₀ hc₀0
      (fun k => by simpa [hρdef] using norm_symS_R3 s hθ0 hθ2 i k)
      (Real.sqrt R) (|Λ| * Real.sqrt R) (Real.sqrt_nonneg _) (by positivity) hwρ h2
    calc _ ≤ c₀ * (Real.sqrt R * (|Λ| * Real.sqrt R)) := this
      _ = c₀ * (|Λ| * (Real.sqrt R * Real.sqrt R)) := by ring
      _ = c₀ * (|Λ| * R) := by rw [hsqrtR]
  have hV1bound : ∀ (i j : Fin d),
      ‖∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        (2 * Real.pi * Complex.I * (k j : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) * u k)‖
        ≤ c₀ * (Real.sqrt C₁ * R) := by
    intro i j
    have h2 : ∑ k ∈ boxFin d n, ρ k ^ 2 * ‖u k‖ ^ 2 ≤ (Real.sqrt C₁ * Real.sqrt R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC₁0, Real.sq_sqrt hR0]
      simp_rw [hρsq]
      refine le_trans ?_ hulam.2
      exact hulam.1.sum_le_tsum (boxFin d n) (fun k _ => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _))
    have := weighted_pairing_bound (boxFin d n) w
      (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) * (2 * Real.pi * Complex.I * (k j : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ))
      (fun k => u k) ρ ρ hρ0 hρ0 c₀ hc₀0
      (fun k => by
        rw [hρρ]
        exact norm_symT_R3 s hθ0 i j k)
      (Real.sqrt R) (Real.sqrt C₁ * Real.sqrt R) (Real.sqrt_nonneg _) (by positivity) hwρ h2
    calc _ ≤ c₀ * (Real.sqrt R * (Real.sqrt C₁ * Real.sqrt R)) := this
      _ = c₀ * (Real.sqrt C₁ * (Real.sqrt R * Real.sqrt R)) := by ring
      _ = c₀ * (Real.sqrt C₁ * R) := by rw [hsqrtR]
  have hQ : bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (nonlocalCoeff D μ F) F =
      ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) * ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
        ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) *
          mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k) := by
    rw [bilinForm_weight_eq α _ F hF]
    have hN : ∀ k, multiDerivCoeff α (nonlocalCoeff D μ F) k =
        ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
          (((2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
            ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
              mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k) := by
      intro k
      rw [multiDerivCoeff_apply, nonlocalCoeff_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h := multiDerivCoeff_mulCoeff α (coeffOf μ) (derivCoeff j F) (hder j) k
      rw [multiDerivCoeff_apply] at h
      calc (∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ α i) * (((D.M j i : ℝ) : ℂ) *
            (((2 * Real.pi * Complex.I * (k i : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) *
              mulCoeff (coeffOf μ) (derivCoeff j F) k))
          = ((D.M j i : ℝ) : ℂ) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
              ((rieszCoeff d s k : ℝ) : ℂ)) *
              ((∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ α i) *
                mulCoeff (coeffOf μ) (derivCoeff j F) k)) := by ring
        _ = _ := by rw [h]
    simp_rw [hN]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the term `β = 0`
  have hU0 : ∀ i j : Fin d,
      ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) *
          mulCoeff (multiDerivCoeff 0 (coeffOf μ)) (multiDerivCoeff (α - 0) (derivCoeff j F)) k) =
      (∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        (2 * Real.pi * Complex.I * (k j : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) * u k)) -
      ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) * mulCoeff (derivCoeff j (coeffOf μ)) w k) := by
    intro i j
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hE : mulCoeff (multiDerivCoeff 0 (coeffOf μ)) (multiDerivCoeff (α - 0) (derivCoeff j F)) k =
        (2 * Real.pi * Complex.I * (k j : ℂ)) * u k - mulCoeff (derivCoeff j (coeffOf μ)) w k := by
      rw [multiDerivCoeff_zero, tsub_zero, multiDerivCoeff_derivCoeff]
      have h := derivCoeff_mulCoeff j (coeffOf μ) w hw k
      have h' : derivCoeff j u k = 2 * Real.pi * Complex.I * (k j : ℂ) * u k := rfl
      rw [h'] at h
      linear_combination (-1 : ℂ) * h
    rw [hE]
    ring
  have hterm : ∀ i j : Fin d, ‖((D.M j i : ℝ) : ℂ) * ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
        ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) *
          mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖
      ≤ |MB| * ((c₀ * Real.sqrt C₁ + c₀ * |Λ| * (1 + ∑ β ∈ (leibnizSet α).erase 0,
          (binomW α β : ℝ))) * R) := by
    intro i j
    have h0mem : (0 : Fin d → ℕ) ∈ leibnizSet α := mem_leibnizSet.mpr fun i => Nat.zero_le _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hMB : |D.M j i| ≤ |MB| := (hM j i).trans (le_abs_self _)
    refine mul_le_mul hMB ?_ (norm_nonneg _) (abs_nonneg _)
    rw [← Finset.add_sum_erase _ _ h0mem]
    have hb0 : (binomW α 0 : ℂ) = 1 := by simp [binomW]
    rw [hb0, one_mul, hU0]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        (2 * Real.pi * Complex.I * (k j : ℂ)) * ((rieszCoeff d s k : ℝ) : ℂ)) * u k)) -
      ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) * mulCoeff (derivCoeff j (coeffOf μ)) w k)‖ ≤
        c₀ * (Real.sqrt C₁ * R) + c₀ * (|Λ| * R) :=
      (norm_sub_le _ _).trans (add_le_add (hV1bound i j) (hV2bound i j))
    have h2 : ‖∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) *
        ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) *
          mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖ ≤
        (∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ)) * (c₀ * (|Λ| * R)) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun β hβ => ?_
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hUbound i j β hβ) (Nat.cast_nonneg _)
    calc _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
  rw [hQ]
  refine (Complex.abs_re_le_norm _).trans ?_
  calc _ ≤ ∑ i : Fin d, ‖∑ j : Fin d, ((D.M j i : ℝ) : ℂ) * ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
        ∑ k ∈ boxFin d n, conj (w k) * (((2 * Real.pi * Complex.I * (k i : ℂ)) *
          ((rieszCoeff d s k : ℝ) : ℂ)) *
          mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, |MB| * ((c₀ * Real.sqrt C₁ + c₀ * |Λ| * (1 + ∑ β ∈
          (leibnizSet α).erase 0, (binomW α β : ℝ))) * R) := by
        refine Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun j _ => hterm i j
    _ = r3Const d s MB Λ α * R := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold r3Const
        ring


/-- Young absorption step of regime R3. -/
theorem r3_absorb (C₃ R A Bq ε lam e : ℝ) (hC₃ : 0 < C₃) (hA : 0 ≤ A) (hAB : A ≤ Bq) (hε : 0 < ε)
    (hl0 : 0 < lam) (hl1 : lam < 1) (he : e = lam / (1 - lam)) (hR : R = A ^ (1 - lam) * Bq ^ lam) :
    C₃ * R ≤ ε * Bq + (ε⁻¹ ^ e * (C₃ * C₃ ^ e)) * A := by
  have hB : 0 ≤ Bq := hA.trans hAB
  have hy := young_mix (C₃ * A) (C₃ * Bq) (ε / C₃) lam (by positivity) (by positivity)
    (by positivity) hl0 hl1
  rw [rpow_mix_mul C₃ A Bq lam hC₃.le hA hB, ← hR, ← he] at hy
  refine hy.trans ?_
  have e1 : (ε / C₃) * (C₃ * Bq) = ε * Bq := by field_simp
  have e2 : (ε / C₃) ^ (-e) * (C₃ * A) = (ε⁻¹ ^ e * (C₃ * C₃ ^ e)) * A := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hε.le hC₃.le, Real.inv_rpow hε.le]
    have : 0 < C₃ ^ e := Real.rpow_pos_of_pos hC₃ e
    have : 0 < ε ^ e := Real.rpow_pos_of_pos hε e
    field_simp
  rw [e1, e2]

end HRS.PDE
