import HRS.PDE.EnergyR2Lead

/-!
# Regime R2: the commutator terms (`β ≠ 0`) of the Leibniz expansion
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

theorem norm_Ssym_sq_le (s : ℝ) (i : Fin d) (k : Lattice d) :
    ‖Ssym d s i k‖ ^ 2 ≤ |rieszConst d s| ^ 2 * sobWeight (max (s + 1 - d) 0) k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : Ssym d s i 0 = 0 := by simp [Ssym, rieszCoeff]
    rw [h0, norm_zero]
    have := sobWeight_nonnegE (max (s + 1 - d) 0) (0 : Lattice d)
    calc (0 : ℝ) ^ 2 = 0 := by norm_num
      _ ≤ _ := mul_nonneg (sq_nonneg _) this
  · have h1 : ‖Ssym d s i k‖ ≤ |rieszConst d s| * rad k ^ (s - (d : ℝ) + 1) :=
      norm_symS_le s i k hk
    have hr1 := one_le_rad k hk
    have h2 : rad k ^ (s - (d : ℝ) + 1) ≤ rad k ^ (max (s + 1 - d) 0) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by
        have := le_max_left (s + 1 - d) 0
        linarith)
    have h3 : (rad k ^ (max (s + 1 - d) 0)) ^ 2 ≤ sobWeight (max (s + 1 - d) 0) k := by
      have := rad_rpow_le_sobWeight k (max (s + 1 - d) 0) (le_max_right _ _)
      have e : rad k ^ (2 * max (s + 1 - d) 0) = (rad k ^ (max (s + 1 - d) 0)) ^ 2 := by
        rw [mul_comm, Real.rpow_mul (rad_nonneg k), Real.rpow_two]
      rwa [e] at this
    have h4 : ‖Ssym d s i k‖ ≤ |rieszConst d s| * rad k ^ (max (s + 1 - d) 0) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    calc ‖Ssym d s i k‖ ^ 2 ≤ (|rieszConst d s| * rad k ^ (max (s + 1 - d) 0)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h4 2
      _ = |rieszConst d s| ^ 2 * (rad k ^ (max (s + 1 - d) 0)) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)

theorem Spair_bound (s : ℝ) (i : Fin d) {n : ℕ} (w U : Coeff d) (A B : ℝ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hw : ∑ k ∈ boxFin d n, ‖w k‖ ^ 2 ≤ A ^ 2)
    (hU : ∑ k ∈ boxFin d n, sobWeight (max (s + 1 - d) 0) k * ‖U k‖ ^ 2 ≤ B ^ 2) :
    ‖∑ k ∈ boxFin d n, conj (w k) * (Ssym d s i k * U k)‖ ≤ |rieszConst d s| * (A * B) := by
  set c₀ := |rieszConst d s| with hc₀
  have hc0 : 0 ≤ c₀ := abs_nonneg _
  have h1 : ∑ k ∈ boxFin d n, ‖Ssym d s i k * U k‖ ^ 2 ≤ (c₀ * B) ^ 2 := by
    calc ∑ k ∈ boxFin d n, ‖Ssym d s i k * U k‖ ^ 2
        ≤ ∑ k ∈ boxFin d n, c₀ ^ 2 * (sobWeight (max (s + 1 - d) 0) k * ‖U k‖ ^ 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, mul_pow]
          calc ‖Ssym d s i k‖ ^ 2 * ‖U k‖ ^ 2
              ≤ (c₀ ^ 2 * sobWeight (max (s + 1 - d) 0) k) * ‖U k‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (norm_Ssym_sq_le s i k) (sq_nonneg _)
            _ = _ := by ring
      _ = c₀ ^ 2 * ∑ k ∈ boxFin d n, sobWeight (max (s + 1 - d) 0) k * ‖U k‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ c₀ ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hU (sq_nonneg _)
      _ = (c₀ * B) ^ 2 := by ring
  have h2 := cs_bound (boxFin d n) w (fun k => Ssym d s i k * U k) A (c₀ * B) hA
    (mul_nonneg hc0 hB) hw h1
  calc ‖∑ k ∈ boxFin d n, conj (w k) * (Ssym d s i k * U k)‖
      ≤ ∑ k ∈ boxFin d n, ‖conj (w k) * (Ssym d s i k * U k)‖ := norm_sum_le _ _
    _ = ∑ k ∈ boxFin d n, ‖w k‖ * ‖Ssym d s i k * U k‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ A * (c₀ * B) := h2
    _ = _ := by ring

theorem sum_sub_succ_le {α β : Fin d → ℕ} (hβα : β ∈ leibnizSet α) (hβ0 : β ≠ 0) :
    ∑ i, (α - β) i + 1 ≤ ∑ i, α i := by
  have h1 : ∑ i, (α - β) i + ∑ i, β i = ∑ i, α i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (mem_leibnizSet.mp hβα i)
  have h2 : 1 ≤ ∑ i, β i := by
    by_contra h
    apply hβ0
    funext i
    have : ∑ i, β i = 0 := by omega
    exact (Finset.sum_eq_zero_iff.mp this) i (Finset.mem_univ _)
  omega

theorem hsNormSq_mono_trig {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) {a b : ℝ} (h : a ≤ b) :
    hsNormSq a c ≤ hsNormSq b c := by
  rw [hsNormSq_of_isTrigPoly hc, hsNormSq_of_isTrigPoly hc]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (sobWeight_monoE h k) (sq_nonneg _)

theorem c01Norm_nonneg' (a : Torus d → ℝ) : 0 ≤ Torus.c01Norm a := by
  unfold Torus.c01Norm
  refine add_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _) ?_
  exact Real.iSup_nonneg fun p => by positivity

/-- The `H^σ` product bound of Lemma C.5(ii) at the level of coefficients. -/
theorem prod_hs_bound (hd : 1 ≤ d) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L A : ℝ) (φ : Torus d → ℝ), Torus.IsLipschitz L φ → (∀ x, |φ x| ≤ A) →
      ∀ (n : ℕ) (f : Coeff d), IsRealCoeff f → IsTrigPoly n f →
        MemHs σ (mulCoeff (coeffOf φ) f) ∧
        hsNormSq σ (mulCoeff (coeffOf φ) f) ≤ C * (A + |L| * Real.sqrt d) ^ 2 * hsNormSq σ f := by
  obtain ⟨C₁, hC₁⟩ := product_toolbox_frac hd σ hσ0 hσ1
  refine ⟨C₁ ^ 2, sq_nonneg _, fun L A φ hφ hA n f hf hft => ?_⟩
  have hφc : Continuous φ := continuous_of_isLipschitz hφ
  set u := toFun f with hu
  have huc : Continuous u := continuous_toFun_trig hf hft
  have huS : MemSobolev σ u := memSobolev_toFun_trig hf hft σ
  obtain ⟨hmem, hnorm⟩ := hC₁ L φ hφ u huS
  have hcoef : coeffOf (fun x => φ x * u x) = mulCoeff (coeffOf φ) f := by
    rw [coeffOf_mul φ u (memLp_of_continuous_real hφc) (memLp_of_continuous_real huc),
      hu, coeffOf_toFun_trig hf hft]
  obtain ⟨hM1, hE1⟩ := hsNormSq_coeffOf σ _ hmem
  obtain ⟨hM2, hE2⟩ := hsNormSq_coeffOf σ _ huS
  rw [hcoef] at hM1 hE1
  have hcu : coeffOf u = f := by rw [hu, coeffOf_toFun_trig hf hft]
  rw [hcu] at hE2
  refine ⟨hM1, ?_⟩
  rw [hE1, hE2]
  have hc01 := c01Norm_le hφ hA
  have hc0 := c01Norm_nonneg' φ
  have hs0 : 0 ≤ sobolevNorm σ u := Real.sqrt_nonneg _
  have hs1 : 0 ≤ sobolevNorm σ (fun x => φ x * u x) := Real.sqrt_nonneg _
  calc sobolevNorm σ (fun x => φ x * u x) ^ 2
      ≤ (C₁ * Torus.c01Norm φ * sobolevNorm σ u) ^ 2 := by
        apply pow_le_pow_left₀ hs1 hnorm
    _ = C₁ ^ 2 * Torus.c01Norm φ ^ 2 * sobolevNorm σ u ^ 2 := by ring
    _ ≤ C₁ ^ 2 * (A + |L| * Real.sqrt d) ^ 2 * sobolevNorm σ u ^ 2 := by
        gcongr

theorem Spair_bound' (s : ℝ) (i : Fin d) {n : ℕ} (w U : Coeff d) (N1 N2 : ℝ) (h1 : 0 ≤ N1)
    (h2 : 0 ≤ N2) (hw : ∑ k ∈ boxFin d n, ‖w k‖ ^ 2 ≤ N1)
    (hU : ∑ k ∈ boxFin d n, sobWeight (max (s + 1 - d) 0) k * ‖U k‖ ^ 2 ≤ N2) :
    ‖∑ k ∈ boxFin d n, conj (w k) * (Ssym d s i k * U k)‖ ≤ |rieszConst d s| * ((N1 + N2) / 2) := by
  have hA := Real.sq_sqrt h1
  have hB := Real.sq_sqrt h2
  have := Spair_bound s i w U (Real.sqrt N1) (Real.sqrt N2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (by rw [hA]; exact hw) (by rw [hB]; exact hU)
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  nlinarith [sq_nonneg (Real.sqrt N1 - Real.sqrt N2)]

/-- `∑_{k ∈ box} |D_γ F(k)|² ≤ ‖F‖²_{H^m}` for `|γ| ≤ m`. -/
theorem sum_box_multiDeriv_le {n : ℕ} (γ : Fin d → ℕ) (m : ℕ) (hγ : ∑ i, γ i ≤ m) (F : Coeff d)
    (hF : IsTrigPoly n F) (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖multiDerivCoeff γ F k‖ ^ 2 ≤ hsNormSq m F :=
  sum_sq_multiDeriv_le γ m hγ F (memHs_of_isTrigPolyE hF _) S

theorem isLipschitz_mono {φ : Torus d → ℝ} {L L' : ℝ} (h : Torus.IsLipschitz L φ) (hL : L ≤ L') :
    Torus.IsLipschitz L' φ := by
  intro x y
  exact (h x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- The derivative function `∂^β μ` (`|β| ≤ m+1`) is continuous, bounded by `Λ`, `Λ`-Lipschitz,
with the right coefficients. -/
theorem derivFn_bd {μ : Torus d → ℝ} {m : ℕ} {Λ : ℝ} (hμ : Torus.IsCk (m + 3) μ)
    (hΛ : Torus.cbNorm (m + 3) μ ≤ Λ) (β : Fin d → ℕ) (hβ : ∑ i, β i ≤ m + 1) :
    ∃ φ : Torus d → ℝ, Continuous φ ∧ (∀ x, |φ x| ≤ Λ) ∧ Torus.IsLipschitz Λ φ ∧
      coeffOf φ = multiDerivCoeff β (coeffOf μ) := by
  have hμ' : Torus.IsCk ((m + 3 : ℕ) : WithTop ℕ∞) μ := by exact_mod_cast hμ
  obtain ⟨φ, h1, h2, h3⟩ := derivFn μ (∑ i, β i) (m + 3) β rfl (by omega) hμ'
  have h1'' : Torus.IsCk 1 φ := h1.of_le (by
    have : (1 : ℕ) ≤ m + 3 - ∑ i, β i := by omega
    exact_mod_cast this)
  have hb : Torus.cbNorm (m + 3 - ∑ i, β i) φ ≤ Λ := h2.trans hΛ
  refine ⟨φ, continuous_of_lift' h1''.continuous, fun x => (abs_le_cbNorm h1 x).trans hb, ?_, h3⟩
  refine isLipschitz_mono (isLipschitz_of_cbNorm h1'') ?_
  exact (cbNorm_mono' (by omega) φ).trans hb

/-- Lower-order (order `θ - 1`) commutator term after integration by parts, items (iv), (vi). -/
theorem commS_term_bound (hd : 1 ≤ d) (s : ℝ) (hsd : s ≤ d) (m : ℕ) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Torus d → ℝ), Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (α β : Fin d → ℕ), ∑ i, α i ≤ m → β ∈ leibnizSet α → β ≠ 0 → ∀ (i j : Fin d) (n : ℕ)
        (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        ‖∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) * (Ssym d s i k *
          mulCoeff (derivCoeff j (multiDerivCoeff β (coeffOf μ))) (multiDerivCoeff (α - β) F) k)‖ ≤
          C * hsNormSq m F := by
  set σ' : ℝ := max (s + 1 - d) 0 with hσ'
  have hσ0 : 0 ≤ σ' := le_max_right _ _
  have hσ1 : σ' ≤ 1 := max_le (by linarith) zero_le_one
  obtain ⟨C₁, hC₁0, hC₁⟩ := prod_hs_bound hd σ' hσ0 hσ1
  set Kc : ℝ := |Λ| + |Λ| * Real.sqrt d with hKc
  refine ⟨|rieszConst d s| * ((1 + C₁ * Kc ^ 2) / 2), by positivity, ?_⟩
  intro μ hμ hΛ α β hα hβ hβ0 i j n F hF hFt
  have hsub := sum_sub_succ_le hβ hβ0
  have hβα : ∑ i, β i ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => mem_leibnizSet.mp hβ i
  have hsj : ∑ i, (β + Pi.single j 1 : Fin d → ℕ) i = ∑ i, β i + 1 := by
    simp [Finset.sum_add_distrib]
  obtain ⟨φ, hφc, hφb, hφL, hφ⟩ := derivFn_bd hμ hΛ (β + Pi.single j 1) (by omega)
  have hcoef : derivCoeff j (multiDerivCoeff β (coeffOf μ)) = coeffOf φ := by
    rw [hφ, derivCoeff_eq_multi, ← multiDerivCoeff_add, add_comm]
  rw [hcoef]
  set f := multiDerivCoeff (α - β) F with hf
  have hfr : IsRealCoeff f := isRealCoeff_multiDerivCoeff hF _
  have hft : IsTrigPoly n f := isTrigPoly_multiDerivCoeff hFt _
  have hΛ0 : 0 ≤ Λ := (cbNorm_nonneg' _ μ).trans hΛ
  have hLΛ : |Λ| = Λ := abs_of_nonneg hΛ0
  obtain ⟨hmem, hU⟩ := hC₁ Λ Λ φ hφL hφb n f hfr hft
  set N := hsNormSq m F with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  have hm1 : m = (m - 1) + 1 := by omega
  have hf1 : hsNormSq σ' f ≤ N := by
    refine (hsNormSq_mono_trig hft hσ1).trans ?_
    have h := hsNormSq_one_multiDeriv_le (α - β) (m - 1) (by omega) F hFt
    have e : (((m - 1 + 1 : ℕ)) : ℝ) = (m : ℝ) := by rw [← hm1]
    rw [e] at h
    exact h
  have hB : ∑ k ∈ boxFin d n, sobWeight σ' k * ‖mulCoeff (coeffOf φ) f k‖ ^ 2 ≤
      C₁ * Kc ^ 2 * N := by
    refine (hmem.sum_le_tsum _ (fun k _ => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _))).trans ?_
    refine hU.trans ?_
    have e : (Λ + |Λ| * Real.sqrt d) ^ 2 = Kc ^ 2 := by rw [hKc, hLΛ]
    rw [e]
    gcongr
  have hA : ∑ k ∈ boxFin d n, ‖multiDerivCoeff α F k‖ ^ 2 ≤ N :=
    sum_box_multiDeriv_le α m hα F hFt _
  have := Spair_bound' s i (multiDerivCoeff α F) (mulCoeff (coeffOf φ) f) N (C₁ * Kc ^ 2 * N)
    hN0 (by positivity) hA hB
  refine this.trans ?_
  have : |rieszConst d s| * ((N + C₁ * Kc ^ 2 * N) / 2) =
      |rieszConst d s| * ((1 + C₁ * Kc ^ 2) / 2) * N := by ring
  rw [this]

/-- Regime R2c, crude route (`θ ≤ 1`): the commutator term before integration by parts. -/
theorem commCrude_term_bound (s : ℝ) (hs : s ≤ (d : ℝ) - 1) (m : ℕ) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Torus d → ℝ), Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (α β : Fin d → ℕ), ∑ i, α i ≤ m → β ∈ leibnizSet α → β ≠ 0 → ∀ (i j : Fin d) (n : ℕ)
        (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        ‖∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) * (Ssym d s i k *
          mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖ ≤
          C * hsNormSq m F := by
  refine ⟨|rieszConst d s| * ((1 + Λ ^ 2) / 2), by positivity, ?_⟩
  intro μ hμ hΛ α β hα hβ hβ0 i j n F hF hFt
  have hsub := sum_sub_succ_le hβ hβ0
  have hβα : ∑ i, β i ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => mem_leibnizSet.mp hβ i
  obtain ⟨φ, hφc, hφb, -, hφ⟩ := derivFn_bd hμ hΛ β (by omega)
  rw [← hφ]
  set g := multiDerivCoeff (α - β) (derivCoeff j F) with hg
  have hge : g = multiDerivCoeff (α - β + Pi.single j 1) F := multiDerivCoeff_comm_single _ _ _
  have hgt : IsTrigPoly n g := by
    rw [hg, derivCoeff_eq_multi]
    exact isTrigPoly_multiDerivCoeff (isTrigPoly_multiDerivCoeff hFt _) _
  have hsj : ∑ i, (α - β + Pi.single j 1 : Fin d → ℕ) i = ∑ i, (α - β) i + 1 := by
    simp [Finset.sum_add_distrib]
  set N := hsNormSq m F with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  have hΛ0 : 0 ≤ Λ := (cbNorm_nonneg' _ μ).trans hΛ
  have hA : ∑ k ∈ boxFin d n, ‖multiDerivCoeff α F k‖ ^ 2 ≤ N :=
    sum_box_multiDeriv_le α m hα F hFt _
  have hmax : max (s + 1 - d) 0 = 0 := max_eq_right (by linarith)
  have hB : ∑ k ∈ boxFin d n, sobWeight (max (s + 1 - d) 0) k *
      ‖mulCoeff (coeffOf φ) g k‖ ^ 2 ≤ Λ ^ 2 * N := by
    simp_rw [hmax, sobWeight_zeroE, one_mul]
    refine (l2_mul_le φ hφc Λ hφb n g hgt _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [hge]
    exact sum_box_multiDeriv_le _ m (by omega) F hFt _
  have := Spair_bound' s i (multiDerivCoeff α F) (mulCoeff (coeffOf φ) g) N (Λ ^ 2 * N)
    hN0 (by positivity) hA hB
  refine this.trans ?_
  have : |rieszConst d s| * ((N + Λ ^ 2 * N) / 2) =
      |rieszConst d s| * ((1 + Λ ^ 2) / 2) * N := by ring
  rw [this]

end HRS.PDE.R2Aux
