import HRS.PDE.EnergyR2Comm

/-!
# Regime R2: the symbol `𝔪_q`, its size and the Cauchy--Schwarz inequality for the form `B_q`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

theorem rieszCoeff_nonneg' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    0 ≤ rieszCoeff d s k := by
  unfold rieszCoeff
  split_ifs with hk
  · exact le_rfl
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hconst : 0 ≤ rieszConst d s := by
      unfold rieszConst
      split_ifs with h0
      · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.Gamma_pos_of_pos (by positivity)).le
      · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h0)
        exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (Real.Gamma_pos_of_pos (by linarith)).le) (Real.Gamma_pos_of_pos (by linarith)).le
    exact mul_nonneg hconst (Real.rpow_nonneg
      (mul_nonneg (by positivity) (norm_nonneg (Lattice.toEuc k))) _)

theorem symbolK_nonneg' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q : Euc d)
    (k : Lattice d) : 0 ≤ symbolK d s q k :=
  mul_nonneg (sq_nonneg _) (rieszCoeff_nonneg' hd hs0 hsd k)

theorem quadForm_symbolK_nonneg' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (q : Euc d)
    (c : Coeff d) : 0 ≤ quadForm (symbolK d s q) c :=
  tsum_nonneg fun k => mul_nonneg (symbolK_nonneg' hd hs0 hsd q k) (sq_nonneg _)

/-- `𝔪_q(k) ≤ c ‖q‖² ⟨k⟩^θ`. -/
theorem symbolK_le (s : ℝ) (hθ : 0 ≤ s + 2 - d) (q : Euc d) (k : Lattice d) :
    |symbolK d s q k| ≤ |rieszConst d s| * ‖q‖ ^ 2 * sobWeight ((s + 2 - d) / 2) k := by
  by_cases hk : k = 0
  · subst hk
    have : symbolK d s q 0 = 0 := by simp [symbolK, rieszCoeff]
    rw [this, abs_zero]
    have := sobWeight_nonnegE ((s + 2 - d) / 2) (0 : Lattice d)
    positivity
  · have hr : 0 < rad k := lt_of_lt_of_le one_pos (one_le_rad k hk)
    have h1 : |inner ℝ q (Lattice.toEuc k)| ≤ ‖q‖ * Lattice.enorm k := abs_real_inner_le_norm _ _
    have h2 : (2 * Real.pi * inner ℝ q (Lattice.toEuc k)) ^ 2 ≤ ‖q‖ ^ 2 * rad k ^ 2 := by
      rw [← sq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have : 2 * Real.pi * |inner ℝ q (Lattice.toEuc k)| ≤ ‖q‖ * rad k := by
        unfold rad
        calc 2 * Real.pi * |inner ℝ q (Lattice.toEuc k)|
            ≤ 2 * Real.pi * (‖q‖ * Lattice.enorm k) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = _ := by ring
      calc (2 * Real.pi * |inner ℝ q (Lattice.toEuc k)|) ^ 2 ≤ (‖q‖ * rad k) ^ 2 :=
            pow_le_pow_left₀ (by positivity) this 2
        _ = _ := by ring
    have h3 := abs_rieszCoeff_le s k hk
    have h4 : rad k ^ (s - (d : ℝ) + 2) ≤ sobWeight ((s + 2 - d) / 2) k := by
      have := rad_rpow_le_sobWeight k ((s + 2 - d) / 2) (by linarith)
      have e : 2 * ((s + 2 - d) / 2) = s - (d : ℝ) + 2 := by ring
      rwa [e] at this
    have h5 : rad k ^ 2 * rad k ^ (s - (d : ℝ)) = rad k ^ (s - (d : ℝ) + 2) := by
      rw [Real.rpow_add hr, Real.rpow_two]; ring
    unfold symbolK
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc (2 * Real.pi * inner ℝ q (Lattice.toEuc k)) ^ 2 * |rieszCoeff d s k|
        ≤ (‖q‖ ^ 2 * rad k ^ 2) * (|rieszConst d s| * rad k ^ (s - (d : ℝ))) :=
          mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
      _ = |rieszConst d s| * ‖q‖ ^ 2 * (rad k ^ 2 * rad k ^ (s - (d : ℝ))) := by ring
      _ = |rieszConst d s| * ‖q‖ ^ 2 * rad k ^ (s - (d : ℝ) + 2) := by rw [h5]
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- Cauchy--Schwarz for the nonnegative symbol form (box sums). -/
theorem Kpair_bound {n : ℕ} (𝔪 : Lattice d → ℝ) (hm : ∀ k, 0 ≤ 𝔪 k) (w U : Coeff d) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hw : ∑ k ∈ boxFin d n, 𝔪 k * ‖w k‖ ^ 2 ≤ A ^ 2)
    (hU : ∑ k ∈ boxFin d n, 𝔪 k * ‖U k‖ ^ 2 ≤ B ^ 2) :
    ‖∑ k ∈ boxFin d n, conj (w k) * (((𝔪 k : ℝ) : ℂ) * U k)‖ ≤ A * B := by
  have h1 := cs_bound (boxFin d n) (fun k => ((Real.sqrt (𝔪 k) : ℝ) : ℂ) * w k)
    (fun k => ((Real.sqrt (𝔪 k) : ℝ) : ℂ) * U k) A B hA hB
    (by
      refine le_trans (le_of_eq ?_) hw
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hm k)])
    (by
      refine le_trans (le_of_eq ?_) hU
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hm k)])
  refine (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) h1)
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : ‖((Real.sqrt (𝔪 k) : ℝ) : ℂ) * w k‖ = Real.sqrt (𝔪 k) * ‖w k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have e2 : ‖((Real.sqrt (𝔪 k) : ℝ) : ℂ) * U k‖ = Real.sqrt (𝔪 k) * ‖U k‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [e1, e2, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hm k)]
  have h := Real.mul_self_sqrt (hm k)
  calc ‖w k‖ * (𝔪 k * ‖U k‖) = (Real.sqrt (𝔪 k) * Real.sqrt (𝔪 k)) * (‖w k‖ * ‖U k‖) := by
        rw [h]; ring
    _ = _ := by ring

/-- The first conjunct of the R2 bounds: the weighted dissipation is finite. -/
theorem summable_sqrtK (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hθ : 0 ≤ s + 2 - d)
    (_hθ2 : s + 2 - d ≤ 2) (μ : Torus d → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ2 : Torus.IsCk 2 μ)
    (q : Euc d) {n : ℕ} (w : Coeff d) (hw : IsRealCoeff w) (hwt : IsTrigPoly n w) :
    Summable fun k => symbolK d s q k *
      ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w k‖ ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := prod_hs_bound hd ((s + 2 - d) / 2) (by linarith) (by linarith)
  have hL := sqrt_isLipschitz (cbNorm_nonneg' 2 μ) hμ0 (isC11_of_cbNorm hμ2)
  have hbd : ∀ x, |Real.sqrt (μ x)| ≤ Real.sqrt (Torus.cbNorm 2 μ) := by
    intro x
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (abs_le_cbNorm hμ2 x))
  obtain ⟨hmem, -⟩ := hC₁ _ _ _ hL hbd n w hw hwt
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (symbolK_nonneg' hd hs0 hsd q k)
    (sq_nonneg _)) (fun k => ?_) (hmem.mul_left (|rieszConst d s| * ‖q‖ ^ 2))
  have := symbolK_le s hθ q k
  calc symbolK d s q k * ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w k‖ ^ 2
      ≤ (|rieszConst d s| * ‖q‖ ^ 2 * sobWeight ((s + 2 - d) / 2) k) *
          ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans this) (sq_nonneg _)
    _ = _ := by ring

/-- The commutator `ρ`-term in `B_q` (order `θ`): `B_q(∂^βμ ∂^{α-β}F) ≤ C ‖F‖²_{H^m}`. -/
theorem Kcomm_term_bound (hd : 1 ≤ d) (s : ℝ) (hθ : 0 ≤ s + 2 - d) (hθ2 : s + 2 - d ≤ 2)
    (m : ℕ) (Λ : ℝ) :
    ∃ Cρ : ℝ, 0 ≤ Cρ ∧ ∀ (q : Euc d), ‖q‖ ≤ 1 → ∀ (μ : Torus d → ℝ), Torus.IsCk (m + 3) μ →
      Torus.cbNorm (m + 3) μ ≤ Λ → ∀ (α β : Fin d → ℕ), ∑ i, α i ≤ m → β ∈ leibnizSet α →
      β ≠ 0 → ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        ∑ k ∈ boxFin d n, symbolK d s q k *
          ‖mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) F) k‖ ^ 2 ≤
          Cρ * hsNormSq m F := by
  set σ : ℝ := (s + 2 - d) / 2 with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσ]; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := prod_hs_bound hd σ hσ0 hσ1
  set Kc : ℝ := |Λ| + |Λ| * Real.sqrt d with hKc
  refine ⟨|rieszConst d s| * (C₁ * Kc ^ 2), by positivity, ?_⟩
  intro q hq μ hμ hΛ α β hα hβ hβ0 n F hF hFt
  have hsub := sum_sub_succ_le hβ hβ0
  have hβα : ∑ i, β i ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => mem_leibnizSet.mp hβ i
  obtain ⟨φ, hφc, hφb, hφL, hφ⟩ := derivFn_bd hμ hΛ β (by omega)
  rw [← hφ]
  set f := multiDerivCoeff (α - β) F with hf
  have hfr : IsRealCoeff f := isRealCoeff_multiDerivCoeff hF _
  have hft : IsTrigPoly n f := isTrigPoly_multiDerivCoeff hFt _
  have hΛ0 : 0 ≤ Λ := (cbNorm_nonneg' _ μ).trans hΛ
  have hLΛ : |Λ| = Λ := abs_of_nonneg hΛ0
  obtain ⟨hmem, hU⟩ := hC₁ Λ Λ φ hφL hφb n f hfr hft
  set N := hsNormSq m F with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  have hm1 : m = (m - 1) + 1 := by omega
  have hf1 : hsNormSq σ f ≤ N := by
    refine (hsNormSq_mono_trig hft hσ1).trans ?_
    have h := hsNormSq_one_multiDeriv_le (α - β) (m - 1) (by omega) F hFt
    have e : (((m - 1 + 1 : ℕ)) : ℝ) = (m : ℝ) := by rw [← hm1]
    rw [e] at h
    exact h
  have hq2 : ‖q‖ ^ 2 ≤ 1 := by
    have := norm_nonneg q
    nlinarith
  have hc0 : 0 ≤ |rieszConst d s| := abs_nonneg _
  calc ∑ k ∈ boxFin d n, symbolK d s q k * ‖mulCoeff (coeffOf φ) f k‖ ^ 2
      ≤ ∑ k ∈ boxFin d n, |rieszConst d s| * (sobWeight σ k * ‖mulCoeff (coeffOf φ) f k‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := (le_abs_self _).trans (symbolK_le s hθ q k)
        have h2 : |rieszConst d s| * ‖q‖ ^ 2 * sobWeight σ k ≤ |rieszConst d s| * sobWeight σ k := by
          have := sobWeight_nonnegE σ k
          have h3 : |rieszConst d s| * ‖q‖ ^ 2 ≤ |rieszConst d s| := by
            calc _ ≤ |rieszConst d s| * 1 := mul_le_mul_of_nonneg_left hq2 hc0
              _ = _ := mul_one _
          exact mul_le_mul_of_nonneg_right h3 this
        calc symbolK d s q k * ‖mulCoeff (coeffOf φ) f k‖ ^ 2
            ≤ (|rieszConst d s| * sobWeight σ k) * ‖mulCoeff (coeffOf φ) f k‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg _)
          _ = _ := by ring
    _ = |rieszConst d s| * ∑ k ∈ boxFin d n, sobWeight σ k * ‖mulCoeff (coeffOf φ) f k‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ |rieszConst d s| * hsNormSq σ (mulCoeff (coeffOf φ) f) :=
        mul_le_mul_of_nonneg_left (hmem.sum_le_tsum _ (fun k _ =>
          mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _))) hc0
    _ ≤ |rieszConst d s| * (C₁ * Kc ^ 2 * N) := by
        refine mul_le_mul_of_nonneg_left (hU.trans ?_) hc0
        have e : (Λ + |Λ| * Real.sqrt d) ^ 2 = Kc ^ 2 := by rw [hKc, hLΛ]
        rw [e]
        exact mul_le_mul_of_nonneg_left hf1 (by positivity)
    _ = |rieszConst d s| * (C₁ * Kc ^ 2) * N := by ring

end HRS.PDE.R2Aux
