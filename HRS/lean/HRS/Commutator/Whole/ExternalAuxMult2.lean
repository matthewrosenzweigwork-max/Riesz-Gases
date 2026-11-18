import HRS.Commutator.Whole.ExternalAuxMult

/-!
# X-MULT auxiliary (2): the dyadic kernel lemma

`cmxMY_LP`: a family `θ_j` of smooth functions supported in `B̄(0,2)` with uniformly bounded
derivatives gives an integrable kernel `K = ∑_j 2^{j(d-γ)} 𝓕⁻θ_j(2^j ·)` whose Fourier transform is
`∑_j 2^{-jγ} θ_j(2^{-j} ξ)`, with rapid decay at infinity and the bound `|x|^{γ-d}` near the origin.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- The dyadic cutoff `ρ = χ - χ(2 ·)`. -/
def cmxMY_rho (η : Euc d) : ℝ := chi η - chi ((2 : ℝ) • η)

lemma cmxMY_rho_contDiff : ContDiff ℝ ∞ (cmxMY_rho : Euc d → ℝ) := by
  unfold cmxMY_rho
  exact cmxFB_chi_contDiff.sub (cmxFB_chi_contDiff.comp (contDiff_const_smul _))

lemma cmxMY_rho_eq_zero_of_le {η : Euc d} (h : ‖η‖ ≤ 1 / 2) : cmxMY_rho η = 0 := by
  unfold cmxMY_rho
  have h1 : chi η = 1 := cmxFB_chi_one (by linarith)
  have h2 : chi ((2 : ℝ) • η) = 1 := cmxFB_chi_one (by
    rw [norm_smul]; simp; linarith)
  rw [h1, h2]; ring

lemma cmxMY_rho_eq_zero_of_ge {η : Euc d} (h : 2 ≤ ‖η‖) : cmxMY_rho η = 0 := by
  unfold cmxMY_rho
  have h1 : chi η = 0 := cmxFB_chi_zero h
  have h2 : chi ((2 : ℝ) • η) = 0 := cmxFB_chi_zero (by
    rw [norm_smul]; simp; linarith)
  rw [h1, h2]; ring

/-- Telescoping: `∑_{j ≤ J} ρ(2^{-j} ξ) = χ(2^{-J} ξ) - χ(2ξ)`. -/
lemma cmxMY_rho_sum (ξ : Euc d) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) =
      chi (((2 : ℝ) ^ J)⁻¹ • ξ) - chi ((2 : ℝ) • ξ) := by
  induction J with
  | zero => simp [cmxMY_rho]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold cmxMY_rho
    have : (2 : ℝ) • (((2 : ℝ) ^ (J + 1))⁻¹ • ξ) = ((2 : ℝ) ^ J)⁻¹ • ξ := by
      rw [smul_smul, pow_succ]
      congr 1
      field_simp
    rw [this]; ring

/-- For `|ξ| ≥ 1` the partition of unity sums to one (eventually). -/
lemma cmxMY_rho_sum_eq_one {ξ : Euc d} (hξ : 1 ≤ ‖ξ‖) :
    HasSum (fun j : ℕ => cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ)) 1 := by
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 2 * ‖ξ‖ < (2 : ℝ) ^ J := pow_unbounded_of_one_lt _ (by norm_num)
  have hzero : ∀ j ∉ Finset.range (J + 1), cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) = 0 := by
    intro j hj
    have hj' : J + 1 ≤ j := by simpa using hj
    apply cmxMY_rho_eq_zero_of_le
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ J * 2 ≤ 2 ^ j := by
      rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) hj'
    nlinarith
  have hs : HasSum (fun j : ℕ => cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ))
      (∑ j ∈ Finset.range (J + 1), cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ)) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hval : ∑ j ∈ Finset.range (J + 1), cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) = 1 := by
    rw [cmxMY_rho_sum]
    have h1 : chi (((2 : ℝ) ^ J)⁻¹ • ξ) = 1 := by
      apply cmxFB_chi_one
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity)]
      linarith
    have h2 : chi ((2 : ℝ) • ξ) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul]; simp; linarith
    rw [h1, h2]; ring
  rwa [hval] at hs

/-- a smooth function supported in `B̄(0,2)` has bounded derivatives -/
lemma cmxMY_bdd_deriv (θ : Euc d → ℂ) (hθ : ContDiff ℝ ∞ θ) (hs : ∀ η : Euc d, 2 < ‖η‖ → θ η = 0)
    (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ η, ‖iteratedFDeriv ℝ n θ η‖ ≤ B := by
  have hcs : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) 2) ?_
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  have h1 : Continuous (iteratedFDeriv ℝ n θ) := hθ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have h2 : HasCompactSupport (iteratedFDeriv ℝ n θ) := hcs.iteratedFDeriv n
  obtain ⟨C, hC⟩ := (h1.norm.bounded_above_of_compact_support h2.norm)
  exact ⟨max C 0, le_max_right _ _, fun η => by simpa using (hC η).trans (le_max_left C 0)⟩

/-- uniform boundedness of the derivatives of the family -/
lemma cmxMY_uniform_bdd (θ : ℕ → Euc d → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0)
    (hB : ∃ j₀ : ℕ, ∀ n : ℕ, ∃ B : ℝ, ∀ j ≥ j₀, ∀ η, ‖iteratedFDeriv ℝ n (θ j) η‖ ≤ B)
    (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ j η, ‖iteratedFDeriv ℝ n (θ j) η‖ ≤ B := by
  obtain ⟨j₀, hj₀⟩ := hB
  obtain ⟨B₀, hB₀⟩ := hj₀ n
  choose b hb0 hb using fun j => cmxMY_bdd_deriv (θ j) (hθ j) (hs j) n
  refine ⟨|B₀| + ∑ j ∈ Finset.range j₀, b j, by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range j₀) => hb0 j)
    positivity, fun j η => ?_⟩
  by_cases hj : j₀ ≤ j
  · have := hB₀ j hj η
    have h2 : 0 ≤ ∑ j ∈ Finset.range j₀, b j := Finset.sum_nonneg (fun j _ => hb0 j)
    linarith [le_abs_self B₀]
  · have hj' : j ∈ Finset.range j₀ := by simpa using hj
    have := hb j η
    have h2 : b j ≤ ∑ j ∈ Finset.range j₀, b j :=
      Finset.single_le_sum (f := b) (fun j _ => hb0 j) hj'
    linarith [abs_nonneg B₀]

lemma cmxMY_one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  rcases le_total t 1 with h | h
  · have h1 : (1 + t) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    have : (0:ℝ) ≤ t ^ N := by positivity
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) N]
  · have h1 : (1 + t) ^ N ≤ (2 * t) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    have : (0:ℝ) ≤ 2 ^ N := by positivity
    nlinarith

/-- uniform decay of the kernels `Θ_j = 𝓕⁻θ_j` -/
lemma cmxMY_decay_unif (θ : ℕ → Euc d → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0)
    (hB : ∃ j₀ : ℕ, ∀ n : ℕ, ∃ B : ℝ, ∀ j ≥ j₀, ∀ η, ‖iteratedFDeriv ℝ n (θ j) η‖ ≤ B)
    (N : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ (j : ℕ) (y : Euc d), ‖𝓕⁻ (θ j) y‖ * (1 + ‖y‖) ^ N ≤ M := by
  choose B hB0 hBd using cmxMY_uniform_bdd θ hθ hs hB
  set V : ℝ := (volume (closedBall (0 : Euc d) 2)).toReal with hV
  have hC : ∀ (n : ℕ) (j : ℕ) (y : Euc d), ‖y‖ ^ n * ‖𝓕⁻ (θ j) y‖ ≤ (2 * (n : ℝ) + 2) ^ n *
      ∑ i ∈ Finset.range (n + 1), B i * V := fun n j y =>
    cmxMY_decay (θ j) (hθ j) (hs j) n B (fun i _ η => hBd i j η) y
  set C : ℕ → ℝ := fun n => (2 * (n : ℝ) + 2) ^ n * ∑ i ∈ Finset.range (n + 1), B i * V with hCdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hC0 : ∀ n, 0 ≤ C n := fun n =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) hV0)
  refine ⟨2 ^ N * (C 0 + C N), mul_nonneg (by positivity) (add_nonneg (hC0 0) (hC0 N)),
    fun j y => ?_⟩
  have h0 : ‖𝓕⁻ (θ j) y‖ ≤ C 0 := by simpa [hCdef] using hC 0 j y
  have hN : ‖y‖ ^ N * ‖𝓕⁻ (θ j) y‖ ≤ C N := hC N j y
  have := cmxMY_one_add_pow_le ‖y‖ (norm_nonneg y) N
  calc ‖𝓕⁻ (θ j) y‖ * (1 + ‖y‖) ^ N ≤ ‖𝓕⁻ (θ j) y‖ * (2 ^ N * (1 + ‖y‖ ^ N)) := by gcongr
    _ = 2 ^ N * (‖𝓕⁻ (θ j) y‖ + ‖y‖ ^ N * ‖𝓕⁻ (θ j) y‖) := by ring
    _ ≤ 2 ^ N * (C 0 + C N) := by gcongr

lemma cmxMY_schwartz (θ : Euc d → ℂ) (hθ : ContDiff ℝ ∞ θ) (hs : ∀ η : Euc d, 2 < ‖η‖ → θ η = 0) :
    Continuous (𝓕⁻ θ) ∧ Integrable (𝓕⁻ θ) ∧ 𝓕 (𝓕⁻ θ) = θ := by
  have hcs : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) 2) ?_
    intro η hη
    by_contra h
    exact hη (hs η (by simpa using h))
  set S : SchwartzMap (Euc d) ℂ := hcs.toSchwartzMap hθ with hS
  have hSθ : (⇑S : Euc d → ℂ) = θ := rfl
  set T : SchwartzMap (Euc d) ℂ := 𝓕⁻ S with hT
  have h1 : (⇑T : Euc d → ℂ) = 𝓕⁻ θ := by
    rw [← hSθ]; exact SchwartzMap.fourierInv_coe S
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; exact T.continuous
  · rw [← h1]; exact T.integrable
  · have h : (𝓕 T : SchwartzMap (Euc d) ℂ) = S := FourierTransform.fourier_fourierInv_eq S
    have h2 : (⇑(𝓕 T : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 (⇑T) := SchwartzMap.fourier_coe T
    rw [← h1, ← h2]
    exact congrArg (⇑) h

lemma cmxMY_fourier_real_smul (g : Euc d → ℂ) (r : ℝ) (ξ : Euc d) :
    𝓕 (fun x => r • g x) ξ = r • 𝓕 g ξ := by
  simp only [Real.fourier_eq]
  rw [← integral_smul]
  congr 1
  ext x
  rw [smul_comm]


/-- the `j`-th dyadic kernel -/
def cmxMY_Kj (γ : ℝ) (θ : ℕ → Euc d → ℂ) (j : ℕ) (x : Euc d) : ℂ :=
  ((((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) : ℝ)) • 𝓕⁻ (θ j) (((2 : ℝ) ^ j) • x)

lemma cmxMY_Kj_continuous {γ : ℝ} (θ : ℕ → Euc d → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0) (j : ℕ) : Continuous (cmxMY_Kj γ θ j) := by
  unfold cmxMY_Kj
  exact ((cmxMY_schwartz (θ j) (hθ j) (hs j)).1.comp (continuous_const_smul ((2 : ℝ) ^ j))).const_smul (((2 : ℝ) ^ j) ^ ((d : ℝ) - γ))

lemma cmxMY_Kj_norm {γ : ℝ} (θ : ℕ → Euc d → ℂ) (j : ℕ) (x : Euc d) :
    ‖cmxMY_Kj γ θ j x‖ = ((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) * ‖𝓕⁻ (θ j) (((2 : ℝ) ^ j) • x)‖ := by
  unfold cmxMY_Kj
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]

lemma cmxMY_Kj_bound {γ : ℝ} (θ : ℕ → Euc d → ℂ) {N : ℕ} {M : ℝ}
    (hM : ∀ (j : ℕ) (y : Euc d), ‖𝓕⁻ (θ j) y‖ * (1 + ‖y‖) ^ N ≤ M) (j : ℕ) (x : Euc d) :
    ‖cmxMY_Kj γ θ j x‖ ≤ M * cmxMY_term ((d : ℝ) - γ) N ‖x‖ j := by
  rw [cmxMY_Kj_norm]
  have h := hM j (((2 : ℝ) ^ j) • x)
  have hn : ‖((2 : ℝ) ^ j) • x‖ = (2 : ℝ) ^ j * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [hn] at h
  unfold cmxMY_term
  have hpos : 0 < (1 + (2 : ℝ) ^ j * ‖x‖) ^ N := by positivity
  have : ‖𝓕⁻ (θ j) (((2 : ℝ) ^ j) • x)‖ ≤ M / (1 + (2 : ℝ) ^ j * ‖x‖) ^ N := by
    rw [le_div_iff₀ hpos]; exact h
  calc ((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) * ‖𝓕⁻ (θ j) (((2 : ℝ) ^ j) • x)‖
      ≤ ((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) * (M / (1 + (2 : ℝ) ^ j * ‖x‖) ^ N) := by gcongr
    _ = _ := by ring

lemma cmxMY_Kj_integrable {γ : ℝ} (θ : ℕ → Euc d → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0) (j : ℕ) : Integrable (cmxMY_Kj γ θ j) := by
  unfold cmxMY_Kj
  exact ((cmxMY_schwartz (θ j) (hθ j) (hs j)).2.1.comp_smul (pow_ne_zero j (two_ne_zero : (2:ℝ) ≠ 0))).smul (((2 : ℝ) ^ j) ^ ((d : ℝ) - γ))

lemma cmxMY_pow_rpow (j : ℕ) (a : ℝ) : (((2 : ℝ) ^ j) ^ a) = (2 : ℝ) ^ ((j : ℝ) * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

lemma cmxMY_Kj_integral_norm_le {γ : ℝ} (θ : ℕ → Euc d → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0) {M : ℝ}
    (hM : ∀ (j : ℕ) (y : Euc d), ‖𝓕⁻ (θ j) y‖ * (1 + ‖y‖) ^ (d + 1) ≤ M) (j : ℕ) :
    ∫ x : Euc d, ‖cmxMY_Kj γ θ j x‖ ≤
      ((2 : ℝ) ^ j) ^ (-γ) * (M * ∫ y : Euc d, ((1 + ‖y‖) ^ (d + 1))⁻¹) := by
  have hg : Integrable (fun y : Euc d => ((1 + ‖y‖) ^ (d + 1))⁻¹) :=
    cmxFB_integrable_inv_pow (d + 1) (by omega)
  have hint : Integrable (fun y : Euc d => ‖𝓕⁻ (θ j) y‖) := (cmxMY_schwartz (θ j) (hθ j) (hs j)).2.1.norm
  have hle : ∫ y : Euc d, ‖𝓕⁻ (θ j) y‖ ≤ M * ∫ y : Euc d, ((1 + ‖y‖) ^ (d + 1))⁻¹ := by
    rw [← integral_const_mul]
    refine integral_mono hint (hg.const_mul M) fun y => ?_
    have h := hM j y
    have hpos : 0 < (1 + ‖y‖) ^ (d + 1) := by positivity
    simp only
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h
  have hs0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have e1 : ∫ x : Euc d, ‖cmxMY_Kj γ θ j x‖ =
      ((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) * ∫ x : Euc d, ‖𝓕⁻ (θ j) (((2 : ℝ) ^ j) • x)‖ := by
    simp_rw [cmxMY_Kj_norm]
    rw [integral_const_mul]
  have e2 := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure (Euc d)))
    (fun y : Euc d => ‖𝓕⁻ (θ j) y‖) ((2 : ℝ) ^ j)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at e2
  rw [e1, e2]
  have e3 : ((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) * |(((2 : ℝ) ^ j) ^ d)⁻¹| = ((2 : ℝ) ^ j) ^ (-γ) := by
    rw [abs_of_pos (by positivity), Real.rpow_sub hs0, Real.rpow_neg hs0.le, Real.rpow_natCast]
    field_simp
  calc ((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) *
        (|(((2 : ℝ) ^ j) ^ d)⁻¹| * ∫ y : Euc d, ‖𝓕⁻ (θ j) y‖)
      = (((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) * |(((2 : ℝ) ^ j) ^ d)⁻¹|) * ∫ y : Euc d, ‖𝓕⁻ (θ j) y‖ := by ring
    _ = ((2 : ℝ) ^ j) ^ (-γ) * ∫ y : Euc d, ‖𝓕⁻ (θ j) y‖ := by rw [e3]
    _ ≤ _ := by gcongr

lemma cmxMY_Kj_fourier {γ : ℝ} (θ : ℕ → Euc d → ℂ) (hθ : ∀ j, ContDiff ℝ ∞ (θ j))
    (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0) (j : ℕ) (ξ : Euc d) :
    𝓕 (cmxMY_Kj γ θ j) ξ = (((2 : ℝ) ^ j) ^ (-γ) : ℝ) • θ j (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  have hs0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have h1 : cmxMY_Kj γ θ j = fun x => (((2 : ℝ) ^ j) ^ ((d : ℝ) - γ) : ℝ) •
      (fun y => 𝓕⁻ (θ j) y) (((2 : ℝ) ^ j) • x) := rfl
  rw [h1, cmxMY_fourier_real_smul (fun x => (fun y => 𝓕⁻ (θ j) y) (((2 : ℝ) ^ j) • x)),
    cmxMY_fourier_comp_smul _ hs0, (cmxMY_schwartz (θ j) (hθ j) (hs j)).2.2]
  rw [smul_smul]
  congr 1
  rw [Real.rpow_sub hs0, Real.rpow_neg hs0.le, Real.rpow_natCast]
  field_simp

theorem cmxMY_LP (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (θ : ℕ → Euc d → ℂ)
    (hθ : ∀ j, ContDiff ℝ ∞ (θ j)) (hs : ∀ j (η : Euc d), 2 < ‖η‖ → θ j η = 0)
    (hB : ∃ j₀ : ℕ, ∀ n : ℕ, ∃ B : ℝ, ∀ j ≥ j₀, ∀ η, ‖iteratedFDeriv ℝ n (θ j) η‖ ≤ B) :
    ∃ K : Euc d → ℂ, Integrable K ∧
      (∀ ξ : Euc d, HasSum (fun j : ℕ => (((2 : ℝ) ^ j) ^ (-γ) : ℝ) • θ j (((2 : ℝ) ^ j)⁻¹ • ξ))
        (𝓕 K ξ)) ∧
      (∀ m : ℕ, ∃ C : ℝ, ∀ x : Euc d, 1 ≤ ‖x‖ → ‖K x‖ ≤ C * ‖x‖ ^ (-(m : ℝ))) ∧
      (γ < d → ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → ‖K x‖ ≤ C * ‖x‖ ^ (γ - d)) := by
  choose M hM0 hM using fun N => cmxMY_decay_unif θ hθ hs hB N
  set a : ℝ := (d : ℝ) - γ with ha
  set N₀ : ℕ := ⌈a⌉₊ + 1 with hN₀
  have haN : a + 1 ≤ N₀ := by
    have := Nat.le_ceil a
    rw [hN₀]; push_cast; linarith
  have hbound : ∀ N : ℕ, a + 1 ≤ N → ∀ j x, ‖cmxMY_Kj γ θ j x‖ ≤ M N * cmxMY_term a N ‖x‖ j :=
    fun N _ j x => cmxMY_Kj_bound θ (hM N) j x
  have hsumm : ∀ x : Euc d, x ≠ 0 → Summable (fun j => ‖cmxMY_Kj γ θ j x‖) := fun x hx =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hbound N₀ haN j x)
      ((cmxMY_term_summable haN (norm_pos_iff.2 hx)).mul_left _)
  set K : Euc d → ℂ := fun x => ∑' j, cmxMY_Kj γ θ j x with hK
  have hHas : ∀ x : Euc d, x ≠ 0 → HasSum (fun j => cmxMY_Kj γ θ j x) (K x) := fun x hx =>
    (hsumm x hx).of_norm.hasSum
  have hcont := cmxMY_Kj_continuous (γ := γ) θ hθ hs
  have hint := cmxMY_Kj_integrable (γ := γ) θ hθ hs
  -- far field
  have far : ∀ m : ℕ, ∃ C : ℝ, ∀ x : Euc d, 1 ≤ ‖x‖ → ‖K x‖ ≤ C * ‖x‖ ^ (-(m : ℝ)) := by
    intro m
    refine ⟨2 * M (m + N₀), fun x hx => ?_⟩
    have hx0 : 0 < ‖x‖ := by linarith
    have hxne : x ≠ 0 := norm_pos_iff.1 hx0
    have hN : a + 1 ≤ ((m + N₀ : ℕ) : ℝ) := by
      push_cast; have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hsg : Summable fun j : ℕ => M (m + N₀) * ((1 / 2 : ℝ) ^ j * (‖x‖ ^ (m + N₀))⁻¹) :=
      ((summable_geometric_two).mul_right _).mul_left _
    calc ‖K x‖ ≤ ∑' j, ‖cmxMY_Kj γ θ j x‖ := norm_tsum_le_tsum_norm (hsumm x hxne)
      _ ≤ ∑' j : ℕ, M (m + N₀) * ((1 / 2 : ℝ) ^ j * (‖x‖ ^ (m + N₀))⁻¹) := by
          refine (hsumm x hxne).tsum_le_tsum (fun j => ?_) hsg
          exact (hbound (m + N₀) hN j x).trans
            (mul_le_mul_of_nonneg_left (cmxMY_term_geom hN hx0 j) (hM0 _))
      _ = 2 * M (m + N₀) * (‖x‖ ^ (m + N₀))⁻¹ := by
          rw [tsum_mul_left, tsum_mul_right, tsum_geometric_two]; ring
      _ ≤ 2 * M (m + N₀) * ‖x‖ ^ (-(m : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by have := hM0 (m + N₀); positivity)
          rw [Real.rpow_neg hx0.le, Real.rpow_natCast]
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hx (by omega)
  -- near field
  have near : γ < d → ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → ‖K x‖ ≤ C * ‖x‖ ^ (γ - d) := by
    intro hγd
    have ha0 : 0 < a := by rw [ha]; linarith
    refine ⟨M N₀ * ((2 : ℝ) ^ a * (1 / ((2 : ℝ) ^ a - 1) + 2)), fun x hx hx1 => ?_⟩
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hsg : Summable fun j : ℕ => M N₀ * cmxMY_term a N₀ ‖x‖ j :=
      (cmxMY_term_summable haN hx0).mul_left _
    calc ‖K x‖ ≤ ∑' j, ‖cmxMY_Kj γ θ j x‖ := norm_tsum_le_tsum_norm (hsumm x hx)
      _ ≤ ∑' j : ℕ, M N₀ * cmxMY_term a N₀ ‖x‖ j :=
          (hsumm x hx).tsum_le_tsum (fun j => hbound N₀ haN j x) hsg
      _ = M N₀ * ∑' j, cmxMY_term a N₀ ‖x‖ j := tsum_mul_left
      _ ≤ M N₀ * (((2 : ℝ) ^ a * (1 / ((2 : ℝ) ^ a - 1) + 2)) * ‖x‖ ^ (-a)) := by
          gcongr
          · exact hM0 _
          · exact cmxMY_term_tsum_near ha0 haN hx0 hx1
      _ = _ := by
          have : -a = γ - d := by rw [ha]; ring
          rw [this]; ring
  -- summability of the `L¹` norms
  set I : ℝ := ∫ y : Euc d, ((1 + ‖y‖) ^ (d + 1))⁻¹ with hI
  have hcj : ∀ j : ℕ, ∫ x : Euc d, ‖cmxMY_Kj γ θ j x‖ ≤
      ((2 : ℝ) ^ j) ^ (-γ) * (M (d + 1) * I) :=
    fun j => cmxMY_Kj_integral_norm_le θ hθ hs (hM (d + 1)) j
  have hr1 : ((2 : ℝ) ^ (-γ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo : Summable fun j : ℕ => ((2 : ℝ) ^ j) ^ (-γ) * (M (d + 1) * I) := by
    have : (fun j : ℕ => ((2 : ℝ) ^ j) ^ (-γ) * (M (d + 1) * I)) =
        fun j : ℕ => ((2 : ℝ) ^ (-γ)) ^ j * (M (d + 1) * I) := by
      funext j
      rw [cmxMY_pow_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 2; ring
    rw [this]
    exact (summable_geometric_of_lt_one (by positivity) hr1).mul_right _
  have hnorm_sum : Summable fun j : ℕ => ∫ x : Euc d, ‖cmxMY_Kj γ θ j x‖ :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _) hcj hgeo
  -- integrability of `K`
  have hmeas : AEStronglyMeasurable K volume := by
    refine aestronglyMeasurable_of_tendsto_ae (f := fun n x => ∑ j ∈ Finset.range n, cmxMY_Kj γ θ j x)
      atTop (fun n => (continuous_finsetSum _ fun j _ => hcont j).aestronglyMeasurable) ?_
    filter_upwards [ae_ne_zero_euc hd] with x hx
    exact (hHas x hx).tendsto_sum_nat
  have hKint : Integrable K := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ x, ‖K x‖ₑ ≤ ∫⁻ x, ∑' j, ‖cmxMY_Kj γ θ j x‖ₑ :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ = ∑' j, ∫⁻ x, ‖cmxMY_Kj γ θ j x‖ₑ :=
          lintegral_tsum fun j => (hcont j).measurable.enorm.aemeasurable
      _ = ∑' j, ENNReal.ofReal (∫ x, ‖cmxMY_Kj γ θ j x‖) := by
          congr 1; funext j
          exact (ofReal_integral_norm_eq_lintegral_enorm (hint j)).symm
      _ = ENNReal.ofReal (∑' j, ∫ x, ‖cmxMY_Kj γ θ j x‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun x => norm_nonneg _)
            hnorm_sum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨K, hKint, ?_, far, near⟩
  -- Fourier transform
  intro ξ
  have hF : ∀ j, Integrable (fun x : Euc d => (𝐞 (-inner ℝ x ξ) : Circle) • cmxMY_Kj γ θ j x) :=
    fun j => (Real.fourierIntegral_convergent_iff ξ).2 (hint j)
  have hsum_fa : Summable fun j => ∫ x : Euc d, ‖(𝐞 (-inner ℝ x ξ) : Circle) • cmxMY_Kj γ θ j x‖ := by
    simpa [Circle.norm_smul] using hnorm_sum
  have hH := hasSum_integral_of_summable_integral_norm hF hsum_fa
  have e1 : ∀ j, ∫ x : Euc d, (𝐞 (-inner ℝ x ξ) : Circle) • cmxMY_Kj γ θ j x =
      (((2 : ℝ) ^ j) ^ (-γ) : ℝ) • θ j (((2 : ℝ) ^ j)⁻¹ • ξ) := fun j => by
    rw [← cmxMY_Kj_fourier θ hθ hs j ξ, Real.fourier_eq]
  have e2 : ∫ x : Euc d, ∑' j, (𝐞 (-inner ℝ x ξ) : Circle) • cmxMY_Kj γ θ j x = 𝓕 K ξ := by
    rw [Real.fourier_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_euc hd] with x hx
    exact ((hHas x hx).const_smul (𝐞 (-inner ℝ x ξ) : Circle)).tsum_eq
  simp_rw [e1] at hH
  rwa [e2] at hH


end HRS.Commutator.Whole
