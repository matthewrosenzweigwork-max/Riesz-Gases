import HRS.MS.CzMikAux1

/-!
# MIK-1, part 2: the dyadic pieces `U_k` of a Mikhlin multiplier, their sum, and the uniform decay constant

For a smooth-off-zero symbol `m` and a Schwartz function `u`, `mik1_U m hm u k` is the Fourier multiplier
with symbol `m(ξ) ρ(2^{-k} ξ)` applied to `u`.  `mik1_U_eq_cv`: it is `dK (mik1_Th m) k ⋆ (symK ρ̃ k ⋆ u)`;
`mik1_U_rep`: it is reproduced by `symK ρ̃ k`; `mik1_sum_U`: if `𝓕 R = m 𝓕 u` and `𝓕 u` is supported in an
annulus then `R` is a finite sum of pieces (no homogeneity of `m` is used: `Θ_k(2^{-k}ξ) = m(ξ) ρ(2^{-k}ξ)`);
`mik1_dK_dec_unif`: the decay constant of `dK Θ j` is `C₀ B` with `C₀` independent of the family
(this is `dK_dec` of `XLIAux10` with its constant made explicit).
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.CZ.Mik
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS HRS.Commutator.Whole.XBB
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma mik1_Th_cs (m : 𝔼 → ℂ) (k : ℤ) : HasCompactSupport (mik1_Th m k) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) 2) ?_
  intro η hη
  by_contra hc
  exact hη (mik1_Th_supp m k (by simpa using hc))

lemma mik1_Th_apply (m : 𝔼 → ℂ) (k : ℤ) (ξ : 𝔼) :
    mik1_Th m k (((2 : ℝ) ^ k)⁻¹ • ξ) = m ξ * rho (((2 : ℝ) ^ k)⁻¹ • ξ) := by
  have hc : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  unfold mik1_Th
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- the `k`-th dyadic piece of the multiplier `m` applied to `u` -/
def mik1_U (m : 𝔼 → ℂ) (hm : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) (u : 𝓢(𝔼, ℂ)) (k : ℤ) :
    𝓢(𝔼, ℂ) :=
  mulS (fun ξ => mik1_Th m k (((2 : ℝ) ^ k)⁻¹ • ξ))
    (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k) u

lemma mik1_U_fourier (m : 𝔼 → ℂ) (hm : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) (u : 𝓢(𝔼, ℂ)) (k : ℤ)
    (ξ : 𝔼) : 𝓕 (⇑(mik1_U m hm u k)) ξ = m ξ * rho (((2 : ℝ) ^ k)⁻¹ • ξ) * 𝓕 (⇑u) ξ := by
  unfold mik1_U
  rw [fourier_mulS, mik1_Th_apply]

lemma mik1_U_eq_cv (m : 𝔼 → ℂ) (hm : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) (u : 𝓢(𝔼, ℂ)) (k : ℤ)
    (x : 𝔼) :
    mik1_U m hm u k x = cv (dK (mik1_Th m) k) (cv (symK (rhoT : 𝔼 → ℂ) k) ⇑u) x := by
  have hdK : dK (mik1_Th m) k = symK (mik1_Th m k) k := rfl
  rw [hdK]
  rw [cv_symK_eq_mulS rhoT_contDiff rhoT_cs u k]
  rw [cv_symK_eq_mulS (mik1_Th_contDiff hm k) (mik1_Th_cs m k) _ k]
  rw [mulS_mulS _ _ (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k)
    (temperate_symbol rhoT_contDiff rhoT_cs k)
    ((temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k).mul
      (temperate_symbol rhoT_contDiff rhoT_cs k))]
  unfold mik1_U
  have hsym : (fun ξ : 𝔼 => mik1_Th m k (((2 : ℝ) ^ k)⁻¹ • ξ) * rhoT (((2 : ℝ) ^ k)⁻¹ • ξ)) =
      fun ξ => mik1_Th m k (((2 : ℝ) ^ k)⁻¹ • ξ) := by
    funext ξ
    unfold mik1_Th
    rw [mul_assoc, mul_comm (rho _) (rhoT _), rhoT_mul_rho]
  rw [mulS_congr hsym ((temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k).mul
      (temperate_symbol rhoT_contDiff rhoT_cs k))
      (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k)]

lemma mik1_U_rep (m : 𝔼 → ℂ) (hm : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) (u : 𝓢(𝔼, ℂ)) (k : ℤ)
    (x : 𝔼) : mik1_U m hm u k x = cv (symK (rhoT : 𝔼 → ℂ) k) (⇑(mik1_U m hm u k)) x := by
  rw [cv_symK_eq_mulS rhoT_contDiff rhoT_cs _ k]
  unfold mik1_U
  rw [mulS_mulS _ _ (temperate_symbol rhoT_contDiff rhoT_cs k)
    (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k)
    ((temperate_symbol rhoT_contDiff rhoT_cs k).mul
      (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k))]
  have hsym : (fun ξ : 𝔼 => rhoT (((2 : ℝ) ^ k)⁻¹ • ξ) * mik1_Th m k (((2 : ℝ) ^ k)⁻¹ • ξ)) =
      fun ξ => mik1_Th m k (((2 : ℝ) ^ k)⁻¹ • ξ) := by
    funext ξ
    unfold mik1_Th
    rw [mul_left_comm, rhoT_mul_rho]
  rw [mulS_congr hsym ((temperate_symbol rhoT_contDiff rhoT_cs k).mul
      (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k))
      (temperate_symbol (mik1_Th_contDiff hm k) (mik1_Th_cs m k) k)]

/-- a Fourier-localised Schwartz function with multiplier `m` is a finite sum of dyadic pieces -/
lemma mik1_sum_U (m : 𝔼 → ℂ) (hm : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) (u R : 𝓢(𝔼, ℂ))
    (ε Rr : ℝ) (hε : 0 < ε)
    (hu : ∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0)
    (hR : ∀ ξ : 𝔼, 𝓕 (⇑R) ξ = m ξ * 𝓕 (⇑u) ξ) :
    ∃ S : Finset ℤ, R = ∑ k ∈ S, mik1_U m hm u k := by
  obtain ⟨K0, n, hK0, hK1⟩ := xbb_exists_K ε (max Rr ε) hε (le_max_right _ _)
  refine ⟨(Finset.range (n + 1)).image (fun i : ℕ => K0 + (i : ℤ)), ?_⟩
  refine xschwartz_ext_fourier fun ξ => ?_
  have e1 : 𝓕 (R : 𝓢(𝔼, ℂ)) ξ = 𝓕 (⇑R) ξ := by rw [SchwartzMap.fourier_coe]
  have e2 : 𝓕 ((∑ k ∈ (Finset.range (n + 1)).image (fun i : ℕ => K0 + (i : ℤ)),
      mik1_U m hm u k : 𝓢(𝔼, ℂ))) ξ
      = 𝓕 (⇑(∑ k ∈ (Finset.range (n + 1)).image (fun i : ℕ => K0 + (i : ℤ)),
        mik1_U m hm u k)) ξ := by
    rw [SchwartzMap.fourier_coe]
  rw [e1, e2, xbb_fourier_sum, hR ξ, Finset.sum_image (fun i _ j _ h => by simpa using h)]
  simp_rw [mik1_U_fourier]
  by_cases h0 : 𝓕 (⇑u) ξ = 0
  · simp [h0]
  · have hξ : ε ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ Rr := by
      by_contra hcon
      apply h0
      refine hu ξ ?_
      by_cases h1 : ε ≤ ‖ξ‖
      · right; by_contra h2; exact hcon ⟨h1, not_lt.1 h2⟩
      · left; exact not_le.1 h1
    have hξ' : ‖ξ‖ ≤ (2 : ℝ) ^ (K0 + (n : ℤ)) := hξ.2.trans ((le_max_left _ _).trans hK1)
    have hp : ∑ i ∈ Finset.range (n + 1), rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ) = 1 := by
      refine xbb_rho_telescope ξ K0 n ?_ ?_
      · refine cut_one ?_
        have hs0 : 0 < (2 : ℝ) ^ (K0 + (n : ℤ)) := zpow_pos (by norm_num) _
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, inv_mul_le_iff₀ hs0, mul_one]
        exact hξ'
      · refine cut_zero ?_
        have hs0 : 0 < (2 : ℝ) ^ (K0 - 1) := zpow_pos (by norm_num) _
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, le_inv_mul_iff₀ hs0]
        have : (2 : ℝ) ^ (K0 - 1) * 2 = (2 : ℝ) ^ K0 := by
          rw [zpow_sub₀ (by norm_num), zpow_one]; field_simp
        rw [this]
        exact hK0.trans hξ.1
    calc m ξ * 𝓕 (⇑u) ξ
        = (m ξ * ∑ i ∈ Finset.range (n + 1), rho (((2 : ℝ) ^ (K0 + (i : ℤ)))⁻¹ • ξ)) *
            𝓕 (⇑u) ξ := by rw [hp, mul_one]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]

/-- `dK_dec` with the constant made explicit: `‖dK Θ j‖` is dominated by `C₀ B Φ_j` for every symbol family
with support in `B̄(0,R)` and derivatives of orders `≤ d+1` bounded by `B`, `C₀ = C₀(d,R)` -/
lemma mik1_dK_dec_unif (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Θ : ℤ → 𝔼 → ℂ), (∀ j, ContDiff ℝ ∞ (Θ j)) →
      (∀ j (η : 𝔼), R < ‖η‖ → Θ j η = 0) → ∀ B : ℝ, 0 ≤ B →
      (∀ j, ∀ i ≤ d + 1, ∀ η, ‖iteratedFDeriv ℝ i (Θ j) η‖ ≤ B) →
      ∀ j, DecK (ENNReal.ofReal (C * B)) j (dK Θ j) := by
  obtain ⟨C, hC0, hC⟩ := decay_dec_unif (d := d) R
  refine ⟨C, hC0, fun Θ hs hsupp B hB0 hB j x => ?_⟩
  have hM := hC (Θ j) (hs j) (hsupp j) B hB0 (hB j)
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hn : ‖((2 : ℝ) ^ j) • x‖ = (2 : ℝ) ^ j * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
  have h1 := hM (((2 : ℝ) ^ j) • x)
  rw [hn] at h1
  have hpos : 0 < (1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1) := by positivity
  have h2 : ‖𝓕⁻ (Θ j) (((2 : ℝ) ^ j) • x)‖ ≤ C * B * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact h1
  have h3 : ‖dK Θ j x‖ ≤ (C * B) * (((2 : ℝ) ^ j) ^ d * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by
    show ‖symK (Θ j) j x‖ ≤ _
    rw [symK_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ((2 : ℝ) ^ j) ^ d * ‖𝓕⁻ (Θ j) (((2 : ℝ) ^ j) • x)‖
        ≤ ((2 : ℝ) ^ j) ^ d * (C * B * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by gcongr
      _ = _ := by ring
  rw [← ofReal_norm]
  unfold Phi
  rw [← ENNReal.ofReal_mul (mul_nonneg hC0 hB0)]
  exact ENNReal.ofReal_le_ofReal h3

end HRS.CZ.Mik
