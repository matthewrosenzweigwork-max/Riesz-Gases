import HRS.Commutator.Whole.XLIAux8

/-!
# X-LI part 9: the reproducing symbols `ρ̃`, `ρ̃̃`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- generic: an annulus-type symbol `θ` with a reproducing partner `θ'` gives a reproducing LP
family `symK θ j` -/
lemma isLPRep_of_symbols {θ θ' : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ)
    (hθ' : ContDiff ℝ ∞ θ') (hcs' : HasCompactSupport θ') (hrep : ∀ ξ, θ' ξ * θ ξ = θ ξ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hsum : ∀ ξ : 𝔼, ∑' j : ℤ, ‖θ (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ M) :
    IsLPRep (fun j => symK θ j) := by
  obtain ⟨A, hA, hdec⟩ := symK_dec hθ hcs
  obtain ⟨A', hA', hdec'⟩ := symK_dec hθ' hcs'
  refine ⟨⟨fun j => (symK_continuous hθ hcs j).measurable, ⟨A, hA, hdec⟩,
    ⟨M, hM, symK_orth hθ hcs hA hdec hsum⟩⟩, ?_⟩
  refine ⟨fun j => symK θ' j, A', hA', hdec',
    fun j => (symK_continuous hθ' hcs' j).measurable, ?_⟩
  intro F hF B hB hFB j x
  have hBr : ∀ x, ‖F x‖ ≤ B.toReal := fun x => by
    have := hFB x
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 this
  exact symK_rep hθ hcs hθ' hcs' hrep hF hBr j x

/-- the second reproducing symbol `ρ̃̃ = cut(·/4) - cut(16 ·)` -/
def rhoTT (η : 𝔼) : ℂ := (((cut ((1 / 4 : ℝ) • η) - cut ((16 : ℝ) • η) : ℝ)) : ℂ)

lemma rhoTT_contDiff : ContDiff ℝ ∞ (rhoTT : 𝔼 → ℂ) :=
  Complex.ofRealCLM.contDiff.comp (cut_contDiff.comp (contDiff_const_smul _) |>.sub
    (cut_contDiff.comp (contDiff_const_smul _)))

lemma rhoTT_eq_zero_of_ge {η : 𝔼} (h : 8 ≤ ‖η‖) : rhoTT η = 0 := by
  unfold rhoTT
  rw [cut_zero (by rw [norm_smul]; norm_num; linarith), cut_zero (by rw [norm_smul]; norm_num; linarith)]
  simp

lemma rhoTT_cs : HasCompactSupport (rhoTT : 𝔼 → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) 8) ?_
  intro η hη
  by_contra h
  exact hη (rhoTT_eq_zero_of_ge (by
    rw [mem_closedBall_zero_iff, not_le] at h; exact h.le))

lemma rhoT_eq_zero_of_le {η : 𝔼} (h : ‖η‖ ≤ 1 / 8) : rhoT η = 0 := by
  unfold rhoT
  rw [cut_one (by rw [norm_smul]; norm_num; linarith), cut_one (by rw [norm_smul]; norm_num; linarith)]
  simp

lemma rhoTT_mul_rhoT (η : 𝔼) : rhoTT η * rhoT η = rhoT η := by
  by_cases h1 : ‖η‖ ≤ 1 / 8
  · rw [rhoT_eq_zero_of_le h1]; simp
  by_cases h2 : 4 ≤ ‖η‖
  · rw [rhoT_eq_zero_of_ge h2]; simp
  push_neg at h1 h2
  have : rhoTT η = 1 := by
    unfold rhoTT
    rw [cut_one (by rw [norm_smul]; norm_num; linarith),
      cut_zero (by rw [norm_smul]; norm_num; linarith)]
    simp
  rw [this, one_mul]

lemma norm_rhoT_le_one (η : 𝔼) : ‖rhoT η‖ ≤ 1 := by
  unfold rhoT
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cut_nonneg ((1 / 2 : ℝ) • η), cut_le_one ((1 / 2 : ℝ) • η),
    cut_nonneg ((4 : ℝ) • η), cut_le_one ((4 : ℝ) • η)]

lemma rhoT_sq_sum_le (ξ : 𝔼) : ∑' j : ℤ, ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ 5 := by
  by_cases hξ : ξ = 0
  · subst hξ
    have : ∀ j : ℤ, ‖rhoT (((2 : ℝ) ^ j)⁻¹ • (0 : 𝔼))‖ₑ ^ 2 = 0 := fun j => by
      rw [smul_zero, rhoT_eq_zero_of_le (by simp)]; simp
    calc ∑' j : ℤ, ‖rhoT (((2 : ℝ) ^ j)⁻¹ • (0 : 𝔼))‖ₑ ^ 2 = ∑' j : ℤ, (0 : ℝ≥0∞) := tsum_congr this
      _ = 0 := tsum_zero
      _ ≤ 5 := zero_le
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨J, hJ1, hJ2⟩ := _root_.exists_mem_Ico_zpow hξ0 (one_lt_two : (1 : ℝ) < 2)
  have hsupp : ∀ j : ℤ, j ∉ (Finset.Icc (J - 1) (J + 3)) →
      ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 = 0 := by
    intro j hj
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    have hnorm : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (zpow_pos (by norm_num) j).le]
    have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
    suffices rhoT (((2 : ℝ) ^ j)⁻¹ • ξ) = 0 by rw [this]; simp
    rcases hj with hlt | hgt
    · -- j < J - 1: scaled norm ≥ 4
      apply rhoT_eq_zero_of_ge
      rw [hnorm]
      have : (2 : ℝ) ^ (j + 2) ≤ (2 : ℝ) ^ J := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have e : (2 : ℝ) ^ (j + 2) = (2 : ℝ) ^ j * 4 := by
        rw [zpow_add₀ (by norm_num)]; norm_num
      rw [← div_eq_inv_mul, le_div_iff₀ hs0]
      nlinarith
    · -- j > J + 3: scaled norm ≤ 1/8
      apply rhoT_eq_zero_of_le
      rw [hnorm]
      have : (2 : ℝ) ^ (J + 1) * 2 ^ 3 ≤ (2 : ℝ) ^ j := by
        have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show J + 4 ≤ j by omega)
        calc (2 : ℝ) ^ (J + 1) * 2 ^ 3 = (2 : ℝ) ^ (J + 4) := by
              rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]; norm_num; ring
          _ ≤ _ := h
      rw [← div_eq_inv_mul, div_le_iff₀ hs0]
      nlinarith
  rw [tsum_eq_sum hsupp]
  calc ∑ j ∈ Finset.Icc (J - 1) (J + 3), ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2
      ≤ ∑ j ∈ Finset.Icc (J - 1) (J + 3), (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have : ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ≤ 1 := by
          calc ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ = ENNReal.ofReal ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ :=
                (ofReal_norm _).symm
            _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (norm_rhoT_le_one _)
            _ = 1 := ENNReal.ofReal_one
        calc ‖rhoT (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ 1 ^ 2 := by gcongr
          _ = 1 := by simp
    _ = 5 := by
        rw [Finset.sum_const, Int.card_Icc]
        have h5 : (J + 3 + 1 - (J - 1)).toNat = 5 := by omega
        rw [h5]
        simp

lemma isLPRep_rhoT : IsLPRep (fun j => symK (rhoT : 𝔼 → ℂ) j) :=
  isLPRep_of_symbols rhoT_contDiff rhoT_cs rhoTT_contDiff rhoTT_cs rhoTT_mul_rhoT
    (M := 5) (by simp) rhoT_sq_sum_le

lemma isLPRep_rho' : IsLPRep (fun j => symK (rho : 𝔼 → ℂ) j) :=
  isLPRep_of_symbols rho_contDiff rho_cs rhoT_contDiff rhoT_cs rhoT_mul_rho
    (M := 2) (by simp) rho_sq_sum_le

end HRS.Commutator.Whole.XLI
