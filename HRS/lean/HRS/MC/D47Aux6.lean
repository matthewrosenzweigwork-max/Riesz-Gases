import HRS.MC.D47Aux5

/-!
# Packet D47, auxiliary facts 6: scale arithmetic, `g_η(0)` bound and the lower bound for `F_{N,η}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

lemma d47_NL_pos {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) : 0 < (N : ℝ) * Λ := by
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  positivity

lemma d47_lam_pos {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) : 0 < smearScale d N Λ :=
  Real.rpow_pos_of_pos (d47_NL_pos hN hΛ) _

lemma d47_lam_le_one (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    smearScale d N Λ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (N : ℝ) * Λ := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  refine Real.rpow_le_one_of_one_le_of_nonpos h1 ?_
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have : -(1 : ℝ) / d ≤ 0 := by
    rw [neg_div]; exact neg_nonpos.mpr (by positivity)
  exact this

lemma d47_lam_rpow (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) (t : ℝ) :
    smearScale d N Λ ^ (-t) = (N : ℝ) ^ (t / d) * Λ ^ (t / d) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold smearScale
  rw [← Real.rpow_mul (d47_NL_pos hN hΛ).le, Real.mul_rpow hN0 (by linarith)]
  congr 2 <;> field_simp

lemma d47_Lam_lam (hd : 1 ≤ d) {s : ℝ} {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    Λ * smearScale d N Λ ^ ((d : ℝ) - s) = Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have h := d47_lam_rpow hd hN hΛ (s - d)
  rw [neg_sub] at h
  rw [h]
  have e : (s - d) / (d : ℝ) = s / d - 1 := by field_simp
  rw [e, Real.rpow_sub_one (by linarith : Λ ≠ 0)]
  have : Λ ≠ 0 := by linarith
  field_simp

lemma d47_lam_div (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) (t : ℝ) :
    smearScale d N Λ ^ (-t) / N = Λ ^ (t / d) * (N : ℝ) ^ (t / d - 1) := by
  rw [d47_lam_rpow hd hN hΛ t]
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [Real.rpow_sub_one hN0]
  field_simp

lemma d47_neg_log_lam (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    -Real.log (smearScale d N Λ) = Real.log ((N : ℝ) * Λ) / d := by
  unfold smearScale
  rw [Real.log_rpow (d47_NL_pos hN hΛ)]
  ring

lemma d47_log_nonneg {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) : 0 ≤ Real.log ((N : ℝ) * Λ) := by
  refine Real.log_nonneg ?_
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- A bound of the form `g_η(0) ≤ 1_{s=0}(-log λ) + C λ^{-s}` for all `η ≥ λ`, `λ ≤ 1`. -/
lemma d47_g0_main (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam η : ℝ, 0 < lam → lam ≤ 1 → lam ≤ η →
      fdlTruncT ψ s b η 0 ≤ (if s = 0 then -Real.log lam else 0) + C * lam ^ (-s) := by
  obtain ⟨C1, hC1⟩ := d47_g0_const hd hs0 hsd hψ hb (η0 := 1) one_pos
  have hlam1 : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → 1 ≤ lam ^ (-s) := fun lam h0 h1 =>
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 (by linarith)
  by_cases hs : s = 0
  · subst hs
    obtain ⟨C, hC⟩ := d47_g0_log hd hψ hb hsd
    refine ⟨max |C| |C1|, by positivity, fun lam η hl0 hl1 hlη => ?_⟩
    simp only [if_true]
    have hm1 : |C| ≤ max |C| |C1| := le_max_left _ _
    have hm2 : |C1| ≤ max |C| |C1| := le_max_right _ _
    have h1 : lam ^ (-(0 : ℝ)) = 1 := by simp
    rw [h1, mul_one]
    have hlog : 0 ≤ -Real.log lam := by
      have := Real.log_nonpos hl0.le hl1
      linarith
    by_cases hη1 : η < 1
    · have := hC η (lt_of_lt_of_le hl0 hlη) hη1
      have hlg : Real.log lam ≤ Real.log η := Real.log_le_log hl0 hlη
      linarith [le_abs_self C]
    · push Not at hη1
      have := hC1 η hη1
      linarith [le_abs_self C1]
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨C, hC0, hC⟩ := d47_g0_pos hd hspos hsd hψ hb
    refine ⟨max C |C1|, by positivity, fun lam η hl0 hl1 hlη => ?_⟩
    rw [if_neg hs, zero_add]
    have hm1 : C ≤ max C |C1| := le_max_left _ _
    have hm2 : |C1| ≤ max C |C1| := le_max_right _ _
    by_cases hη1 : η < 1
    · have h1 := hC η (lt_of_lt_of_le hl0 hlη) hη1
      have h2 : η ^ (-s) ≤ lam ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hl0 hlη (by linarith)
      have h3 : C * η ^ (-s) ≤ C * lam ^ (-s) := mul_le_mul_of_nonneg_left h2 hC0
      have h4 : C * lam ^ (-s) ≤ max C |C1| * lam ^ (-s) :=
        mul_le_mul_of_nonneg_right hm1 (Real.rpow_nonneg hl0.le _)
      linarith
    · push Not at hη1
      have := hC1 η hη1
      have h5 := hlam1 lam hl0 hl1
      have h6 : |C1| * 1 ≤ max C |C1| * lam ^ (-s) :=
        mul_le_mul hm2 h5 zero_le_one (by positivity)
      linarith [le_abs_self C1]

/-- The lower bound `F_{N,η} ≥ -(1_{s=0} log(NΛ)/(2dN) + C₁ a_N^Λ)` for every `η ≥ λ`. -/
lemma d47_lowerB (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → ∀ X : Config d N, ∀ η : ℝ,
      smearScale d N Λ ≤ η →
      -((if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) +
          C₁ * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1))) ≤
        fdlEnergy ψ s b η X (withDensityReal ρ) := by
  obtain ⟨C, hC0, hC⟩ := d47_g0_main hd hs0 hsd hψ hb
  refine ⟨C / 2, by positivity, fun Λ hΛ N hN ρ hρ X η hη => ?_⟩
  haveI := isProb_withDensityReal hρ
  set lam := smearScale d N Λ with hlam
  have hl0 : 0 < lam := d47_lam_pos hN hΛ
  have hl1 : lam ≤ 1 := d47_lam_le_one hd hN hΛ
  have hη0 : 0 < η := lt_of_lt_of_le hl0 hη
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hg0 := hC lam η hl0 hl1 hη
  have hF : fdlEnergy ψ s b η X (withDensityReal ρ) =
      modE (specKernel (d47_a ψ s b η)) N X (withDensityReal ρ) + d47_kappa ψ s b η / (2 * N) := by
    have h1 : fdlEnergy ψ s b η X (withDensityReal ρ) =
        modE (fun x => specKernel (d47_a ψ s b η) x - d47_kappa ψ s b η) N X (withDensityReal ρ) := by
      unfold fdlEnergy modulatedEnergyKernel modulatedEnergy modE
      rw [d47_trunc_eq hd hs0 hsd hψ hb hη0]
    rw [h1]
    exact d47_modE_sub_const (continuous_specKernel (fun k => d47_a_nonneg hb.1.le hη0 k)
      (d47_summable hd hs0 hψ hb.1 hη0).2) _ _ hN X
  have hlow := d47_modE_spec_lower (fun k => d47_a_nonneg hb.1.le hη0 k)
    (d47_summable hd hs0 hψ hb.1 hη0).2 (withDensityReal ρ) hN X
  have hg : fdlTruncT ψ s b η 0 = specKernel (d47_a ψ s b η) 0 - d47_kappa ψ s b η := by
    rw [d47_trunc_eq hd hs0 hsd hψ hb hη0]
  have hdiv := d47_lam_div hd hN hΛ s
  have hlogt : (if s = 0 then -Real.log lam else 0) =
      (if s = 0 then Real.log ((N : ℝ) * Λ) / d else 0) := by
    split_ifs
    · exact d47_neg_log_lam hd hN hΛ
    · rfl
  rw [hlogt] at hg0
  rw [hF]
  have key : -(specKernel (d47_a ψ s b η) 0 - d47_kappa ψ s b η) / (2 * N) ≤
      modE (specKernel (d47_a ψ s b η)) N X (withDensityReal ρ) + d47_kappa ψ s b η / (2 * N) := by
    have : -(specKernel (d47_a ψ s b η) 0 - d47_kappa ψ s b η) / (2 * N) =
        -(specKernel (d47_a ψ s b η) 0) / (2 * N) + d47_kappa ψ s b η / (2 * N) := by ring
    rw [this]; linarith
  refine le_trans ?_ key
  rw [← hg]
  have h2 : (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) =
      (if s = 0 then Real.log ((N : ℝ) * Λ) / d else 0) / (2 * N) := by
    split_ifs
    · field_simp
    · simp
  have e1 : (C / 2) * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) = C * lam ^ (-s) / (2 * N) := by
    rw [← hdiv]; field_simp; rfl
  rw [h2, e1, ← add_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right hg0 (by positivity)

end HRS.MC.D47
