import HRS.Uniform.Q12W6

/-!
# Q12, part W7: Lemma 3.23 (`energy_W2`) conditional on Peyre's inequality
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- Lemma 3.23, statement of `HRS/Uniform/Comparison.lean` verbatim, with Peyre's inequality as hypothesis. -/
theorem energy_W2_of_peyre (hP : PeyreW2 d) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (Λ m₀ : ℝ) (hm₀ : 0 < m₀) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → (∀ x, m₀ ≤ ρ x) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N ∧
        torusWassersteinE 2 (empirical X) (withDensityReal ρ) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) ^ ((1 : ℝ) / max 2 ((d : ℝ) - s)))) := by
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  obtain ⟨C₀k, hC₀k, hE⟩ := coercivity_energy hd hs0 hsd
  obtain ⟨-, C₀m, hC₀m, hm⟩ := oNΛ_le_oN hd hs0 hsd C₀k hC₀k Λ' hΛ'1
  obtain ⟨Kh, hKh0, hKh⟩ := q12_hmSum_le hd hs0 hsd
  obtain ⟨Cp, hCp, hchain⟩ := q12_W_chain hP
  refine ⟨C₀m, fun C₀ hC₀ => ⟨2 * Real.sqrt (d / 8) * (Real.sqrt 2 + 1) +
    Cp / Real.sqrt m₀ * Real.sqrt (2 * Kh) + 1, by positivity, ?_⟩⟩
  intro N hN ρ hρ hρΛ hρm X hX
  have hρΛ' : ∀ x, ρ x ≤ Λ' := fun x => (hρΛ x).trans (le_max_left _ _)
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hΛ0 : 0 < Λ' := by linarith
  obtain ⟨hE0, hE1⟩ := hE Λ' hΛ'1 N hN ρ hρ hρΛ' X hX
  haveI := PDE.MFSemigroup.isProb_withDensityReal hρ
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  set F := rieszEnergy d s X μ with hF
  set lam := smearScale d N Λ' with hlam
  have hlam0 : 0 < lam := smearScale_pos (d := d) hN1 hΛ0
  have hε₀ : 0 < lam ^ 2 := by positivity
  have hEE : F + oNΛ d s C₀k Λ' N ≤ F + oN d s C₀ N := by
    have := (hm N hN).trans (q12_oN_mono hC₀ N)
    linarith
  have hE'0 : 0 ≤ F + oNΛ d s C₀k Λ' N := by
    have := Esq_nonneg hd hs0 hsd hε₀ X μ
    linarith
  have hT0 : 0 ≤ F + oN d s C₀ N := le_trans hE'0 hEE
  refine ⟨hT0, ?_⟩
  -- choice of the smearing scale
  set q : ℝ := (d : ℝ) - s with hq
  set t : ℝ := max (2 * lam ^ 2) ((F + oN d s C₀ N) ^ (2 / max 2 q)) with ht
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have h2ε : 2 * lam ^ 2 ≤ t := le_max_left _ _
  have hW := hchain ht0 hN0 X ρ hρ hm₀ hρm
  have hS := hKh hε₀ h2ε hN0 X μ
  have hEsq : Esq d s (lam ^ 2) X μ ≤ 2 * (F + oNΛ d s C₀k Λ' N) := hE1
  have hfac : 0 ≤ Kh * t ^ (-(max (q - 2) 0) / 2) := mul_nonneg hKh0 (Real.rpow_nonneg ht0.le _)
  have hS' : hmSum (smearDens d t (empirical X)) (smearDens d t μ) ≤
      Kh * t ^ (-(max (q - 2) 0) / 2) * (2 * (F + oNΛ d s C₀k Λ' N)) :=
    hS.trans (mul_le_mul_of_nonneg_left hEsq hfac)
  have hv : lam ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
    have hN0' : (0 : ℝ) < N := by exact_mod_cast hN0
    have hNΛ : (N : ℝ) ≤ N * Λ' := by nlinarith
    unfold smearScale at hlam
    rw [hlam]
    refine Real.rpow_le_rpow_of_nonpos hN0' hNΛ ?_
    have : 0 ≤ 1 / (d : ℝ) := by positivity
    rw [neg_div]; linarith
  refine hW.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsq : Real.sqrt (hmSum (smearDens d t (empirical X)) (smearDens d t μ)) ≤
      Real.sqrt (Kh * t ^ (-(max (q - 2) 0) / 2) * (2 * (F + oNΛ d s C₀k Λ' N))) :=
    Real.sqrt_le_sqrt hS'
  have hCm : 0 ≤ Cp / Real.sqrt m₀ := by positivity
  have hfin := q12_final_bound (dd := d) (Cp := Cp) (m := m₀) (Kh := Kh) (Nat.cast_nonneg d) hCp hm₀ hKh0
    (lam := lam) (v := (N : ℝ) ^ (-(1 : ℝ) / d)) (E := F + oN d s C₀ N)
    (E' := F + oNΛ d s C₀k Λ' N) q hlam0 hv hE'0 hEE
  refine le_trans ?_ hfin
  have : 2 * Real.sqrt (d * t / 8) + Cp / Real.sqrt m₀ *
      Real.sqrt (hmSum (smearDens d t (empirical X)) (smearDens d t μ)) ≤
      2 * Real.sqrt (d * t / 8) + Cp / Real.sqrt m₀ *
        Real.sqrt (Kh * t ^ (-(max (q - 2) 0) / 2) * (2 * (F + oNΛ d s C₀k Λ' N))) := by
    gcongr
  exact this

end HRS.Uniform.Q12
