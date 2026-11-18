import HRS.MS.Fp81S21QwinDecay

/-!
# HRS S2.1(iii), SOL26 packet 27c: shifted terminal families

The common-radius orbit and terminal-regularity claims produce the exact
`s103_famHyp` needed by the derivative-valued cosine integration lemma, on each
horizon `[0,T₀]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrb
open HRS.MS.R2WinOrbNL
open HRS.MS.R2WinErr

private theorem fp81s21_qwin_family_of_claims
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Co co : ℝ}
    (hOrbit : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (α : MultiIndex p.d) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    ∃ F : ℕ → ℝ → Euc p.d → ℝ,
      s103_famHyp F (4 * p.d + 42) T₀
        (max Co 0 * s103_b p.d α) ∧
      (∀ (i : ℕ) (hi : i < 3) (t : ℝ),
        F i t = propagatorW (r26t3_coeff R) 0 t
          (s103nData (r26t3_coeff R)
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α) ⟨i, hi⟩ t)) := by
  let C := r26t3_coeff R
  let φ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let F : ℕ → ℝ → Euc p.d → ℝ := fun i t =>
    if hi : i < 3 then propagatorW C 0 t
      (s103nData C φ ⟨i, by omega⟩ t) else 0
  have hFval : ∀ i (hi : i < 3) t,
      F i t = propagatorW C 0 t (s103nData C φ ⟨i, hi⟩ t) := by
    intro i hi t
    simp [F, hi]
  have hFam : s103_famHyp F (4 * p.d + 42) T₀
      (max Co 0 * s103_b p.d α) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi t ht
      have hExist := hterm R.ε R.ψ R.ρ R.admissible R.resulting α T₀ hT₀
      obtain ⟨f, hf⟩ := hExist.1 ⟨i, by omega⟩ t ht
      have hpw : IsClassicalAdjointW C t
          (s103nData C φ ⟨i, by omega⟩ t)
          (fun r => propagatorW C r t (s103nData C φ ⟨i, by omega⟩ t)) :=
        HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
      obtain ⟨hSup0, hGrad0, hSup1, hGrad1, hSup2⟩ :=
        hOrbit R.ε R.ψ R.ρ R.admissible R.resulting α t ht.1
      have hb : 0 ≤ s103_b p.d α := s103_b_nonneg α
      have hA : Co * s103_b p.d α ≤ max Co 0 * s103_b p.d α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hb
      have hSup : R2OrbitSup C (4 * p.d + 42) t
          (s103nData C φ ⟨i, by omega⟩ t)
          (max Co 0 * s103_b p.d α) := by
        interval_cases i
        · simpa [s103nData, C, φ, r26t3_coeff, wholeSpaceIndex] using s103_orbitSup_mono hSup0 hA
        · simpa [s103nData, C, φ, r26t3_coeff, wholeSpaceIndex] using s103_orbitSup_mono hSup1 hA
        · simpa [s103nData, C, φ, r26t3_coeff, wholeSpaceIndex] using s103_orbitSup_mono hSup2 hA
      obtain ⟨hcd, _⟩ := hSup _ hpw 0 ⟨by norm_num, ht.1⟩
      simpa [F, hFval i (by omega) t] using hcd
    · intro i hi t ht j hj x
      have hExist := hterm R.ε R.ψ R.ρ R.admissible R.resulting α T₀ hT₀
      obtain ⟨f, hf⟩ := hExist.1 ⟨i, by omega⟩ t ht
      have hpw : IsClassicalAdjointW C t
          (s103nData C φ ⟨i, by omega⟩ t)
          (fun r => propagatorW C r t (s103nData C φ ⟨i, by omega⟩ t)) :=
        HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
      obtain ⟨hSup0, hGrad0, hSup1, hGrad1, hSup2⟩ :=
        hOrbit R.ε R.ψ R.ρ R.admissible R.resulting α t ht.1
      have hb : 0 ≤ s103_b p.d α := s103_b_nonneg α
      have hA : Co * s103_b p.d α ≤ max Co 0 * s103_b p.d α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hb
      have hSup : R2OrbitSup C (4 * p.d + 42) t
          (s103nData C φ ⟨i, by omega⟩ t)
          (max Co 0 * s103_b p.d α) := by
        interval_cases i
        · simpa [s103nData, C, φ, r26t3_coeff, wholeSpaceIndex] using s103_orbitSup_mono hSup0 hA
        · simpa [s103nData, C, φ, r26t3_coeff, wholeSpaceIndex] using s103_orbitSup_mono hSup1 hA
        · simpa [s103nData, C, φ, r26t3_coeff, wholeSpaceIndex] using s103_orbitSup_mono hSup2 hA
      obtain ⟨_, hbd⟩ := hSup _ hpw 0 ⟨by norm_num, ht.1⟩
      have hbound := s103_cb_of_E
        (mul_nonneg (le_max_right Co 0) hb) hbd j hj x
      simpa [F, hFval i (by omega) t] using hbound
    · intro i hi t ht ε hε
      obtain ⟨δq, hδq, hq⟩ := (hterm R.ε R.ψ R.ρ
        R.admissible R.resulting α T₀ hT₀).2.1
          ⟨i, by omega⟩ (by omega) 0 t (by norm_num) ht.1 ht.2 ε hε
      refine ⟨δq, hδq, fun h hh hhd ht' j hj x => ?_⟩
      have hq' := hq h hh hhd (by linarith [ht'.1]) ht'.2 j hj x
      simpa [F, C, φ, r26t3_coeff, wholeSpaceIndex,
        show i < 3 by omega, show i + 1 < 3 by omega] using hq'
  refine ⟨F, hFam, ?_⟩
  intro i hi t
  exact hFval i hi t

theorem fp81s21_qwin_shifted_family (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ α : MultiIndex p.d, ∀ T₀ : ℝ, 0 ≤ T₀ →
          ∃ F : ℕ → ℝ → Euc p.d → ℝ,
            s103_famHyp F (4 * p.d + 42) T₀ (C * s103_b p.d α) ∧
            (∀ (i : ℕ) (hi : i < 3) (t : ℝ),
              F i t = propagatorW (r26t3_coeff R) 0 t
                (s103nData (r26t3_coeff R)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α) ⟨i, hi⟩ t)) := by
  obtain ⟨δ0, Co, co, hδ0, hδ0half, hco, hcommon⟩ :=
    fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδ0half, fun δ hδ hδle R => ?_⟩
  obtain ⟨hOrbit, _, hterm, _⟩ :=
    hcommon δ hδ hδle R.ρβ R.thermal
  let C : ℝ := max Co 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, fun α T₀ hT₀ => ?_⟩
  exact fp81s21_qwin_family_of_claims p R hOrbit hterm α hT₀

#print axioms fp81s21_qwin_shifted_family

end HRS.Fp81.S21

end
