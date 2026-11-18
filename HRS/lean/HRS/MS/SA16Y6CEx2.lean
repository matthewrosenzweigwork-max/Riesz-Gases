import HRS.MS.SA16Y6CEx1
import HRS.MS.SA16Y6CDs2
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Ex2

/-! # SA16Y6 critical-case copy of SA16Y5Ex2 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16V2

section Ex2
variable {d : ℕ}
theorem sa16y6c_Hd_iso (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (hθ0 : 0 < s + 2 - d)
    {p : ℝ} [Fact (2 ≤ p)] (hfar : (d : ℝ) < p * (s + 1)) (m : ℕ) (MB : ℝ) :
    ∀ Wd : ℝ, 0 ≤ Wd → ∃ cN : ℝ, 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ},
      (∃ lam : ℝ, 0 ≤ lam ∧ M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ))) →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb 2 Wd μ → sa16y5_Dec (m + 2) Wd μ → ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        SA16IsoOp d (m + 1) p s M μ N' → ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hsd : s < d := by linarith
  intro Wd hWd
  obtain ⟨C1, hC10, hdiss⟩ := sa16y6c_diss (s := s) (p := p) hd hs0 hsd hs1 hθ0 hfar hWd Wd hWd m
  refine ⟨p * max MB 0 * C1, mul_nonneg (mul_nonneg hp0.le (le_max_right _ _)) hC10,
    fun {M} hMC hM {μ} hμ hpos hCb hdec N' hN' G => ?_⟩
  obtain ⟨lam, hlam, hMl⟩ := hMC
  have hlamMB : lam ≤ max MB 0 := by
    have h := hM ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [hMl] at h
    have h' : lam ≤ MB := by simpa [abs_of_nonneg hlam] using h
    exact h'.trans (le_max_left _ _)
  refine (hdiss hμ hpos hCb hdec hlam N' (by rw [← hMl]; exact hN') G).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamMB hp0.le) hC10)
    (sa16v2c_E_nonneg d m p _)

theorem sa16y6c_Hd_hilb (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (hθ0 : 0 < s + 2 - d)
    {p : ℝ} [Fact (2 ≤ p)] (hfar : (d : ℝ) < p * (s + 1)) (m : ℕ) (MB : ℝ) :
    ∀ Wd : ℝ, 0 ≤ Wd → ∃ cN : ℝ, 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ},
      (∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
        M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb 2 Wd μ → sa16y5_Dec (m + 2) Wd μ → ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        SA16IsoOp d (m + 1) p s M μ N' → ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hsd : s < d := by linarith
  intro Wd hWd
  obtain ⟨C1, C2, hC10, hC20, hdiss⟩ :=
    sa16y6c_diss_hilb (s := s) (p := p) hd hs0 hsd hs1 hθ0 hfar hWd Wd hWd m (max MB 0) (le_max_right _ _)
  refine ⟨p * (max MB 0 * C1 + C2), mul_nonneg hp0.le (add_nonneg (mul_nonneg (le_max_right _ _) hC10) hC20),
    fun {M} hMC hM {μ} hμ hpos hCb hdec N' hN' G => ?_⟩
  obtain ⟨lam, hlam, A, hskew, hMl⟩ := hMC
  have hAii : ∀ i, A i i = 0 := fun i => by
    have := congrFun (congrFun hskew i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hlamMB : lam ≤ max MB 0 := by
    have h := hM ⟨0, by omega⟩ ⟨0, by omega⟩
    rw [hMl] at h
    have h' : lam ≤ MB := by simpa [hAii, abs_of_nonneg hlam] using h
    exact h'.trans (le_max_left _ _)
  have hA : ∀ i j, |A i j| ≤ max MB 0 := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hAii]; simp
    · have h1 := hM i j
      rw [hMl] at h1
      have : |A i j| ≤ MB := by simpa [Matrix.one_apply, h] using h1
      exact this.trans (le_max_left _ _)
  refine (hdiss hμ hpos hCb hdec hlam hA hskew N' (by rw [← hMl]; exact hN') G).trans ?_
  have hE := sa16v2c_E_nonneg d m p (sa16sz_iota2 d m p G)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hp0.le) hE
  exact add_le_add (mul_le_mul_of_nonneg_right hlamMB hC10) le_rfl

theorem sa16y6c_adjoint_lp_iso (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1) (m : ℕ)
    (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → LpCase.iso.Holds d s p D.M →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
        (∃ F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤
            ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ) ∧
        ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F₁ →
          IsLpSolutionRd m p χ (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hiso : (d : ℝ) - 2 < s
  · have hθ0 : 0 < s + 2 - d := by linarith
    have hfar : (d : ℝ) < p * (s + 1) := by
      have : 2 * (s + 1) ≤ p * (s + 1) := by nlinarith
      linarith
    obtain ⟨C, hC, H⟩ := sa16y6c_exists_gen hd s hs0 hs1 hθ0 m hm p hfar MB Λ ΛV G₀ νbar T
      (fun M => ∃ lam : ℝ, 0 ≤ lam ∧ M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)))
      (fun Wd hWd => sa16y6c_Hd_iso hd hs0 hs1 hθ0 hfar m MB Wd hWd) χ hχ
    refine ⟨C, hC, fun D μ hD hκ t ht φ hφ => ?_⟩
    obtain ⟨-, lam, hlam, hMl⟩ := hκ
    exact ⟨H D μ hD ⟨lam, hlam.le, hMl⟩ t ht φ hφ, fun F₁ F₂ h₁ h₂ =>
      Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd m hm p LpCase.iso MB Λ ΛV G₀ νbar T χ D μ hD
        ⟨hiso, lam, hlam, hMl⟩ t ht φ F₁ F₂ h₁ h₂⟩
  · exact ⟨1, one_pos, fun D μ hD hκ => absurd hκ.1 hiso⟩

theorem sa16y6c_adjoint_lp_hilbert (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1) (m : ℕ)
    (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → LpCase.hilbert.Holds d s p D.M →
      ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
        (∃ F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) t, wNormE m p (F τ) ≤
            ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ) ∧
        ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F₁ →
          IsLpSolutionRd m p χ (D.coeff μ) t φ F₂ →
          ∀ τ ∈ Set.Icc (0 : ℝ) t, F₁ τ =ᵐ[volume] F₂ τ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_cases hhil : (d : ℝ) - 2 < s
  · have hθ0 : 0 < s + 2 - d := by linarith
    have hfar : (d : ℝ) < p * (s + 1) := by
      have : 2 * (s + 1) ≤ p * (s + 1) := by nlinarith
      linarith
    obtain ⟨C, hC, H⟩ := sa16y6c_exists_gen hd s hs0 hs1 hθ0 m hm p hfar MB Λ ΛV G₀ νbar T
      (fun M => ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
        M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A)
      (fun Wd hWd => sa16y6c_Hd_hilb hd hs0 hs1 hθ0 hfar m MB Wd hWd) χ hχ
    refine ⟨C, hC, fun D μ hD hκ t ht φ hφ => ?_⟩
    obtain ⟨-, hp, lam, hlam, A, hA, hMl⟩ := hκ
    exact ⟨H D μ hD ⟨lam, hlam, A, hA, hMl⟩ t ht φ hφ, fun F₁ F₂ h₁ h₂ =>
      Phase2SA16Assembly.sa16y4_lp_unique d hd s hs0 hsd m hm p LpCase.hilbert MB Λ ΛV G₀ νbar T χ D μ hD
        ⟨hhil, hp, lam, hlam, A, hA, hMl⟩ t ht φ F₁ F₂ h₁ h₂⟩
  · exact ⟨1, one_pos, fun D μ hD hκ => absurd hκ.1 hhil⟩

end Ex2

end HRS.Whole.AppendixA.Phase2SA16R
