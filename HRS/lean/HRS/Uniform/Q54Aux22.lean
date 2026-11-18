import HRS.Uniform.Q54Aux21
import HRS.Uniform.Q54Aux18

/-!
# Q54, part 22: the function-level family `UpF` (corrected propagator) from adjoint data

`UpF D μ u t φ = φ` for `u = t` and the adjoint propagator `U^{u,t} φ` otherwise.  From adjoint data of level `J` on every
window (`AdjointData`) and the coefficient hypotheses `GenHyp` we get `EvoCore J (UpF D μ)` (Proposition 3.9, uniqueness of
classical solutions: the cocycle law), quasi-contractivity `QuasiAt` and the Hölder estimate `HoldAt` at real levels.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- the adjoint propagator, corrected to be the identity on the diagonal. -/
def UpF (D : DynData d) (μ : ℝ → Torus d → ℝ) : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ :=
  fun u t φ => if u = t then φ else propagator D μ u t φ

theorem upF_self (D : DynData d) (μ : ℝ → Torus d → ℝ) (t : ℝ) (φ : Torus d → ℝ) :
    UpF D μ t t φ = φ := by simp [UpF]

theorem upF_of_ne (D : DynData d) (μ : ℝ → Torus d → ℝ) {u t : ℝ} (h : u ≠ t) (φ : Torus d → ℝ) :
    UpF D μ u t φ = propagator D μ u t φ := by simp [UpF, h]

theorem evoCore_upF (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : ∀ T : ℝ, 0 < T → AdjointData s J R MB Λ VB D ν₀ T μ) : EvoCore J (UpF D μ) := by
  have hpos : ∀ {u t : ℝ}, 0 ≤ u → u ≤ t → u ≠ t → 0 < t :=
    fun hu hut hne => lt_of_le_of_lt hu (lt_of_le_of_ne hut hne)
  refine ⟨fun u t hu hut φ hφ => ?_, fun u t hu hut φ ψ hφ hψ α β => ?_,
    fun u t hu hut c => ?_, fun t _ φ => upF_self D μ t φ, fun s' r t hs hsr hrt φ hφ => ?_⟩
  · by_cases h : u = t
    · rw [h, upF_self]; exact hφ
    · have ht := hpos hu hut h
      rw [upF_of_ne D μ h]
      exact prop_dom hd s hs0 hsd J hJ R MB Λ VB D ν₀ t μ (hA t ht) ⟨ht, le_rfl⟩ hφ ⟨hu, hut⟩
  · by_cases h : u = t
    · subst h
      simp only [upF_self]
    · have ht := hpos hu hut h
      simp only [upF_of_ne D μ h]
      exact prop_lin hd s hs0 hsd J hJ R MB Λ VB D ν₀ t μ (hA t ht) ⟨ht, le_rfl⟩ hφ hψ α β ⟨hu, hut⟩
  · by_cases h : u = t
    · subst h
      simp only [upF_self]
    · have ht := hpos hu hut h
      simp only [upF_of_ne D μ h]
      exact prop_const hd s hs0 hsd J hJ R MB Λ VB D ν₀ t μ (hA t ht) ⟨ht, le_rfl⟩ c ⟨hu, hut⟩
  · -- the cocycle law
    by_cases hrt' : r = t
    · subst hrt'
      rw [upF_self]
    · have hrtlt : r < t := lt_of_le_of_ne hrt hrt'
      have htpos : 0 < t := lt_of_le_of_lt (hs.trans hsr) hrtlt
      by_cases hsr' : s' = r
      · subst hsr'
        rw [upF_self]
      · have hsrlt : s' < r := lt_of_le_of_ne hsr hsr'
        have hst : s' ≠ t := ne_of_lt (hsrlt.trans hrtlt)
        rw [upF_of_ne D μ hst, upF_of_ne D μ hrt', upF_of_ne D μ hsr']
        exact propagator_semigroup hd s hs0 hsd J hJ R MB Λ VB D ν₀ t μ (hA t htpos) t
          ⟨htpos, le_rfl⟩ φ hφ.1 hφ.2 s' r hs hsr hrtlt

theorem quasi_upF (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB)
    (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ : ℝ) (hν₀ : 0 < ν₀)
    (J : ℕ) (hJa : a + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d) (μ : ℝ → Torus d → ℝ),
      (∀ T : ℝ, 0 < T → AdjointData s J R MB' Λ VB D ν₁ T μ) →
      (∀ t : ℝ, 0 ≤ t → GenHyp d s K MB Bμ BV D (μ t)) → ν₀ ≤ D.invβ →
      QuasiAt J (UpF D μ) a C := by
  obtain ⟨C, hC, hq⟩ := propagator_quasi hd s hs0 hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ hν₀ J hJa hJ3 hJm
  refine ⟨C, hC, fun R MB' Λ VB ν₁ D μ hA hG hν u t hu hut φ hφ => ?_⟩
  by_cases h : u = t
  · subst h
    rw [upF_self]
    refine ⟨memSobolev_of_dom (by linarith) hφ, ?_⟩
    simp
  · have ht : 0 < t := lt_of_le_of_lt hu (lt_of_le_of_ne hut h)
    rw [upF_of_ne D μ h]
    exact hq R MB' Λ VB ν₁ D t μ (hA t ht) (fun r hr => hG r hr.1) hν hφ hu hut ht le_rfl

theorem hold_upF (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K MB Bμ BV : ℝ) (hMB : 0 ≤ MB)
    (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (a : ℝ) (hK : (d : ℝ) + |a| + 4 ≤ K) (ν₀ νM : ℝ) (hν₀ : 0 < ν₀)
    (J : ℕ) (hJa : a + 2 < J) (hJ3 : (3 : ℝ) < J) (hJm : mStar d ≤ J) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (R : Regime) (MB' Λ VB ν₁ : ℝ) (D : DynData d)
      (μ : ℝ → Torus d → ℝ), (∀ T : ℝ, 0 < T → AdjointData s J R MB' Λ VB D ν₁ T μ) →
      (∀ t : ℝ, 0 ≤ t → GenHyp d s K MB Bμ BV D (μ t)) → ν₀ ≤ D.invβ → D.invβ ≤ νM →
      HoldAt J (UpF D μ) a A B := by
  obtain ⟨A, B, hA0, hB0, hh⟩ := prop_hold hd s hs0 hsd K MB Bμ BV hMB hBμ hBV a hK ν₀ νM hν₀ J hJa
    hJ3 hJm
  refine ⟨A, B, hA0, hB0, fun R MB' Λ VB ν₁ D μ hA hG hν hνM u t hu hut φ hφ => ?_⟩
  by_cases h : u = t
  · subst h
    rw [upF_self]
    have e : (fun x => φ x - φ x) = fun _ : Torus d => (0 : ℝ) := by funext x; ring
    rw [e]
    refine ⟨MFSemigroup.memSobolev_of_isSmooth (isSmooth_const' 0) a, ?_⟩
    have hz : sobolevNorm a (fun _ : Torus d => (0 : ℝ)) = 0 := by
      unfold sobolevNorm
      rw [mean_const']
      have : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun _ : Torus d => (0 : ℝ)) k = 0 := by
        intro k
        unfold Torus.funRealCoeff
        simp
      simp [this]
    rw [hz]
    simp
  · have ht : 0 < t := lt_of_le_of_lt hu (lt_of_le_of_ne hut h)
    rw [upF_of_ne D μ h]
    exact hh R MB' Λ VB ν₁ D t μ (hA t ht) (fun r hr => hG r hr.1) hν hνM hφ hu hut ht le_rfl

end HRS.Uniform.Q54
