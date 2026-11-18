import HRS.Main.GFEVAux5

/-!
# Packet GFEVG, part 6: `EvoCore`, `QuasiAt` at integer levels (uniform constants), `HoldAt`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ}

/-- Quasi-contractivity at every integer level `1 ≤ m' ≤ J`, with constants `Cs m'` chosen before the data
(Proposition 3.9, regimes with `Λ_m = C`). -/
theorem gfev_quasi_levels (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (J : ℕ) (hJ : mStar d ≤ J)
    (R : Regime) (hR : ∀ C ν θ : ℝ, R.lambdaM C ν θ = C) (MB Λ VB : ℝ) :
    ∃ Cs : ℕ → ℝ, (∀ m', 0 < Cs m') ∧ ∀ (D : DynData d) (ν₀ : ℝ) (μ : ℝ → Torus d → ℝ),
      (∀ T : ℝ, 0 < T → AdjointData s J R MB Λ VB D ν₀ T μ) →
      ∀ m' : ℕ, 1 ≤ m' → m' ≤ J → QuasiAt J (UpF D μ) (m' : ℝ) (Cs m') := by
  obtain ⟨C, Cs, -, hCs, hmain⟩ := adjoint_torus_classical hd s hs0 hsd J hJ R MB Λ VB
  refine ⟨Cs, hCs, fun D ν₀ μ hA m' hm1 hmJ u t hu hut φ hφ => ?_⟩
  by_cases h : u = t
  · subst h
    rw [upF_self]
    refine ⟨memSobolev_of_dom (by exact_mod_cast hmJ) hφ, ?_⟩
    simp
  · have ht : 0 < t := lt_of_le_of_lt hu (lt_of_le_of_ne hut h)
    rw [upF_of_ne D μ h]
    obtain ⟨-, -, h3, -⟩ := hmain D ν₀ t μ (hA t ht) t ⟨ht, le_rfl⟩ φ hφ.1 hφ.2
    obtain ⟨hm, hb⟩ := h3 m' hm1 hmJ u ⟨hu, hut⟩
    rw [hR] at hb
    exact ⟨hm, hb⟩

variable {s : ℝ} {γ : ℕ} {R : Regime} {VB Λ : ℝ} {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem GFPde.core (h : GFPde d s γ R VB Λ D T ρ) :
    EvoCore (γ + 2) (UpF D (gfevMu T ρ)) := by
  have hJm : mStar d ≤ γ + 2 := by have := h.hm; omega
  exact evoCore_upF h.hd s h.hs0 h.hsd (γ + 2) hJm R 1 Λ VB D 0 (gfevMu T ρ)
    (fun T' hT' => h.adjointData (m := γ + 2) (by omega) hT')

/-- The Hölder estimate at the level `γ - 2`, from quasi-contractivity at the level `γ`. -/
theorem GFPde.hold (h : GFPde d s γ R VB Λ D T ρ) (l : ℝ)
    (hq : QuasiAt (γ + 2) (UpF D (gfevMu T ρ)) (γ : ℝ) l) :
    ∃ A B : ℝ, 0 ≤ B ∧ HoldAt (γ + 2) (UpF D (gfevMu T ρ)) ((γ : ℝ) - 2) A B := by
  obtain ⟨Bμ, BV, hBμ, hBV, hG⟩ := h.genHyp
  have hγ2 : (2 : ℝ) ≤ γ := by have := h.hγ5; exact_mod_cast (by omega : 2 ≤ γ)
  have hK : (d : ℝ) + |(γ : ℝ) - 2| + 4 ≤ ((γ + 2 * d + 11 : ℕ) : ℝ) := by
    rw [abs_of_nonneg (by linarith)]; push_cast; linarith
  have hJa : ((γ : ℝ) - 2) + 2 < ((γ + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hJ3 : (3 : ℝ) < ((γ + 2 : ℕ) : ℝ) := by
    have := h.hγ5; have : (5 : ℝ) ≤ γ := by exact_mod_cast this
    push_cast; linarith
  have hJm : mStar d ≤ γ + 2 := by have := h.hm; omega
  obtain ⟨B, hB0, hH⟩ := gfev_prop_hold h.hd s h.hs0 h.hsd ((γ + 2 * d + 11 : ℕ) : ℝ) 1 Bμ BV zero_le_one hBμ hBV
    ((γ : ℝ) - 2) hK D.invβ l (γ + 2) hJa hJ3 hJm
  refine ⟨1 + 2 * |l|, B, hB0, fun u t hu hut φ hφ => ?_⟩
  by_cases hne : u = t
  · subst hne
    rw [upF_self]
    have e : (fun x => φ x - φ x) = fun _ : Torus d => (0 : ℝ) := by funext x; ring
    rw [e]
    refine ⟨MFSemigroup.memSobolev_of_isSmooth (isSmooth_const' 0) _, ?_⟩
    have hz : sobolevNorm ((γ : ℝ) - 2) (fun _ : Torus d => (0 : ℝ)) = 0 := by
      unfold sobolevNorm
      rw [mean_const']
      have : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun _ : Torus d => (0 : ℝ)) k = 0 := by
        intro k; unfold Torus.funRealCoeff; simp
      simp [this]
    rw [hz]; simp
  · have ht : 0 < t := lt_of_le_of_lt hu (lt_of_le_of_ne hut hne)
    have hA : AdjointData s (γ + 2) R 1 Λ VB D 0 t (gfevMu T ρ) := h.adjointData (m := γ + 2) (by omega) ht
    have hGt : ∀ r ∈ Set.Icc (0 : ℝ) t, GenHyp d s ((γ + 2 * d + 11 : ℕ) : ℝ) 1 Bμ BV D (gfevMu T ρ r) :=
      fun r _ => hG r
    have hprop : ∀ {φ' : Torus d → ℝ}, Dom (γ + 2) φ' → ∀ {u' t' : ℝ}, 0 ≤ u' → u' ≤ t' → 0 < t' → t' ≤ t →
        propagator D (gfevMu T ρ) u' t' φ' = UpF D (gfevMu T ρ) u' t' φ' := by
      intro φ' hφ' u' t' hu' hut' ht' ht't
      by_cases h0 : u' = t'
      · subst h0
        rw [upF_self]
        exact prop_self_pos h.hd s h.hs0 h.hsd (γ + 2) hJm R 1 Λ VB D 0 t (gfevMu T ρ) hA ⟨ht', ht't⟩ hφ'
      · rw [upF_of_ne D (gfevMu T ρ) h0]
    have hq' : ∀ {φ : Torus d → ℝ}, Dom (γ + 2) φ → ∀ {u t' : ℝ}, 0 ≤ u → u ≤ t' → 0 < t' → t' ≤ t →
        MemSobolev (((γ : ℝ) - 2) + 2) (propagator D (gfevMu T ρ) u t' φ) ∧
          sobolevNorm (((γ : ℝ) - 2) + 2) (propagator D (gfevMu T ρ) u t' φ) ≤
            Real.exp (l * (t' - u)) * sobolevNorm (((γ : ℝ) - 2) + 2) φ := by
      intro φ' hφ' u' t' hu' hut' ht' ht't
      have e2 : ((γ : ℝ) - 2) + 2 = γ := by ring
      rw [e2, hprop hφ' hu' hut' ht' ht't]
      exact hq u' t' hu' hut' φ' hφ'
    have key := hH R 1 Λ VB 0 D t (gfevMu T ρ) hA hGt le_rfl hq' hφ hu hut ht le_rfl
    simp only [upF_of_ne D (gfevMu T ρ) hne]
    exact key

end HRS.GF
