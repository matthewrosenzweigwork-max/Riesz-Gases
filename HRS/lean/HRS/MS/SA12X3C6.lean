import HRS.MS.SA12X3C6D
import HRS.MS.SA12X2Z
import HRS.MS.SA12X2I
import HRS.MS.SA12Z3NearR1

/-!
# S.A.12 C6 (SA12X3): `near_local_regimes`

The regime dispatch: R1 (`near_R1`), R2a (`near_R2a`), R2b (hypothesis `False`), R2c (`near_R2c`) and R3 (`r3_near_cell`),
each transported to real centres and `C_b^{m+3}` densities by `sa12x3_bridge`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- The dissipation spill: `ν₀/(8 card E)` in regime R3 and zero otherwise. -/
def nearSpill (Rg : PDE.Regime) (ν₀ : ℝ) (E : Finset (Fin d → ℤ)) : ℝ :=
  match Rg with
  | .R3 => ν₀ / (8 * (E.card : ℝ))
  | _ => 0

theorem sa12x3_posOf {s : ℝ} {m : ℕ} {Λ Cb T : ℝ} {χ χh : Euc d → ℝ} {E : Finset (Fin d → ℤ)} {A κ : ℝ}
    {hreg : Matrix (Fin d) (Fin d) ℝ → Prop} (h : EucNlBound s m Λ Cb T χ χh E A κ hreg) :
    EucNlBoundPositive d s m Λ Cb T χ χh E A κ hreg :=
  fun b Ψ hb hΨ M hM μ hμ _ F hF τ hτ z => h b Ψ hb hΨ M hM μ hμ F hF τ hτ z

theorem near_local_regimes (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hsd : s<d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (C : ℝ), CoversBall8 E ∧ 0<C ∧
      ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (ν ν₀ : ℝ),
      PDE.MatBound MB M → RdRegimeHolds Rg d s M ν ν₀ →
      ∀ μ : Euc d → ℝ, MemCb (m+3) μ → cbNorm (m+3) μ ≤ Λ →
      (∀ x, 0 ≤ μ x) → ∀ F : Euc d → ℝ, BddJets m F →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ c : Euc d,
        -(2*jetPair m (advCutoff χ Ψ τ c) F
          (eucNonlocal s M (fun y => advCutoff χh Ψ τ c y*μ y) F)) ≤
          nearSpill Rg ν₀ E*∑ k ∈ E, cellDissip m χ Ψ τ (c+cellPt d k) F+
          Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*
            ∑ k ∈ E, cellEnergy m χ Ψ τ (c+cellPt d k) F := by
  obtain ⟨Λ'', hΛ'', hbr⟩ := sa12x3_bridge hd m Cb T χ χh hχ Λ
  -- a vacuous fallback when the regime hypothesis cannot hold
  have hvac : ∀ (P : Prop), ¬ P → (∀ (M : Matrix (Fin d) (Fin d) ℝ) (ν ν₀ : ℝ), RdRegimeHolds Rg d s M ν ν₀ → P) →
      ∃ (E : Finset (Fin d → ℤ)) (C : ℝ), CoversBall8 E ∧ 0<C ∧
      ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ (M : Matrix (Fin d) (Fin d) ℝ) (ν ν₀ : ℝ),
      PDE.MatBound MB M → RdRegimeHolds Rg d s M ν ν₀ →
      ∀ μ : Euc d → ℝ, MemCb (m+3) μ → cbNorm (m+3) μ ≤ Λ →
      (∀ x, 0 ≤ μ x) → ∀ F : Euc d → ℝ, BddJets m F →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ c : Euc d,
        -(2*jetPair m (advCutoff χ Ψ τ c) F
          (eucNonlocal s M (fun y => advCutoff χh Ψ τ c y*μ y) F)) ≤
          nearSpill Rg ν₀ E*∑ k ∈ E, cellDissip m χ Ψ τ (c+cellPt d k) F+
          Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*
            ∑ k ∈ E, cellEnergy m χ Ψ τ (c+cellPt d k) F := by
    intro P hP hreg
    obtain ⟨E, hE⟩ := sa12z3_E_exists hd
    refine ⟨E, 1, hE, one_pos, ?_⟩
    intro b Ψ hb hΨ M ν ν₀ hMB hR
    exact absurd (hreg M ν ν₀ hR) hP
  have hEn : ∀ (E : Finset (Fin d → ℤ)) (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ)
      (F : Euc d → ℝ) (c : Euc d), 0 ≤ ∑ k ∈ E, cellEnergy m χ Ψ τ (c + cellPt d k) F :=
    fun E b Ψ τ F c => Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg m χ Ψ τ _ F
  cases Rg with
  | R1 =>
    by_cases h : s ≤ (d : ℝ) - 2
    · obtain ⟨E, A, hE, hA, hlat⟩ := near_R1 d hd s hs0 h m hm MB Λ'' Cb T χ χh hχ
      refine ⟨E, A + 1, hE, by linarith, ?_⟩
      intro b Ψ hb hΨ M ν ν₀ hMB hR μ hμ hcb hμ0 F hF τ hτ c
      have := hbr s E A 0 _ (sa12x3_posOf hlat) b Ψ hb hΨ M hMB μ hμ hcb hμ0 F hF τ hτ c
      have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + 1 by linarith) (hEn E b Ψ τ F c)
      simp only [nearSpill, PDE.Regime.lambdaM, zero_mul, zero_add] at this ⊢
      linarith
    · exact hvac (s ≤ (d : ℝ) - 2) h (fun M ν ν₀ hR => hR)
  | R2a =>
    by_cases h : (d : ℝ) - 2 < s
    · obtain ⟨E, A, hE, hA, hlat⟩ := near_R2a d hd s hs0 h hsd m hm MB Λ'' Cb T χ χh hχ
      refine ⟨E, A + 1, hE, by linarith, ?_⟩
      intro b Ψ hb hΨ M ν ν₀ hMB hR μ hμ hcb hμ0 F hF τ hτ c
      have hsym : Torus.symPart M = 0 := hR.2
      have := hbr s E A 0 _ (sa12x3_posOf hlat) b Ψ hb hΨ M ⟨hMB, hsym⟩ μ hμ hcb hμ0 F hF τ hτ c
      have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + 1 by linarith) (hEn E b Ψ τ F c)
      simp only [nearSpill, PDE.Regime.lambdaM, zero_mul, zero_add] at this ⊢
      linarith
    · exact hvac ((d : ℝ) - 2 < s) h (fun M ν ν₀ hR => hR.1)
  | R2b lam0 =>
    exact hvac False id (fun M ν ν₀ hR => hR)
  | R2c =>
    by_cases h : (d : ℝ) - 2 < s ∧ s ≤ (d : ℝ) - 1
    · obtain ⟨E, A, hE, hA, hlat⟩ := near_R2c d hd s hs0 h.1 h.2 hsd m hm MB Λ'' Cb T χ χh hχ
      refine ⟨E, A + 1, hE, by linarith, ?_⟩
      intro b Ψ hb hΨ M ν ν₀ hMB hR μ hμ hcb hμ0 F hF τ hτ c
      have hsn : Torus.SymNonpos M := hR.2.2
      have := hbr s E A 0 _ hlat b Ψ hb hΨ M ⟨hMB, hsn⟩ μ hμ hcb hμ0 F hF τ hτ c
      have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + 1 by linarith) (hEn E b Ψ τ F c)
      simp only [nearSpill, PDE.Regime.lambdaM, zero_mul, zero_add] at this ⊢
      linarith
    · exact hvac _ h (fun M ν ν₀ hR => ⟨hR.1, hR.2.1⟩)
  | R3 =>
    by_cases h : (d : ℝ) - 2 < s
    · obtain ⟨E, hE⟩ := sa12z3_E_exists hd
      obtain ⟨C3, hC3, hr3⟩ := r3_near_cell_gen d hd s hs0 hsd h m hm MB Λ'' Cb T χ χh hχ E hE
      refine ⟨E, C3 + 1, hE, by linarith, ?_⟩
      intro b Ψ hb hΨ M ν ν₀ hMB hR μ hμ hcb hμ0 F hF τ hτ c
      have hν₀ : 0 < ν₀ := hR.2.1
      have := hbr s E _ _ _ (sa12x3_posOf (hr3 ν₀ hν₀)) b Ψ hb hΨ M hMB μ hμ hcb hμ0 F hF τ hτ c
      have hp : 0 ≤ 1 + ν₀ ^ (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s))) := by
        have := Real.rpow_nonneg hν₀.le (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s)))
        linarith
      have h1 := mul_le_mul_of_nonneg_right
        (show C3 * (1 + ν₀ ^ (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s)))) ≤
          (C3 + 1) * (1 + ν₀ ^ (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s)))) by nlinarith)
        (hEn E b Ψ τ F c)
      simp only [nearSpill, PDE.Regime.lambdaM] at this ⊢
      linarith
    · exact hvac ((d : ℝ) - 2 < s) h (fun M ν ν₀ hR => hR.1)

end HRS.MH.AdjointRd.Phase2SA12Construction
