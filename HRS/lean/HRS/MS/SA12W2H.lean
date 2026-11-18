import HRS.MS.SA12W2G

/-!
# S.A.12 C5 (SA12W2 worker), part H: `sa12w2_torus_data` (`R26-T5.T01` and `T02`)

Descent to the unit torus with `M ↦ L^{-s-2}M`, `ν ↦ ν/L²`, `V ↦ V(L·)/L²`, density `L^d μ(L·)` (clamped reversed time),
datum `φ(L·)`, and `AdjointData` at every level `N` (constants depending on `L, N` and the approximant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12w2_torus_data (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (T L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    (μ : ℝ → Euc d → ℝ) (V : Euc d → ℝ) (b : ℝ → Euc d → Euc d)
    (hP : PerSmooth s T L γ M ν μ V b) (hTime : PeriodicTimeSmooth T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (Rg : PDE.Regime) (ν₀ : ℝ) (hR : RdRegimeHolds Rg d s M ν ν₀)
    (φ : Euc d → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφp : ∀ (x : Euc d) (k : Fin d → ℤ), φ (x + L • latticePt k) = φ x) :
    ∃ (D₁ : DynData d) (ρ : ℝ → Torus d → ℝ) (φ₁ : Torus d → ℝ),
      D₁.s = s ∧ D₁.M = (L ^ (-s - 2)) • M ∧ D₁.invβ = ν / L ^ 2 ∧
      Torus.lift D₁.V = (fun y => V (L • y) / L ^ 2) ∧
      (∀ r ∈ Icc (0 : ℝ) T, Torus.lift (ρ r) = fun y => L ^ d * μ (max (t - r) 0) (L • y)) ∧
      Torus.lift φ₁ = (fun y => φ (L • y)) ∧
      (∀ N : ℕ, ∃ MB Λ VB : ℝ, PDE.AdjointData s N Rg MB Λ VB D₁ (ν₀ / L ^ 2) T ρ) ∧
      (∀ N : ℕ, PDE.MemHs (N : ℝ) (PDE.coeffOf φ₁)) ∧ PDE.IsRealCoeff (PDE.coeffOf φ₁) := by
  have hL : 0 < L := lt_of_lt_of_le one_pos hP.hL
  have hT0 : 0 ≤ T := ht.1.le.trans ht.2
  have hVper : ∀ (x : Euc d) (z : Fin d → ℤ), (fun x => V x / L ^ 2) (x + L • latticePt z) =
      (fun x => V x / L ^ 2) x := fun x z => by simp only [hP.V_periodic x z]
  set D₁ : DynData d :=
    { s := s, M := (L ^ (-s - 2)) • M, V := sa12w2_desc L (fun x => V x / L ^ 2), invβ := ν / L ^ 2,
      hs0 := hs0, hsd := hsd, hβ := div_nonneg hP.hν (sq_nonneg L) } with hD₁
  set ρ : ℝ → Torus d → ℝ := fun r => sa12w2_dens L (μ (sa12w2_tau t T r)) with hρ
  refine ⟨D₁, ρ, sa12w2_desc L φ, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext y
    exact sa12w2_lift_desc (f := fun x => V x / L ^ 2) hVper y
  · intro r hr
    funext y
    simp only [hρ]
    rw [sa12w2_dens_lift (hP.μ_periodic _ (sa12w2_tau_mem hT0 r)) y, sa12w2_tau_eq ht.2 hr]
  · funext y
    exact sa12w2_lift_desc hφp y
  · intro N
    have hck : ∀ r : ℝ, Torus.IsCk ((N : WithTop ℕ∞) + 3) (ρ r) := fun r =>
      sa12w2_contDiff_desc (f := fun x => L ^ d * μ (sa12w2_tau t T r) x)
        (fun x z => by rw [hP.μ_periodic _ (sa12w2_tau_mem hT0 r) x z]) hL.ne'
        (contDiff_const.mul ((hP.μ_smooth _ (sa12w2_tau_mem hT0 r)).of_le (by simp)))
    obtain ⟨Λ, hΛ⟩ := sa12w2_dens_cb hL hP.μ_periodic hP.μ_smooth hTime (N + 3)
    have hVck : Torus.IsCk ((N : WithTop ℕ∞) + 3) D₁.V :=
      sa12w2_contDiff_desc (f := fun x => V x / L ^ 2) hVper hL.ne'
        ((hP.V_smooth.div_const _).of_le (by simp))
    refine ⟨∑ i, ∑ j, |D₁.M i j|, Λ, Torus.cbNorm (N + 3) D₁.V,
      ⟨rfl, fun i j => ?_, ⟨hVck, le_rfl⟩, ⟨fun r hr => ?_, fun r hr => hck r, fun r hr => ?_, ?_⟩,
        ht.1.trans_le ht.2, ?_⟩⟩
    · calc |D₁.M i j| ≤ ∑ j', |D₁.M i j'| :=
            Finset.single_le_sum (f := fun j' => |D₁.M i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', |D₁.M i' j'| :=
            Finset.single_le_sum (f := fun i' => ∑ j', |D₁.M i' j'|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    · obtain ⟨hnn, hint⟩ := hP.μ_prob _ (sa12w2_tau_mem hT0 r)
      exact sa12w2_dens_prob hL (hP.μ_periodic _ (sa12w2_tau_mem hT0 r))
        (hP.μ_smooth _ (sa12w2_tau_mem hT0 r)) hnn hint
    · exact hΛ _ (sa12w2_tau_mem hT0 r)
    · exact fun ψ hψ => (sa12w2_dens_cont hL hT0 hP.μ_periodic hP.μ_smooth hTime ψ hψ).continuousOn
    · exact sa12w2_regime s M ν ν₀ L T hL Rg ρ hR
  · intro N
    exact (ClassicalPart.memHs_coeffOf_cbNorm N (sa12w2_desc L φ)
      (sa12w2_contDiff_desc hφp hL.ne' (hφ.of_le (by simp)))).1
  · exact isRealCoeff_coeffOf _ (ClassicalAux.integrable_of_continuous
      (Torus.continuous_of_continuous_lift
        (sa12w2_contDiff_desc hφp hL.ne' (hφ.of_le (by simp)) (n := 0)).continuous))

end HRS.PDE.SA12W2
