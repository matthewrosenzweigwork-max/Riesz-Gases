import HRS.MS.FixEqP3Aux9

/-!
# S5.7 `fixed_equation` (worker S57P), part 22: uniform bounds of the feature orbits of a family

`S57pFx`: the hypotheses on one family `(ν, c, ρ)` at level `n` (adjoint input through order `n+1`, decay class and `C^{R₁}` bounds,
`R₁ = n+2+⌈d/2⌉`).  `s57p_fam_bounds`: constants `C_a, C_d` (independent of the family) with
`‖D^i U^{r,t}φ_α‖ ≤ C_a λ_α^{(J-m)/2}` (`i ≤ n+1`) and `‖D (U^{r,t}φ_α - U^{r,s}φ_α)‖ ≤ C_d λ_α^{(J-m)/2} (t-s)`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the hypotheses on one family at level `n` -/
structure S57pFx (θ : Euc d → ℝ) (T : ℝ) (n : ℕ) (K : ℝ) (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    (c : ℝ → Euc d → Euc d) (ρ : ℝ → Euc d → ℝ) (A Λc νbar : ℝ) : Prop where
  fam : S57pFam (fixedEqCoeff s M Q ν c ρ) θ T (n + 1) K
  fe : S57pFeData s Q ν c ρ T
  hn4 : 4 ≤ n
  hT : 0 ≤ T
  prob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t)
  hρ : ∀ t ∈ Set.Icc (0 : ℝ) T, RgDecay (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ + 2) (fun _ => A) (ρ t)
  hc : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) (c t) ∧
    ∀ i ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x, ‖iteratedFDeriv ℝ i (c t) x‖ ≤ Λc
  hν : |ν| ≤ νbar

/-- the feature kernel `κ_t(φ) = 1_{r ≤ t} √(2qρ) ∇U^{r,t}φ` -/
def s57pκ (C : WholeCoeff d) (T q : ℝ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (φ : Euc d → ℝ) : Lp (Euc d) 2 (s57pμ d T) :=
  s57pel T (s57pw T q ρ) (s57pA C t φ) t

/-- the orbit bounds of the Hermite features -/
def S57pOrbBd (C : WholeCoeff d) (T : ℝ) (n : ℕ) (m : ℝ) (J : ℕ) (Ca Cd : ℝ) : Prop :=
  ∀ α : MultiIndex d,
    (∀ t ∈ Set.Icc (0 : ℝ) T, IsClassicalAdjointW C t (oscTestFun m α) (fun r => propagatorW C r t (oscTestFun m α)) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (n + 1) (propagatorW C r t (oscTestFun m α)) ∧
        ∀ i ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ i (propagatorW C r t (oscTestFun m α)) x‖ ≤
          Ca * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ∧
    ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T → ∀ r ∈ Set.Icc (0 : ℝ) t₁, ∀ i ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ i (fun y => propagatorW C r t₂ (oscTestFun m α) y - propagatorW C r t₁ (oscTestFun m α) y) x‖ ≤
        Cd * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) * (t₂ - t₁)

theorem s57p_fam_bounds {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (K : ℝ) (m : ℝ) (J : ℕ)
    (hJ : 3 * (n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) + 9 ≤ J) {A Λc νbar : ℝ} (hA : 0 ≤ A) (hΛc : 0 ≤ Λc) (hνbar : 0 ≤ νbar) :
    ∃ Cj Ca Cd : ℝ, 0 ≤ Cj ∧ 0 ≤ Ca ∧ 0 ≤ Cd ∧
      (∀ α : MultiIndex d, ContDiff ℝ ∞ (oscTestFun m α) ∧ ∀ l ≤ n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊, ∀ x,
        ‖iteratedFDeriv ℝ l (oscTestFun m α) x‖ ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) ∧
      ∀ {T : ℝ} {ν : ℝ} {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ}, S57pFx θ T n K s M Q ν c ρ A Λc νbar →
        S57pOrbBd (fixedEqCoeff s M Q ν c ρ) T n m J Ca Cd := by
  set R := n + 1 + 1 + ⌈(d : ℝ) / 2⌉₊ with hR
  obtain ⟨Cj, hCj0, hjets⟩ := s57p_osc_jets hθ hd m J R hJ
  obtain ⟨Cg, hCg0, hCg⟩ := s57p_gen_jets hθ hd hs0 hsd M Q m J R hJ hA hΛc hνbar
  obtain ⟨hCu0, hCu⟩ := s57pCu_spec hθ (n + 1)
  set Cu := s57pCu θ hθ (n + 1) with hCudef
  refine ⟨Cj, |K| * (Cu * Cj), |K| * (Cu * Cg), hCj0, by positivity, by positivity, hjets, ?_⟩
  intro T ν c ρ Fx α
  have hpos : 0 ≤ Cj * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    mul_nonneg hCj0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hposg : 0 ≤ Cg * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) :=
    mul_nonneg hCg0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hφR : ContDiff ℝ (R : WithTop ℕ∞) (oscTestFun m α) := (hjets α).1.of_le (by exact_mod_cast le_top)
  refine ⟨fun t ht => ?_, fun t₁ t₂ h0 h12 h2T r hr i hi x => ?_⟩
  · obtain ⟨h1, h2⟩ := hCu Fx.fam.adj hpos hφR (fun l hl x => (hjets α).2 l hl x) t ht
    refine ⟨h1, fun r hr => ⟨(h2 r hr).1, fun i hi x => ?_⟩⟩
    refine ((h2 r hr).2 i hi x).trans (le_of_eq ?_)
    ring
  · have hg : ∀ u ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (R : WithTop ℕ∞) (generatorW (fixedEqCoeff s M Q ν c ρ) u (oscTestFun m α)) ∧
        ∀ l ≤ R, ∀ x, ‖iteratedFDeriv ℝ l (generatorW (fixedEqCoeff s M Q ν c ρ) u (oscTestFun m α)) x‖ ≤
          Cg * oscEigenvalue d α ^ (((J : ℝ) - m) / 2) := fun u hu =>
      hCg Fx.hν (Fx.hρ u hu) (Fx.hc u hu).1 (Fx.hc u hu).2 α
    have := s57p_td_bound hθ Fx.fam Fx.hn4 hpos hposg hφR (fun l hl x => (hjets α).2 l hl x) hg h0 h12 h2T r hr i hi x
    refine this.trans (le_of_eq ?_)
    ring

end HRS.MS.FixEq
