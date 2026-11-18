import HRS.MS.SA16Y9Sw1
import HRS.MS.SA16Y11Crit
import HRS.MS.SA16Y11Fr4
import HRS.MS.SA16Y11Iso
import HRS.MS.SA16Y5Ex2
import HRS.MS.SA16Y5Ex3f
import HRS.MS.SA16Y6CEx2

/-!
# S.A.16 (SA16Y9) Fa1: `adjoint_lp_stability`

`sa16y9_adjoint_lp_stability : type_of% @HRS.Whole.AppendixA.adjoint_lp_stability`.  Case split over `κc : LpCase` and the range of `s`:
`sub` by `sa16y9_sub_stability` with `sa16y9_sub_src`; `iso`/`hilbert` for `d-2 < s < d-1` by `sa16y9_iso_stability` with `sa16y11_isoSrc`, for `s = d-1`
by `sa16y9_crit_stability` with `sa16y11_critSrc`, for `d-1 < s < d` by `sa16y9_frac_stability` with `sa16y11_fracSrc`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Fa1
variable {d : ℕ}

lemma sa16y9_hfar (hd : 1 ≤ d) {p s : ℝ} (hp : 2 ≤ p) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 < s) :
    (d : ℝ) < p * (s + 1) := by
  have h1 : (d : ℝ) < 2 * (s + 1) := by
    rcases (show d = 1 ∨ 2 ≤ d by omega) with h | h
    · subst h; norm_num; linarith
    · have : (2 : ℝ) ≤ d := by exact_mod_cast h
      linarith
  nlinarith

/-- the iso/hilbert-type regimes `s ≥ d-1` and `d-2 < s < d-1` for a matrix class `MCls` (generic in the class) -/
theorem sa16y9_stab_of_class (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (κc : LpCase) (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop) (hκMC : ∀ M, κc.Holds d s p M → MCls M)
    (hdom : ∀ M, κc.Holds d s p M → (d : ℝ) - 2 < s)
    (hMH : ∀ M, MCls M → ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
      M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A)
    (hHdI : ∀ m' : ℕ, s < (d : ℝ) - 1 → 0 < s + 2 - d → (d : ℝ) < p * (s + 1) → Sa16IsoHd d s p MB MCls m')
    (hHdC : ∀ m' : ℕ, s = (d : ℝ) - 1 → 0 < s + 2 - d → (d : ℝ) < p * (s + 1) → Sa16IsoHd d s p MB MCls m')
    (hHex : ∀ m' : ℕ, (d : ℝ) - 1 < s → Sa16FracEx d s p MB MCls m') :
    ∃ C : ℝ, 0 < C ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ → AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
      κc.Holds d s p D₁.M → κc.Holds d s p D₂.M →
      D₁.M = D₂.M → D₁.V = D₂.V → ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE (m + 2) p φ < ⊤ →
      ∀ F₁ F₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
        IsLpSolutionRd (m + 2) p χ (D₁.coeff μ₁) t φ F₁ → IsLpSolutionRd (m + 2) p χ (D₂.coeff μ₂) t φ F₂ →
        ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (fun x => F₁ τ x - F₂ τ x) ≤
          ENNReal.ofReal (C * τ * Real.exp (C * τ) * (|D₁.invβ - D₂.invβ| + δ)) * wNormE (m + 2) p φ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  by_cases hdom' : (d : ℝ) - 2 < s
  swap
  · exact ⟨1, one_pos, fun D₁ D₂ μ₁ μ₂ hD1 hD2 hκ1 => absurd (hdom _ hκ1) hdom'⟩
  have hfar := sa16y9_hfar hd hp2 hs0 hdom'
  rcases lt_trichotomy s ((d : ℝ) - 1) with hlt | heq | hgt
  · -- iso/hilbert, d-2 < s < d-1
    have hθ0 : 0 < s + 2 - d := by linarith
    exact sa16y9_iso_stability hd s hs0 hlt hθ0 m hm p hfar MB Λ ΛV G₀ νbar T χ hχ κc MCls hκMC
      (hHdI m hlt hθ0 hfar) (hHdI (m + 2) hlt hθ0 hfar) (sa16y11_isoSrc hd s hs0 m p MB Λ ΛV G₀ νbar T MCls)
  · have hθ0 : 0 < s + 2 - d := by linarith
    have hsrc9 : Sa16CritSrc d s m p MB Λ ΛV G₀ νbar T MCls :=
      sa16y11_critSrc hd s hs0 m p MB Λ ΛV G₀ νbar T MCls
    exact sa16y9_crit_stability hd s hs0 heq hθ0 m hm p hfar MB Λ ΛV G₀ νbar T χ hχ κc MCls hκMC
      (hHdC m heq hθ0 hfar) (hHdC (m + 2) heq hθ0 hfar) hsrc9
  · by_cases hMB : 0 ≤ MB
    · have hsrc9 : Sa16FracSrc d s m p MB Λ ΛV G₀ νbar T MCls :=
        sa16y11_fracSrc hd s hs0 m p MB Λ ΛV G₀ νbar T MCls hMH
      exact sa16y9_frac_stability hd s hsd hgt m hm p MB Λ ΛV G₀ νbar T hMB χ hχ κc MCls hκMC
        (hHex m hgt) (hHex (m + 2) hgt) hsrc9
    · exact ⟨1, one_pos, fun D₁ D₂ μ₁ μ₂ hD1 =>
        absurd ((abs_nonneg _).trans (hD1.hM ⟨0, by omega⟩ ⟨0, by omega⟩)) (not_le.2 (lt_of_not_ge hMB))⟩

end Fa1

end HRS.Whole.AppendixA.Phase2SA16R
