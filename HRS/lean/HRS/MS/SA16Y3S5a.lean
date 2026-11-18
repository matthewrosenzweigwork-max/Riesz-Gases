import HRS.MS.SA16Y3S4
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# S.A.16 (SA16Y3) S5a: passage to the limit in the weak identity (abstract)

`sa16y3_limit_identity`: let `a_n(τ) = ℓ_ψ(g_n τ)` satisfy `a_n(τ) = c_n + ∫_0^τ f_n` on `[0,T]` with `f_n` continuous on `[0,T]`,
`|f_n| ≤ Lf` (uniform in `n`), `c_n → c0`, and along a subsequence `a_{n_j}(τ) → a(τ)` and `f_{n_j}(σ) → f(σ)` for
`σ ∈ [0,T]`.  Then `a(τ) = c0 + ∫_0^τ f` for `τ ∈ [0,T]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

theorem sa16y3_limit_identity {T Lf c0 : ℝ} (a : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (hfc : ∀ n, ContinuousOn (f n) (Icc 0 T)) (hfb : ∀ n, ∀ σ ∈ Icc (0 : ℝ) T, |f n σ| ≤ Lf)
    (hid : ∀ n, ∀ τ ∈ Icc (0 : ℝ) T, a n τ = c n + ∫ σ in (0 : ℝ)..τ, f n σ)
    (hc : Tendsto c atTop (𝓝 c0)) (φ : ℕ → ℕ) (hφ : StrictMono φ) (alim : ℝ → ℝ) (flim : ℝ → ℝ)
    (ha : ∀ τ ∈ Icc (0 : ℝ) T, Tendsto (fun j => a (φ j) τ) atTop (𝓝 (alim τ)))
    (hf : ∀ σ ∈ Icc (0 : ℝ) T, Tendsto (fun j => f (φ j) σ) atTop (𝓝 (flim σ))) :
    ∀ τ ∈ Icc (0 : ℝ) T, alim τ = c0 + ∫ σ in (0 : ℝ)..τ, flim σ := by
  intro τ hτ
  have hτ0 := hτ.1
  have hsub : Set.uIoc (0 : ℝ) τ ⊆ Icc 0 T := by
    rw [uIoc_of_le hτ0]
    exact fun x hx => ⟨hx.1.le, hx.2.trans hτ.2⟩
  have hlim : Tendsto (fun j => ∫ σ in (0 : ℝ)..τ, f (φ j) σ) atTop (𝓝 (∫ σ in (0 : ℝ)..τ, flim σ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Lf) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun j => ((hfc (φ j)).mono hsub).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun j => Eventually.of_forall fun σ hσ => by
        rw [Real.norm_eq_abs]; exact hfb _ σ (hsub hσ)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun σ hσ => hf σ (hsub hσ)
  have h2 : Tendsto (fun j => a (φ j) τ) atTop (𝓝 (c0 + ∫ σ in (0 : ℝ)..τ, flim σ)) := by
    have := (hc.comp hφ.tendsto_atTop).add hlim
    refine this.congr (fun j => ?_)
    rw [hid (φ j) τ hτ]
    rfl
  exact tendsto_nhds_unique (ha τ hτ) h2

end HRS.Whole.AppendixA.Phase2SA16R
