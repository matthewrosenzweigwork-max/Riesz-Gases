import HRS.Uniform.Q48bAux5

/-!
# Q48b: exponential decay of the frozen dual evolution on `E_m` (infrastructure for Lemma 3.31 `stationary_noise`)

`HRS.Uniform.stationary_noise` constrains the dual evolution `Vev` only through
`IsDualEvolution (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev` with the frozen equilibrium density.  This file proves,
from exactly the hypotheses of `stationary_noise`, the decay estimate its proof needs:

```
theorem HRS.Uniform.Q48b.stationary_decay (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρ : Torus.IsSmooth ρβ) (hpos : ∀ x, 0 < ρβ x) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev →
        ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ C * Real.exp (-c * (t - u))
```

(`m₀ = d/2 + 7` works; `C, c` depend on `(d, s, β, V, ρβ, m)` only, not on `Vev`.)

Route: the constant path `ρ^t ≡ ρβ` is a solution of the mean-field equation (`Q48bAux1`), so Proposition 5.2
(`adjoint_decay_comparison`) applies at the even integers `j₁ ≤ m < j₂ = j₁ + 2` (`Q48bAux2`); duality against finite
trigonometric test functions turns the `H^j`-decay of the centered propagator into weighted `ℓ²` matrix bounds on
the matrix of `Vev t u` at the two levels `j₁, j₂` (`Q48bAux3`, `Q48bAux4`); Hadamard's three-lines theorem
interpolates them to the real level `m` (`Q48bInterp`); density of finite vectors gives the operator norm on `E_m`
(`Q48bAux5`).  The interpolation is needed because Proposition 5.2 is only stated for even integer `j`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48b

open HRS HRS.PDE HRS.Uniform

variable {d : ℕ}

theorem stationary_decay (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hth : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρ : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev →
        ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ C * Real.exp (-c * (t - u)) := by
  refine ⟨(d : ℝ) / 2 + 7, fun m hm => ?_⟩
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, (2 * n : ℝ) ≤ m ∧ m < 2 * n + 2 := by
    refine ⟨⌊m / 2⌋₊, ?_, ?_⟩
    · have := Nat.floor_le (show 0 ≤ m / 2 by linarith)
      linarith
    · have := Nat.lt_floor_add_one (m / 2)
      linarith
  have hj1 : (d : ℝ) / 2 + 4 < ((2 * n : ℕ) : ℝ) := by push_cast; linarith
  have hj2 : (d : ℝ) / 2 + 4 < ((2 * n + 2 : ℕ) : ℝ) := by push_cast; linarith
  have he1 : Even (2 * n) := even_two_mul n
  have he2 : Even (2 * n + 2) := ⟨n + 1, by ring⟩
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := q48b_prop52 hd s hs0 hsd β hβ V hV ρβ hth hρ hpos _ he1 hj1
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := q48b_prop52 hd s hs0 hsd β hβ V hV ρβ hth hρ hpos _ he2 hj2
  obtain ⟨K₁, hK₁0, hK₁⟩ := q48b_proj_test_bound ρβ hth.1 ((2 * n : ℕ) : ℝ)
    (by push_cast at hj1 ⊢; linarith)
  obtain ⟨K₂, hK₂0, hK₂⟩ := q48b_proj_test_bound ρβ hth.1 ((2 * n + 2 : ℕ) : ℝ)
    (by push_cast at hj2 ⊢; linarith)
  set θ : ℝ := (m - 2 * n) / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  set A₁ : ℝ := C₁ * (K₁ + 1) with hA₁
  set A₂ : ℝ := C₂ * (K₂ + 1) with hA₂
  have hA₁0 : 0 < A₁ := mul_pos hC₁ (by linarith)
  have hA₂0 : 0 < A₂ := mul_pos hC₂ (by linarith)
  refine ⟨A₁ ^ (1 - θ) * A₂ ^ θ, (1 - θ) * c₁ + θ * c₂,
    mul_pos (Real.rpow_pos_of_pos hA₁0 _) (Real.rpow_pos_of_pos hA₂0 _),
    by nlinarith, fun Vev hdual u t hu hut => ?_⟩
  set τ : ℝ := t - u with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hdualV : ∀ (z : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
      NegSobolev.eval (Vev t u z) φ =
        NegSobolev.eval z (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t φ) :=
    fun z φ hφ => hdual u t hu hut z φ hφ
  -- the two weighted bounds
  have W₁ : ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m (Vev t u)) S T
      (((2 * n : ℕ) : ℝ)) (A₁ * Real.exp (-c₁ * τ)) := by
    intro S T
    have hb := q48b_wbound_of_duality (m := m) (a := ((2 * n : ℕ) : ℝ)) ρβ
      (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t) (Vev t u) hdualV K₁ hK₁0 hK₁
      (C₁ * Real.exp (-c₁ * τ)) (by positivity) (fun φ hc hmem => by
        have := h₁ φ hc hmem u t hu hut
        exact ⟨this.1, this.2⟩) S T
    refine q48b_wbound_mono (by positivity) ?_ hb q48bW_pos
    have : C₁ * Real.exp (-c₁ * τ) * K₁ ≤ A₁ * Real.exp (-c₁ * τ) := by
      rw [hA₁]
      have := Real.exp_pos (-c₁ * τ)
      nlinarith [mul_pos hC₁ this]
    exact this
  have W₂ : ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m (Vev t u)) S T
      (((2 * n + 2 : ℕ) : ℝ)) (A₂ * Real.exp (-c₂ * τ)) := by
    intro S T
    have hb := q48b_wbound_of_duality (m := m) (a := ((2 * n + 2 : ℕ) : ℝ)) ρβ
      (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) u t) (Vev t u) hdualV K₂ hK₂0 hK₂
      (C₂ * Real.exp (-c₂ * τ)) (by positivity) (fun φ hc hmem => by
        have := h₂ φ hc hmem u t hu hut
        exact ⟨this.1, this.2⟩) S T
    refine q48b_wbound_mono (by positivity) ?_ hb q48bW_pos
    have : C₂ * Real.exp (-c₂ * τ) * K₂ ≤ A₂ * Real.exp (-c₂ * τ) := by
      rw [hA₂]
      have := Real.exp_pos (-c₂ * τ)
      nlinarith [mul_pos hC₂ this]
    exact this
  have hM₁ : 0 ≤ A₁ * Real.exp (-c₁ * τ) := by positivity
  have hM₂ : 0 ≤ A₂ * Real.exp (-c₂ * τ) := by positivity
  have hα : (((2 * n : ℕ) : ℝ)) + θ * ((((2 * n + 2 : ℕ) : ℝ)) - ((2 * n : ℕ) : ℝ)) = m := by
    rw [hθ]; push_cast; ring
  have hall : ∀ S T : Finset (NonzeroLattice d), WBound q48bW (q48bMat m (Vev t u)) S T m
      ((A₁ * Real.exp (-c₁ * τ)) ^ (1 - θ) * (A₂ * Real.exp (-c₂ * τ)) ^ θ) := by
    intro S T
    have := q48b_wbound_interp q48bW_pos hM₁ hM₂ (W₁ S T) (W₂ S T) θ hθ0 hθ1
    rwa [hα] at this
  have hnorm := q48b_opNorm_le (Vev t u) _ (by positivity) hall
  refine hnorm.trans (le_of_eq ?_)
  have e1 : Real.exp (-c₁ * τ) ^ (1 - θ) = Real.exp (-c₁ * τ * (1 - θ)) := (Real.exp_mul _ _).symm
  have e2 : Real.exp (-c₂ * τ) ^ θ = Real.exp (-c₂ * τ * θ) := (Real.exp_mul _ _).symm
  rw [Real.mul_rpow hA₁0.le (Real.exp_pos _).le, Real.mul_rpow hA₂0.le (Real.exp_pos _).le, e1, e2]
  have e3 : Real.exp (-c₁ * τ * (1 - θ)) * Real.exp (-c₂ * τ * θ) =
      Real.exp (-((1 - θ) * c₁ + θ * c₂) * (t - u)) := by
    rw [← Real.exp_add, hτ]; congr 1; ring
  calc A₁ ^ (1 - θ) * Real.exp (-c₁ * τ * (1 - θ)) * (A₂ ^ θ * Real.exp (-c₂ * τ * θ))
      = A₁ ^ (1 - θ) * A₂ ^ θ * (Real.exp (-c₁ * τ * (1 - θ)) * Real.exp (-c₂ * τ * θ)) := by ring
    _ = _ := by rw [e3]

end HRS.Uniform.Q48b
