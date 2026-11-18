import HRS.MS.MovSchAux10

/-!
# S64 (S6.9), part 6: `movPartial` along coordinate lines; reduction of `movFP` to one-dimensional calculus

Namespace `HRS.MS.MovSch`, prefix `s64_`.  `s64_ell X i k τ = update X i (X i + τ e_k)` is the line through `X` in the direction of the
`k`-th coordinate of the `i`-th particle.  The key observation: `movPartial f i k (ℓ(τ)) = φ'(τ)` for `φ(τ) = f(ℓ(τ))` (without any
differentiability hypothesis), hence `movPartial (movPartial f i k) i k X = φ''(0)` and
`movFP f X = ∑_{i,k} (β⁻¹ φ_{ik}''(0) + (φ_{ik} ψ_{ik})'(0))` with `ψ_{ik}(τ) = drift_{ik}(ℓ(τ))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- The line through `X` along the `k`-th coordinate of particle `i`. -/
def s64_ell (X : EucConfig d N) (i : Fin N) (k : Fin d) (τ : ℝ) : EucConfig d N :=
  Function.update X i (X i + τ • EuclideanSpace.single k (1 : ℝ))

lemma s64_ell_apply (X : EucConfig d N) (i : Fin N) (k : Fin d) (τ : ℝ) (j : Fin N) :
    s64_ell X i k τ j = X j + τ • (if j = i then EuclideanSpace.single k (1 : ℝ) else 0) := by
  unfold s64_ell
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, h]

lemma s64_ell_zero (X : EucConfig d N) (i : Fin N) (k : Fin d) : s64_ell X i k 0 = X := by
  funext j; rw [s64_ell_apply]; simp

lemma s64_ell_ell (X : EucConfig d N) (i : Fin N) (k : Fin d) (τ σ : ℝ) :
    s64_ell (s64_ell X i k τ) i k σ = s64_ell X i k (τ + σ) := by
  funext j
  rw [s64_ell_apply, s64_ell_apply, s64_ell_apply]
  by_cases h : j = i
  · simp [h, add_smul, add_assoc]
  · simp [h]

lemma s64_movPartial_def (f : EucConfig d N → ℝ) (i : Fin N) (k : Fin d) (X : EucConfig d N) :
    movPartial f i k X = deriv (fun τ : ℝ => f (s64_ell X i k τ)) 0 := rfl

lemma s64_movPartial_ell (f : EucConfig d N → ℝ) (i : Fin N) (k : Fin d) (X : EucConfig d N) (τ : ℝ) :
    movPartial f i k (s64_ell X i k τ) = deriv (fun σ : ℝ => f (s64_ell X i k σ)) τ := by
  rw [s64_movPartial_def]
  have : (fun σ : ℝ => f (s64_ell (s64_ell X i k τ) i k σ)) =
      fun σ => (fun σ' : ℝ => f (s64_ell X i k σ')) (τ + σ) := by
    funext σ; rw [s64_ell_ell]
  rw [this]
  have h := deriv_comp_const_add (a := τ) (x := (0 : ℝ)) (f := fun σ' : ℝ => f (s64_ell X i k σ'))
  simpa using h

lemma s64_movPartial2 (f : EucConfig d N → ℝ) (i : Fin N) (k : Fin d) (X : EucConfig d N) :
    movPartial (movPartial f i k) i k X =
      deriv (deriv (fun σ : ℝ => f (s64_ell X i k σ))) 0 := by
  rw [s64_movPartial_def]
  congr 1
  funext τ
  exact s64_movPartial_ell f i k X τ

/-- The drift coordinate `q y_{ik} + N⁻¹ ∑_{j≠i} ∂_kg(y_i - y_j)` of `movFP`. -/
def s64_drift (d : ℕ) (s q : ℝ) (N : ℕ) (i : Fin N) (k : Fin d) (Y : EucConfig d N) : ℝ :=
  q * Y i k + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, rieszKernelGrad d s (Y i - Y j) k

lemma s64_movFP_eq (s q β : ℝ) (f : EucConfig d N → ℝ) (X : EucConfig d N) :
    movFP d s q β N f X = ∑ i, ∑ k, (β⁻¹ * deriv (deriv (fun σ : ℝ => f (s64_ell X i k σ))) 0 +
      deriv (fun τ : ℝ => f (s64_ell X i k τ) * s64_drift d s q N i k (s64_ell X i k τ)) 0) := by
  unfold movFP
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [s64_movPartial2]
  rfl

end HRS.MS.MovSch

end
