/-
# HRS.Equilibrium.Q84eAuxH — packet Q84e: the pointwise normal form off collisions

`(√N/2) D_μ(h_f)(X) = -𝓛F_N(ψ)(X) + E_N(ψ)(X) - (2/N)√N μ_N(a_f)(X) + c₀/(2√N)` for `X ∉ collisionSet`
(`Q:eq:lifted-generator`, `Q:eq:pair-poisson`, `Q:eq:deleted-canonical`, source lines 4943-4962).
-/
import HRS.Equilibrium.Q84eAuxG

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84e_pointwise (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hβ : 0 < β) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ)
    (hN : 2 ≤ N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    Real.sqrt N / 2 * quadStat (hTransport d s f) (withDensityReal ρ) X =
      -particleGen d s V β (Fstat ψ) X + errStat d s ρ ψ X -
        (2 / (N : ℝ)) * (Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (X i))) +
        (1 / (2 * Real.sqrt N)) *
          ∫ x', ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have h1 := q84e_gen_alg hN hsd V β ρ hψ.symm hψ.size.smooth X hXne
  have h2 : pairSumOrdered (fun x y =>
      Bop d s V β ρ (fun z => ψ z y) x + Bop d s V β ρ (fun z => ψ z x) y + Jpair d s ρ ψ x y) X =
      -pairSumOrdered (Hsource d s ρ f) X := by
    unfold pairSumOrdered
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact q84e_poisson_red hd hcrit hβ hV hρ hρs hψ _ _ (hXne i j (Finset.ne_of_mem_erase hj).symm)
  rw [h2] at h1
  have h3 := q84e_quad_alg (by omega : 1 ≤ N) hsd ρ f X
  unfold Fstat at h3
  rw [h3]
  linarith

end HRS.Q84e

end
