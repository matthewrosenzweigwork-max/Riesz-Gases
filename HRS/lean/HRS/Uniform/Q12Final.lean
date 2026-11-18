import HRS.Uniform.Q12W7
import HRS.Uniform.Q12P18
import HRS.Uniform.Comparison

/-!
# Q12, final: Peyre's inequality and Lemma 3.23 (`energy_W2`)

`HRS/Uniform/Comparison.lean` cannot import this file (it imports the `Comparison` module through
`Q12W*`), so the proof of `HRS.Uniform.energy_W2` is stated verbatim here as `energy_W2_proof`, together
with a type-check `example` that it has exactly the type of `HRS.Uniform.energy_W2`.
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_hmSum_nonneg (f g : Torus d → ℝ) : 0 ≤ hmSum f g := by
  unfold hmSum
  refine tsum_nonneg fun k => ?_
  split_ifs
  · exact le_rfl
  · positivity

/-- Peyre's inequality with constant `1/2`. -/
theorem q12_peyre (d : ℕ) : PeyreW2 d := by
  refine ⟨1 / 2, by norm_num, fun f g hf hg hfs hgs hfpos m hm hgm => ?_⟩
  obtain ⟨u, hus, hlap, hE⟩ := q12_poisson hf hg hfs hgs
  let D : PeyreData d := ⟨f, g, u, m, hm, hf, hg, hfs, hgs, hus, hfpos, hgm, hlap⟩
  have h1 : torusWassersteinE 2 (withDensityReal g) (withDensityReal f) ≤
      ENNReal.ofReal (Real.sqrt (π ^ 2 * D.energy / m)) := D.W2_data
  have hen : D.energy = hmSum f g / (4 * π ^ 2) := by
    rw [D.energy_eq]; exact hE
  have hH := q12_hmSum_nonneg f g
  have hval : Real.sqrt (π ^ 2 * D.energy / m) = 1 / 2 / Real.sqrt m * Real.sqrt (hmSum f g) := by
    rw [hen]
    have hπ : (0 : ℝ) < π := Real.pi_pos
    have : π ^ 2 * (hmSum f g / (4 * π ^ 2)) / m = (1 / 2) ^ 2 * (hmSum f g / m) := by
      field_simp; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), Real.sqrt_div hH]
    ring
  rw [hval] at h1
  exact (q12_W_symm 2 (withDensityReal f) (withDensityReal g)).trans h1

/-- Lemma 3.23, statement of `HRS/Uniform/Comparison.lean` verbatim. -/
theorem energy_W2_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ m₀ : ℝ) (hm₀ : 0 < m₀) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → (∀ x, m₀ ≤ ρ x) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N ∧
        torusWassersteinE 2 (empirical X) (withDensityReal ρ) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) ^ ((1 : ℝ) / max 2 ((d : ℝ) - s)))) :=
  energy_W2_of_peyre (q12_peyre d) hd s hs0 hsd Λ m₀ hm₀

example := (@energy_W2_proof : type_of% @HRS.Uniform.energy_W2)

end HRS.Uniform.Q12

#print axioms HRS.Uniform.Q12.energy_W2_proof
#print axioms HRS.Uniform.Q12.q12_peyre
