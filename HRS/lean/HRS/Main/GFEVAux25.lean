import HRS.Main.GFEVAux24
import HRS.Main.GFB2Aux2

/-!
# Packet GFEVG, part 25: gluing lemmas for the final theorem
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfev_classical_congr {D : DynData d} {ρ μ' : ℝ → Torus d → ℝ} {T t : ℝ} (htT : t ≤ T)
    (hμ : ∀ r ∈ Set.Icc (0 : ℝ) T, μ' r = ρ r) (φ : Torus d → ℝ) :
    IsClassicalAdjointSolution D ρ t φ = IsClassicalAdjointSolution D μ' t φ := by
  funext f
  apply propext
  have hm : ∀ r ∈ Set.Icc (0 : ℝ) t, μ' r = ρ r := fun r hr => hμ r ⟨hr.1, hr.2.trans htT⟩
  constructor
  · intro h
    refine ⟨h.c2, h.cont_c2, h.terminal, fun x r hr => ?_, ?_⟩
    · have := h.time_deriv x r hr
      rwa [← hm r ⟨hr.1.le, hr.2.le⟩] at this
    · refine h.cont_time_deriv.congr fun p => ?_
      rw [hm p.1.1 p.1.2]
  · intro h
    refine ⟨h.c2, h.cont_c2, h.terminal, fun x r hr => ?_, ?_⟩
    · have := h.time_deriv x r hr
      rwa [hm r ⟨hr.1.le, hr.2.le⟩] at this
    · refine h.cont_time_deriv.congr fun p => ?_
      rw [← hm p.1.1 p.1.2]

theorem gfev_propagator_congr {D : DynData d} {ρ μ' : ℝ → Torus d → ℝ} {T t : ℝ} (htT : t ≤ T)
    (hμ : ∀ r ∈ Set.Icc (0 : ℝ) T, μ' r = ρ r) (φ : Torus d → ℝ) (r : ℝ) :
    propagator D ρ r t φ = propagator D μ' r t φ := by
  unfold propagator
  rw [gfev_classical_congr htT hμ φ]

theorem gfev_symNonpos_neg_one : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  unfold Torus.SymNonpos Torus.symPart
  simp only [Matrix.transpose_neg, Matrix.transpose_one]
  have : (-((1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + -1))) = 1 := by
    rw [← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
    norm_num
  rw [this]
  exact Matrix.PosSemidef.one

theorem gfev_mStar_le (d : ℕ) : mStar d ≤ 2 * d + 10 := by
  unfold mStar
  have : ⌊(d : ℝ) / 2⌋₊ ≤ d := by
    refine Nat.floor_le_of_le ?_
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  omega

end HRS.GF
