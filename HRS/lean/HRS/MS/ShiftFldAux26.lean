import HRS.MS.ShiftFldAux25

/-!
# S79P: classical solutions and time translation for the Hermite data of the stationary coefficient
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MS.Ul HRS.MS.S52B HRS.MS.S85 HRS.MS.UlW HRS.MS.Go
open HRS (Euc)

variable {d : ℕ}

theorem s79g_Cst_eq (s a β : ℝ) :
    Cst d s a β = fixedViscosityCoeff s (-1) (a • (1 : Matrix (Fin d) (Fin d) ℝ)) β⁻¹
      (s85c s (thermalDensity d s a β)) (thermalDensity d s a β) := by
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  unfold Cst
  rw [s21_dyn_eq]
  exact s85_coeff_fv _ hQ _

/-- Existence of the classical solution with Hermite datum, and its identification with `propagatorW`. -/
theorem s79g_classical (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (m : ℝ) (α : MultiIndex d) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ u, IsClassicalAdjointW (Cst d s a β) τ (oscTestFun m α) u ∧
      ∀ r ∈ Icc (0 : ℝ) τ, propagatorW (Cst d s a β) r τ (oscTestFun m α) = u r := by
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  have hρS := s21_schwartz_thermal hd hs0 hsd ha hβ
  have hcoef := s79g_Cst_eq (d := d) s a β
  obtain ⟨⟨f, hf⟩, -⟩ := s85_exists_adjoint hd hs0 hsd (inv_pos.2 hβ)
    (a • (1 : Matrix (Fin d) (Fin d) ℝ)) hQ hρS τ hτ m α τ ⟨hτ, le_rfl⟩
  have hf' : IsClassicalAdjointW (Cst d s a β) τ (oscTestFun m α) f := by
    rw [hcoef, ← s85_coeff_fv _ hQ]
    exact hf
  refine ⟨f, hf', fun r hr => ?_⟩
  rw [hcoef] at hf' ⊢
  exact s21_prop_eq_classical hd hs0 hsd (inv_pos.2 hβ) _ hQ hρS τ ⟨hτ, le_rfl⟩ hf' r hr

theorem s79g_translate (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (m : ℝ) (α : MultiIndex d) {T r σ : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (hrσ : r ≤ σ)
    (hσT : σ ≤ T) :
    propagatorW (Cst d s a β) r σ (oscTestFun m α) =
      propagatorW (Cst d s a β) 0 (σ - r) (oscTestFun m α) := by
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    unfold Matrix.IsSymm; simp
  have hρS := s21_schwartz_thermal hd hs0 hsd ha hβ
  rw [s79g_Cst_eq]
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  have O : UlOrb d s β⁻¹ (thermalDensity d s a β) (fun _ => 0) (s85c s (thermalDensity d s a β)) θ :=
    ⟨hd, hs0, hsd, inv_pos.2 hβ, hρS.2, s85_sigma d, rfl, hθ⟩
  set K : ℕ := ⌊(4 : ℝ) + (d : ℝ) / 2⌋₊ + 1 with hKdef
  have hK : (4 : ℝ) + (d : ℝ) / 2 < K := by
    rw [hKdef]; push_cast; exact Nat.lt_floor_add_one _
  obtain ⟨f, hf, -⟩ := s52b_phi (d := d) m α
  have hφ0 : UlClosure K θ (oscTestFun m α) := by
    have := ul6_closure O (a • (1 : Matrix (Fin d) (Fin d) ℝ)) f 0 K
    rw [← hf]; exact this
  exact s21_shift hd hs0 hsd (inv_pos.2 hβ) _ hQ hρS T hT hθ hK hφ0 r σ hr hrσ hσT

end HRS.MS.S79G
