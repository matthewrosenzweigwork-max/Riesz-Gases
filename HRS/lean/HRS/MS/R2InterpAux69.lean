import HRS.MS.R2InterpAux68
import HRS.MS.FeatDecAux12
import HRS.MS.WsStatAux6
import HRS.MS.OrbFeatAux1

/-!
# S10.2 (worker S102), part 69: existence of classical adjoint solutions for Schwartz data (general `0 ≤ s < d/2`) and linearity of the propagator

Port of `s84_exists_adjoint` (critical `s = d/2`) to the Hilbert--Schmidt range, for the quadratic stationary coefficient.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S85 HRS.MS.S52B

variable {d : ℕ}

theorem s102_exists_adjoint (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 ≤ T)
    (f : SchwartzMap (Euc d) ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ w : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t (⇑f) w := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hρS : IsSchwartzDensity ρ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  obtain ⟨K, hK⟩ := s85_witness5 hd s hs0 hsd θ hθ 5 le_rfl T β⁻¹ (a • 1) (-1) 0 ρ hT hν hQ hρS
  set k : ℕ := 5 + 1 + ⌈(d : ℝ) / 2⌉₊ with hk
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S (d := d) hθ k
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) ((d : ℝ) / 2) k
  have hφ : ContDiff ℝ ((5 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (⇑f) := s85_cdiff_nat (f.smooth _) _
  have hul : ulNormE k θ (⇑f) < ⊤ := by
    have := hCu (-((d : ℝ) / 2 + 1)) (C1 * oscNorm ((s52bIdx d ((d : ℝ) / 2) k : ℕ) : ℝ) f) f
      (by linarith) (f.smooth _) (hC1 f)
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  rw [HRS.MS.S21.s21_dyn_eq]
  exact (hK t t ht.1 le_rfl ht.2 _ hφ hul).1

end HRS.MS.R2Interp

end
