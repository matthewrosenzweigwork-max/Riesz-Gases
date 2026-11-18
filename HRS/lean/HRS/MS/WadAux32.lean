import HRS.MS.WadAux31
import HRS.MS.FeatDecAux12
import HRS.MS.WsStatAux5

/-!
# S8.3, packet D7a (Route A): existence of the classical adjoint solutions for Schwartz data

`s84_exists_adjoint`: for the thermal density `ρβ` of the critical quadratic model and every Schwartz
terminal datum `f` there is a classical adjoint solution `IsClassicalAdjointW (critCoeff d a β ρβ) t f w` on
`[0,t]`, `0 ≤ t ≤ T`.  (Reduction of the frozen `critCoeff` to the fixed-viscosity coefficient of S5.1 and
`s85_witness5`; `C_c^∞ ⊂ 𝒮`.)  Together with `s84_apriori_classical` this is the existence/boundedness half of
the extension of `U_t` from `C_c^∞` to `C_M`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul HRS.MS.S85 HRS.MS.S52B

variable {d : ℕ}

theorem s84_exists_adjoint (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {T : ℝ} (hT : 0 ≤ T)
    (f : SchwartzMap (Euc d) ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ w : ℝ → Euc d → ℝ, IsClassicalAdjointW (critCoeff d a β ρβ) t (⇑f) w := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < (d : ℝ) := by linarith
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hρS : IsSchwartzDensity ρβ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ]
    exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by
    simp [Matrix.IsSymm]
  have hcoeff : critCoeff d a β ρβ =
      (⟨(d : ℝ) / 2, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff
        (fun _ => ρβ) := by
    unfold critCoeff
    rw [HRS.MS.S21.s21_dyn_eq]
  obtain ⟨θ, hθ⟩ := s52b_exists_ulCutoff d
  obtain ⟨K, hK⟩ := s85_witness5 hd ((d : ℝ) / 2) hs0 hsd θ hθ 5 le_rfl T β⁻¹ (a • 1) (-1) 0 ρβ hT hν hQ hρS
  set k : ℕ := 5 + 1 + ⌈(d : ℝ) / 2⌉₊ with hk
  obtain ⟨Cu, hCu0, hCu⟩ := ul6_ul_of_S (d := d) hθ k
  obtain ⟨C1, hC10, hC1⟩ := s52b_schwartz_S (d := d) ((d : ℝ) / 2) k
  have hφ : ContDiff ℝ ((5 + 1 + ⌈(d : ℝ) / 2⌉₊ : ℕ) : WithTop ℕ∞) (⇑f) := s85_cdiff_nat (f.smooth _) _
  have hul : ulNormE k θ (⇑f) < ⊤ := by
    have := hCu (-((d : ℝ) / 2 + 1)) (C1 * oscNorm ((s52bIdx d ((d : ℝ) / 2) k : ℕ) : ℝ) f) f
      (by linarith) (f.smooth _) (hC1 f)
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  rw [hcoeff]
  exact (hK t t ht.1 le_rfl ht.2 _ hφ hul).1

end HRS.MS.Wad
