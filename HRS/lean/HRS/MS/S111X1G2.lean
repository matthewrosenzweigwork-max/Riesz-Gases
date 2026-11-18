import HRS.MS.S111X1G1
import HRS.MS.FeatDecAux12
import HRS.MS.UlOrbitAux1
import HRS.MS.OrbFeatAux1
import HRS.MS.S111X1F2

/-!
# S11.1 X1: existence of classical adjoint solutions for oscillator test functions
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem ulNormE_lt_top_of_bdd {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (K : ℕ) {g : Euc d → ℝ}
    (hg : ContDiff ℝ ∞ g) {A : ℝ} (hb : ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ A) :
    ulNormE K θ g < ⊤ := by
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  obtain ⟨Ce, hCe, hequ⟩ := HRS.MS.Ul.ul_equiv K θ χ hθ hχ
  obtain ⟨Cc, hCc, hcb⟩ := HRS.MS.Ul.ulocNormE_le_cb K χ hχ
  have hmem : HRS.MemCb K g := ⟨hg.of_le (by exact_mod_cast le_top), fun j hj =>
    ⟨A, by rintro _ ⟨x, rfl⟩; exact hb j hj x⟩⟩
  have h1 := hcb g hmem
  calc ulNormE K θ g ≤ ENNReal.ofReal Ce * HRS.Whole.AppendixA.ulocNormE K χ g := (hequ g).1
    _ ≤ ENNReal.ofReal Ce * ENNReal.ofReal (Cc * HRS.cbNorm K g) := by gcongr
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem exist_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ClassicalExist d s a β ρ := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by
    rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by unfold Matrix.IsSymm; simp
  obtain ⟨θ, hθ⟩ := HRS.MS.S52B.s52b_exists_ulCutoff d
  intro t ht ψ hψ
  obtain ⟨K, hK⟩ := HRS.MS.S85.s85_witness5 hd s hs0 hsd θ hθ 5 le_rfl t β⁻¹
    (a • (1 : Matrix (Fin d) (Fin d) ℝ)) (-1) 0 ρ ht (inv_pos.2 hβ) hQ hSch
  set k : ℕ := 5 + 1 + ⌈(d : ℝ) / 2⌉₊ with hk
  have hceil : ⌈(d : ℝ) / 2⌉₊ ≤ d := Nat.ceil_le.2 (by linarith)
  have hceil' : (⌈(d : ℝ) / 2⌉₊ : ℝ) ≤ d := by exact_mod_cast hceil
  have hceil2 : (d : ℝ) / 2 ≤ ⌈(d : ℝ) / 2⌉₊ := Nat.le_ceil _
  obtain ⟨A, hA⟩ := osc_deriv_bdd (m := (wholeSpaceIndex d : ℝ)) (n := k + d) (K := k) (ψ := ψ)
    (by rw [hk]; push_cast; linarith) (by
      rw [hk]; unfold wholeSpaceIndex; push_cast; linarith) hψ.1 hψ.2
  have hul : ulNormE k θ ψ < ⊤ := ulNormE_lt_top_of_bdd hθ k hψ.1 hA
  have hcd : ContDiff ℝ (k : WithTop ℕ∞) ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have := (hK 0 t le_rfl ht le_rfl ψ hcd hul).1
  rw [x1C_eq]
  exact this

end HRS.MS.S111X1
