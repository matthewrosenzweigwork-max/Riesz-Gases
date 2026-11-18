import HRS.MS.S116P02
import HRS.MS.S116P03
import HRS.MS.S116P05
import HRS.MS.R2ObsAux1

/-!
# S11.6 packet P06 (`R26-T8B.P06`): terminal-time continuity at every oscillator index

Prefix `s116_`, namespace `HRS.MS.S116`.  Stationary branch: native `s910_hcont`.  Nonlinear branch: continuity at the base index (`s116_base_continuity`, P02),
the scalar relation `φ_{m,α} = λ_α^{(n-m)/2} φ_{n,α}` (P03) and homogeneity of the propagator (P05; existence at the base datum from the `ex` clause of `S104bTermRegGen`).
No restriction on `m` is used.
-/

set_option autoImplicit false

noncomputable section

namespace HRS.MS.S116

open HRS HRS.Whole HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem s116_all_order_continuity {d : ℕ} (hd : 2 ≤ d) {a β εstar c₁ C₁ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d 0 a β ρβ)
    (hR : HRS.MS.R2WinErr.S104bTermRegGen d 0 a β ρβ εstar c₁ C₁)
    (ρ : ℝ → Euc d → ℝ) (htraj : IsR2WindowTrajectory d 0 a β ρβ εstar c₁ C₁ ρ)
    (T : ℝ) (hT : 0 < T) (m : ℕ)
    (hex : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∃ f : ℝ → Euc d → ℝ, IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t
        (oscTestFun (m : ℝ) α) f) :
    ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t
        (oscTestFun (m : ℝ) α) x) (Set.Icc (0 : ℝ) T) := by
  intro α x
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rcases htraj with h | ⟨ε, ψ, hadm, hres⟩
  · subst h
    exact HRS.MS.R2Obs.s910_hcont hd (s := 0) le_rfl hsd ha hβ T hρβ (hex α T ⟨hT.le, le_rfl⟩) x
  · set n : ℝ := ((wholeSpaceIndex d : ℕ) : ℝ) with hn
    set c : ℝ := oscEigenvalue d α ^ ((n - (m : ℝ)) / 2) with hc
    have hbase := s116_base_continuity hR ε ψ ρ hadm hres T hT.le α x
    refine ((continuousOn_const (c := c)).mul hbase).congr (fun t ht => ?_)
    obtain ⟨hex0, -, -⟩ := hR ε ψ ρ hadm hres α T hT.le
    have hexn := hex0 0 t ht
    have hexn' : ∃ f : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t (oscTestFun n α) f := by
      obtain ⟨f, hf⟩ := hexn
      exact ⟨f, hf⟩
    have hsm := s116_propagator_smul hd ha hβ hρβ hadm hres t ht.1 (oscTestFun n α) hexn' c
    rw [s116_osc_rescale (m : ℝ) n α, hsm]
    rfl

end HRS.MS.S116

end
