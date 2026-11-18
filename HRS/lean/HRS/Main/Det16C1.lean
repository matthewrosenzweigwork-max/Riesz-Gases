import HRS.Main.Det16A1
import HRS.Main.Det16A2
import HRS.Main.Det16A4

/-!
# Example A.16, lemma L4 (part 1): the pathwise energy bound for the selected flows

Bookkeeping around `det16_pathwise_energy` (L3) and `det16_energy_N1_bdd` (L2): from the selected flows of
a zero-temperature sequence, `invβ_N = 0`, we get case (a) of `SelectedFlowA1.flow` (an `IsStrongSolution`),
hence the a.s. bound `sup_t F_N^C₀(X^t) ≤ e^{C T Λ'} F_N^C₀(X^0)`, `X^0 = Y_N` a.s.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

variable {d : ℕ}

/-- The density bound `ρ_N^t ≤ Λ` from `MeanFieldRegularity`. -/
theorem det16c_rho_le {S : MainData d} {r : ℕ} {Λ : ℝ} (hmf : MeanFieldRegularity S r Λ) {N : ℕ}
    (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (x : Torus d) : S.ρ N t x ≤ Λ := by
  have hreg := ((hmf.regular N hN).1 t ht)
  have h := HRS.GF.gfb2_sup_le_cbNorm hreg.1 x
  exact (le_abs_self _).trans (h.trans hreg.2)

/-- With `invβ_N = 0`, the selected flow is a strong solution (case (a) of A.1). -/
theorem det16c_strong {S : MainData d} (hβ : ∀ N, S.invβ N = 0) {R : ∀ N, Realization d N}
    (hflow : SelectedFlows S R) {N : ℕ} (hN : 1 ≤ N) :
    IsStrongSolution (R N).P (S.dyn N) S.T (R N).X₀ (R N).W (R N).X := by
  have h0 : (S.dyn N).invβ = 0 := hβ N
  rcases (hflow N hN).flow with ⟨h, -⟩ | ⟨-, -, hpos, -⟩ | ⟨-, -, hpos, -⟩
  · exact h
  · rw [h0] at hpos; exact absurd hpos (lt_irrefl _)
  · rw [h0] at hpos; exact absurd hpos (lt_irrefl _)

theorem det16c_energy_bounds (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀min C : ℝ, 0 ≤ C₀min ∧ 0 < C ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : MainData d), S.s = s → (∀ N, S.invβ N = 0) →
    ∀ (R : ∀ N, Realization d N), SelectedFlows S R →
    ∀ {r : ℕ} {Λ : ℝ}, 3 ≤ r → MeanFieldRegularity S r Λ → Torus.IsCk 2 S.V →
    Torus.SymNonpos S.M →
    ∀ Λ' : ℝ, (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    ∀ (Y : ∀ N, Config d N), (∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P, (R N).X₀ ω = Y N) →
      (∀ N : ℕ, 2 ≤ N → ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t ≤
          Real.exp (C * S.T * Λ') * correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) ∧
      (∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ X : Config d 1,
        correctedEnergy (S.dyn 1) C₀ Λ (S.ρ 1) X t ≤ B) := by
  obtain ⟨C₀min, C, hC₀, hC, hpe⟩ := det16_pathwise_energy hd hs0 hsd
  refine ⟨C₀min, C, hC₀, hC, fun C₀ hC₀' S hSs hβ R hflow r Λ hr hmf hV hsym Λ' hΛ' Y hdet => ⟨?_, ?_⟩⟩
  · intro N hN
    have hN1 : 1 ≤ N := by omega
    have hΛ1 : 1 ≤ Λ := det16_Lam_ge_one hmf
    have hsol := det16c_strong hβ hflow hN1
    have hreg := (hmf.regular N hN1).1
    have hb := hpe C₀ hC₀' (S.dyn N) hSs (hβ N) hsym hV N hN S.T S.hT.le (S.ρ N) r Λ hr hΛ1
      (hmf.solution N hN1) hreg Λ' (hΛ' N hN1) (R N).P (R N).X₀ (R N).W (R N).X hsol
    filter_upwards [hb, hsol.init, hdet N hN1] with ω h1 h2 h3
    intro t ht
    have h4 := h1 t ht
    rw [h2, h3] at h4
    exact h4
  · obtain ⟨B, hB⟩ := det16_energy_N1_bdd hd hs0 hsd C₀ Λ (by linarith [det16_Lam_ge_one hmf])
    refine ⟨B, fun t ht X => ?_⟩
    exact hB (S.dyn 1) hSs (S.ρ 1) t ((hmf.solution 1 le_rfl).density t ht)
      (fun x => det16c_rho_le hmf le_rfl ht x) X

end HRS.Main.Det16
