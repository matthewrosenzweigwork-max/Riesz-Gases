import HRS.Equilibrium.Parametrix.Assembly
import HRS.Equilibrium.Parametrix.PXFIDAuxQ
import HRS.Equilibrium.Parametrix.PXFIDTAuxE

/-!
# Proposition 4.13 with all clauses (packet PX-FID)

`pair_poisson_full_proof` is the frozen spec `HRS.pair_poisson_full`.

* The conclusions of `pair_poisson` are those of `pair_poisson_proof` (same `Ψ`).
* The distributional clause (`IsWeakPairPoisson`) is proved for **every** pair corrector, by
  `HRS.Parx.PXFID.weak_of_corrector` (`PXFIDAuxQ.lean`): off the diagonal the equation holds
  pointwise, and the integrations by parts have no diagonal flux (`PXFIDAuxG.lean`).
* The tangential clause (`PsiSize` of `tanIter es (Ψ f)`, `|es| ≤ 4`) is proved by `PXFIDTAuxA-E`
  (packet PX-FID-T) for `Ψ f = ψ^loc + Ψ_{R_L}` with the Sobolev level `a = ⌊d/2⌋ + 7` of the pair
  inverse (`C^6` output needs `d + 12 < 2a`, input `C^{2a}`), the gap lemma at `J = 2a - 1`
  (`R_L ∈ C^{J+1} = C^{2a}` with one more conormal derivative, `σ_L = -J-3`), and the closure of the
  conormal classes under `∂_X` (a tangential derivative costs one conormal derivative).  The index is
  `K = parxK d J + 1 = 10⌊d/2⌋ + 2d + 81 ≤ 7d + 81 ≤ 8d + 80`.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

section Critical

theorem pair_poisson_full_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ (Ψ : (Torus d → ℝ) → Torus d → Torus d → ℝ) (C : ℝ),
      (∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
        Ψ (a • f + b • f') = a • Ψ f + b • Ψ f') ∧
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        IsPairCorrector d s V β ρ f (C * posSeminorm (8 * d + 80) f) (Ψ f) ∧
        (∃ M : ℝ, ∀ x, |aCoef d s ρ f x| ≤ M) ∧
        eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * posSeminorm (8 * d + 80) f) ∧
        (∀ es : List (Euc d), es.length ≤ 4 →
          PsiSize s (C * posSeminorm (8 * d + 80) f * (es.map fun e => ‖e‖).prod)
            (tanIter es (Ψ f))) ∧
        IsWeakPairPoisson d s β ρ f (Ψ f) := by
  have H : Parx.PXFID.FidHyp d s V β ρ := ⟨hd, hcrit, hβ, hV, hρ, hρs⟩
  have H' : Parx.ParxHyp d s V β ρ := ⟨hd, hcrit, hβ, hV, hρ, hρs⟩
  -- Sobolev level `a = ⌊d/2⌋ + 7` and `J = 2a - 1`
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌊(d : ℝ) / 2⌋₊ := ⟨_, rfl⟩
  have hq1 : 2 * q ≤ d := by
    have h : (q : ℝ) ≤ (d : ℝ) / 2 := by rw [hq]; exact Nat.floor_le (by positivity)
    have : (2 * q : ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hq2 : (d : ℝ) / 2 < (q : ℝ) + 1 := by rw [hq]; exact Nat.lt_floor_add_one _
  have hpm : PDE.PX7.px7_m d = q + 5 := by rw [hq]; rfl
  set J : ℕ := 2 * q + 13 with hJ
  have hspec : Parx.PairInverseSpec H' J :=
    PDE.PX7.px7_spec H'.two_le s H'.s_nonneg H'.s_lt β H'.beta_pos V H'.V_smooth ρ H'.thermal
      H'.rho_smooth.smooth H'.rho_smooth.pos J (by rw [hpm]; omega)
  have h6 : ∃ C6 : ℝ, 0 ≤ C6 ∧ ∀ R : Torus d → Torus d → ℝ, PDE.IsCk2 (J + 1) R →
      PDE.IsCk2 6 (PDE.pairInverse H'.dyn ρ R) ∧
      PDE.cbNorm2 6 (PDE.pairInverse H'.dyn ρ R) ≤ C6 * PDE.cbNorm2 (J + 1) R := by
    obtain ⟨Cinv, hC0, hC⟩ := PDE.PX7.pxfidt_inv_Cn_spec (d := d) (by omega) s H'.s_nonneg H'.s_lt β
      H'.beta_pos V H'.V_smooth ρ H'.thermal H'.rho_smooth.smooth H'.rho_smooth.pos (q + 7)
      (by rw [hpm]; omega) 6 (by push_cast; linarith)
    refine ⟨Cinv, hC0, fun R hR => ?_⟩
    have e : q + 7 + (q + 7) = J + 1 := by rw [hJ]; omega
    rw [e] at hC
    exact hC R hR
  obtain ⟨Ψ, C, hlin, hf⟩ := Parx.PXFIDT.fidt_gen H' J hspec h6 (by rw [hJ]; omega) (8 * d + 80)
    (by unfold Parx.parxK; rw [hJ]; omega)
  refine ⟨Ψ, C, hlin, fun f hfs => ⟨(hf f hfs).1, (hf f hfs).2.1, (hf f hfs).2.2.1,
    (hf f hfs).2.2.2, Parx.PXFID.weak_of_corrector H (hf f hfs).1⟩⟩

example := (@pair_poisson_full_proof : type_of% @HRS.pair_poisson_full)

end Critical

end HRS

end
