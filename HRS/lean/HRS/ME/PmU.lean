import HRS.ME.ParxU
import HRS.Equilibrium.PoleCavity

/-!
# Packet PU0 (uniform hypotheses for the pair-moment estimates)

`RhoU d βm βp c₀ Λ₀ β ρ` collects the hypotheses on `(β, ρ)` that the pair-moment estimates
(`pair_moments_proof` and its dependency tree) use: `β ∈ [βm, βp]` with `βm > 0`, the density `ρ` is a
smooth positive probability density (`SmoothPosDensity`), and `c₀ ≤ ρ ≤ Λ₀` pointwise.  The parameters
`βm, βp, c₀, Λ₀` are fixed before `β` and `ρ`; every uniform lemma in the stage chooses its constant after
`d, s, βm, βp, c₀, Λ₀` and before `β, ρ`.

`rhoU_exists` produces `c₀, Λ₀` for all thermal densities at `β ∈ [βm, βp]` (from `parxU_of_eqevo`).
-/

noncomputable section

open Set

namespace HRS.ME.PmU

variable {d : ℕ}

/-- The standing hypotheses on `(β, ρ)` for the uniform pair-moment estimates. -/
structure RhoU (d : ℕ) (βm βp c₀ Λ₀ : ℝ) (β : ℝ) (ρ : Torus d → ℝ) : Prop where
  hβm : 0 < βm
  hβ : β ∈ Icc βm βp
  hc₀ : 0 < c₀
  rho : HRS.SmoothPosDensity ρ
  hlow : ∀ x, c₀ ≤ ρ x
  hup : ∀ x, ρ x ≤ Λ₀

theorem RhoU.hβpos {βm βp c₀ Λ₀ β : ℝ} {ρ : Torus d → ℝ} (U : RhoU d βm βp c₀ Λ₀ β ρ) : 0 < β :=
  lt_of_lt_of_le U.hβm U.hβ.1

theorem RhoU.hβle {βm βp c₀ Λ₀ β : ℝ} {ρ : Torus d → ℝ} (U : RhoU d βm βp c₀ Λ₀ β ρ) : β ≤ βp :=
  U.hβ.2

theorem RhoU.hβge {βm βp c₀ Λ₀ β : ℝ} {ρ : Torus d → ℝ} (U : RhoU d βm βp c₀ Λ₀ β ρ) : βm ≤ β :=
  U.hβ.1

/-- The constants `c₀, Λ₀` (with `1 ≤ Λ₀`) for which every thermal density at `β ∈ [βm, βp]` satisfies
`RhoU`, chosen before `β` and `ρ`. -/
theorem rhoU_exists (hd : 2 ≤ d) (s βm βp : ℝ) (hs : s = (d : ℝ) / 2) (hsd : s < d)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) :
    ∃ c₀ Λ₀ : ℝ, 0 < c₀ ∧ 1 ≤ Λ₀ ∧ ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.IsThermalDensity (HRS.periodicRiesz d s) V β ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
        RhoU d βm βp c₀ Λ₀ β ρ := by
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hs]; positivity
  obtain ⟨c₀, Λ₀, hc₀, hU⟩ := HRS.ME.ParxU.parxU_of_eqevo hd s βm βp hs hs0 hsd hβm hββ V hV 0
    (6 * d + 30) (by omega)
  refine ⟨c₀, max Λ₀ 1, hc₀, le_max_right _ _, fun β hβ ρ hρ hsm hpos => ?_⟩
  have U := hU β hβ ρ hρ hsm hpos
  exact ⟨hβm, hβ, hc₀, ⟨hρ.1, hsm, hpos⟩, U.rho_ge, fun x => (U.rho_le x).trans (le_max_left _ _)⟩

end HRS.ME.PmU
