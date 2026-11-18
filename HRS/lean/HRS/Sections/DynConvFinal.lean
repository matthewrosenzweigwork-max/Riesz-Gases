import HRS.Sections.DynConvAux1
import HRS.Sections.Sec5

/-!
# DYNCONV final: relocated proofs

* `HRS.transport_bound_uniform_proof` (Proposition 3.41, last sentence), tied to the frozen statement.
* `dynamic_convergence_proof`: NOT proved (see the plan in `DynConvAux1`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem transport_bound_uniform_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (Λ lam₀ ΛV σ₀ : ℝ) (hlam₀ : 0 < lam₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : DynData d), D.s = s → 0 < D.invβ → D.invβ ≤ σ₀ →
        Torus.IsCk (PDE.mStar d + 2) D.V → Torus.cbNorm (PDE.mStar d + 2) D.V ≤ ΛV →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (PDE.mStar d + 2) ρ →
        Torus.cbNorm (PDE.mStar d + 2) ρ ≤ Λ → (∀ x, lam₀ ≤ ρ x) →
        HasTransportBound d s (mfeTransport D ρ) C := by
  obtain ⟨B, hB0, hB⟩ := dynconv_mfeTransport_cbNorm hd hs0 hsd Λ lam₀ ΛV σ₀ hlam₀
  have h1 : 1 ≤ PDE.mStar d + 1 := by omega
  have h2 : (d : ℝ) / 2 + 1 ≤ ((PDE.mStar d + 1 : ℕ) : ℝ) := by
    have h3 : (d : ℝ) / 2 < (⌊(d : ℝ) / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    unfold PDE.mStar
    push_cast
    linarith
  obtain ⟨cT, hcT0, hcT⟩ := dynconv_transport_of_cbNorm (d := d) (PDE.mStar d + 1) h1 h2
  refine ⟨cT * B, mul_nonneg hcT0 hB0, fun D hDs hβ hβ' hV hVb ρ _ hρ hρb hlow => ?_⟩
  obtain ⟨hu, hub⟩ := hB D hDs hβ hβ' hV hVb ρ hρ hρb hlow
  exact hcT s hs0 (mfeTransport D ρ) B hu hub

example := (@transport_bound_uniform_proof : type_of% @HRS.transport_bound_uniform)

end HRS
