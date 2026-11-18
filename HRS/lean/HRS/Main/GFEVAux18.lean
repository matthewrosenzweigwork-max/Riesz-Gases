import HRS.Main.GFEVAux17

/-!
# Packet GFEVG, part 18: the core `D ⊂ E_γ`, the operator `A`, and the abstract data `GFAbs`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfev_le4 (γ : ℕ) : (γ : ℝ) - 4 ≤ γ := by linarith
theorem gfev_le42 (γ : ℕ) : (γ : ℝ) - 4 ≤ (γ : ℝ) - 2 := by linarith
theorem gfev_le2 (γ : ℕ) : (γ : ℝ) - 2 ≤ γ := by linarith

/-- The core: the image of `E_{γ-4}` in `E_γ`. -/
def gfevD (d γ : ℕ) : Submodule ℝ (NegSobolev d (γ : ℝ)) :=
  LinearMap.range (gfevEmbL (d := d) (gfev_le4 γ))

theorem gfev_embed_mem (γ : ℕ) (w : NegSobolev d ((γ : ℝ) - 4)) :
    NegSobolev.embed (γ : ℝ) w ∈ gfevD d γ := ⟨w, rfl⟩

theorem gfev_mem_D {γ : ℕ} {x : NegSobolev d (γ : ℝ)} (hx : x ∈ gfevD d γ) :
    ∃ w : NegSobolev d ((γ : ℝ) - 4), NegSobolev.embed (γ : ℝ) w = x := hx

/-- The linear operator `A` on the core from the bounded operator `A2 : E_{γ-2} → E_γ`. -/
def gfevAop {γ : ℕ} (A2 : NegSobolev d ((γ : ℝ) - 2) →L[ℝ] NegSobolev d (γ : ℝ)) :
    gfevD d γ →ₗ[ℝ] NegSobolev d (γ : ℝ) :=
  (A2 : NegSobolev d ((γ : ℝ) - 2) →ₗ[ℝ] NegSobolev d (γ : ℝ)) ∘ₗ gfevEmbL (d := d) (gfev_le42 γ) ∘ₗ
    (LinearEquiv.ofInjective (gfevEmbL (d := d) (gfev_le4 γ)) (gfev_embed_injective (gfev_le4 γ))).symm.toLinearMap

theorem gfevAt_embed {γ : ℕ} (A2 : ℝ → NegSobolev d ((γ : ℝ) - 2) →L[ℝ] NegSobolev d (γ : ℝ)) (t : ℝ)
    (w : NegSobolev d ((γ : ℝ) - 4)) :
    gfevAt (gfevD d γ) (fun s => gfevAop (A2 s)) t (NegSobolev.embed (γ : ℝ) w) =
      A2 t (NegSobolev.embed ((γ : ℝ) - 2) w) := by
  rw [gfevAt_of_mem t (gfev_embed_mem γ w)]
  have : (⟨NegSobolev.embed (γ : ℝ) w, gfev_embed_mem γ w⟩ : gfevD d γ) =
      LinearEquiv.ofInjective (gfevEmbL (d := d) (gfev_le4 γ)) (gfev_embed_injective (gfev_le4 γ)) w := rfl
  unfold gfevAop
  rw [this]
  show A2 t (gfevEmbL (d := d) (gfev_le42 γ) ((LinearEquiv.ofInjective (gfevEmbL (d := d) (gfev_le4 γ))
    (gfev_embed_injective (gfev_le4 γ))).symm
      ((LinearEquiv.ofInjective (gfevEmbL (d := d) (gfev_le4 γ)) (gfev_embed_injective (gfev_le4 γ))) w))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem gfev_ext_fc {m : ℝ} {F G : NegSobolev d m}
    (h : ∀ k, NegSobolev.fourierCoeff F k = NegSobolev.fourierCoeff G k) : F = G := by
  refine gfev_ext fun k => ?_
  rw [gfev_coord_eq_fc F k, gfev_coord_eq_fc G k, h k]

theorem gfev_dense_D (γ : ℕ) :
    Dense ((gfevD d γ : Submodule ℝ (NegSobolev d (γ : ℝ))) : Set (NegSobolev d (γ : ℝ))) := by
  classical
  intro x
  refine mem_closure_of_tendsto (tendsto_trunc x) (Eventually.of_forall fun S => ?_)
  refine ⟨q48bFin ((γ : ℝ) - 4) S (fun k => NegSobolev.fourierCoeff x k), ?_⟩
  show NegSobolev.embed (γ : ℝ) _ = _
  refine gfev_ext_fc fun k => ?_
  rw [gfev_fourierCoeff_embed (gfev_le4 γ), q48bFin_fourierCoeff, q48bFin_fourierCoeff]

end HRS.GF
