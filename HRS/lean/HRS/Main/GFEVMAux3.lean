import HRS.Main.GFEVMAux2

/-!
# Packet GFEVM, part 3: the abstract two-level dual evolution (hypotheses, dual operators, algebraic fields)

`GfmAbs` collects the properties of the adjoint propagator `Up r t` (on the classes `C² ∩ H^γ`, `C² ∩ H^{γ+2}`) and of the
generators `Lb σ` that suffice to build the `EvolData E_γ E_{γ+2}` of the matrix clause of Lemma 3.17.  `GfmOps` are the dual
operators.  This file: existence of the dual operators, the cocycle fields and the intertwining relation.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

structure GfmAbs (γ T K : ℝ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ)
    (Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ) : Prop where
  hK : 1 ≤ K
  upH : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → DualHyp (gfmCls γ) γ (Up r t) K
  upE : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → DualHyp (gfmCls (γ + 2)) (γ + 2) (Up r t) K
  clsH : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls γ φ → gfmCls γ (Up r t φ)
  clsE : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls (γ + 2) φ → gfmCls (γ + 2) (Up r t φ)
  selfH : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls γ φ → Up t t φ = φ
  selfE : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls (γ + 2) φ → Up t t φ = φ
  cocH : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls γ φ →
    Up s r (Up r t φ) = Up s t φ
  cocE : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, gfmCls (γ + 2) φ →
    Up s r (Up r t φ) = Up s t φ
  gen : ∀ σ : ℝ, 0 ≤ σ → σ ≤ T → GfDualHyp (gfmCls (γ + 2)) (γ + 2) γ (Lb σ) K
  gencont : ∀ σ₀ : ℝ, 0 ≤ σ₀ → σ₀ ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 0 ≤ σ → σ ≤ T →
    |σ - σ₀| < δ → ∀ φ : Torus d → ℝ, gfmCls (γ + 2) φ →
      MemSobolev γ (fun x => Lb σ φ x - Lb σ₀ φ x) ∧
        sobolevNorm γ (fun x => Lb σ φ x - Lb σ₀ φ x) ≤ ε * sobolevNorm (γ + 2) φ
  duh : ∀ t u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ t → t ≤ T → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
    ∀ z : NegSobolev d γ, NegSobolev.eval z (Up u t φ) - NegSobolev.eval z (Up u' t φ) =
      ∫ σ in u..u', NegSobolev.eval z (Lb σ (Up σ t φ))

structure GfmOps (γ T K : ℝ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ)
    (Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ)
    (VH : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ)
    (VE : ℝ → ℝ → NegSobolev d (γ + 2) →L[ℝ] NegSobolev d (γ + 2))
    (A : ℝ → NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2)) : Prop where
  bdH : ∀ t r : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖VH t r‖ ≤ K
  bdE : ∀ t r : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖VE t r‖ ≤ K
  bdA : ∀ σ : ℝ, 0 ≤ σ → σ ≤ T → ‖A σ‖ ≤ K
  dualH : ∀ t r : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ (z : NegSobolev d γ) (φ : Torus d → ℝ), gfmCls γ φ →
    NegSobolev.eval (VH t r z) φ = NegSobolev.eval z (Up r t φ)
  dualE : ∀ t r : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ (z : NegSobolev d (γ + 2)) (φ : Torus d → ℝ),
    gfmCls (γ + 2) φ → NegSobolev.eval (VE t r z) φ = NegSobolev.eval z (Up r t φ)
  dualA : ∀ σ : ℝ, 0 ≤ σ → σ ≤ T → ∀ (z : NegSobolev d γ) (φ : Torus d → ℝ), gfmCls (γ + 2) φ →
    NegSobolev.eval (A σ z) φ = NegSobolev.eval z (Lb σ φ)

/-- the embedding `E_γ → E_{γ+2}` as a continuous linear map -/
def gfmJ (γ : ℝ) : NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2) :=
  LinearMap.mkContinuous (gfevEmbL (by linarith : γ ≤ γ + 2)) 1 (fun F => by
    rw [one_mul]; exact NegSobolev.norm_embed_le (γ + 2) (by linarith) F)

theorem gfmJ_apply (γ : ℝ) (z : NegSobolev d γ) : gfmJ γ z = NegSobolev.embed (γ + 2) z := rfl

theorem gfmJ_norm_le (γ : ℝ) : ‖(gfmJ γ : NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2))‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem gfm_exists_ops {γ T K : ℝ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ}
    {Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ} (h : GfmAbs γ T K Up Lb) :
    ∃ (VH : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ)
      (VE : ℝ → ℝ → NegSobolev d (γ + 2) →L[ℝ] NegSobolev d (γ + 2))
      (A : ℝ → NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2)), GfmOps γ T K Up Lb VH VE A := by
  classical
  have hH : ∀ t r : ℝ, ∃ V : NegSobolev d γ →L[ℝ] NegSobolev d γ, 0 ≤ r → r ≤ t → t ≤ T →
      ‖V‖ ≤ K ∧ ∀ (z : NegSobolev d γ) (φ : Torus d → ℝ), gfmCls γ φ →
        NegSobolev.eval (V z) φ = NegSobolev.eval z (Up r t φ) := by
    intro t r
    by_cases hc : 0 ≤ r ∧ r ≤ t ∧ t ≤ T
    · obtain ⟨V, hV, hd⟩ := exists_dual_op (h.upH r t hc.1 hc.2.1 hc.2.2)
      exact ⟨V, fun _ _ _ => ⟨hV, hd⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
  have hE : ∀ t r : ℝ, ∃ V : NegSobolev d (γ + 2) →L[ℝ] NegSobolev d (γ + 2), 0 ≤ r → r ≤ t → t ≤ T →
      ‖V‖ ≤ K ∧ ∀ (z : NegSobolev d (γ + 2)) (φ : Torus d → ℝ), gfmCls (γ + 2) φ →
        NegSobolev.eval (V z) φ = NegSobolev.eval z (Up r t φ) := by
    intro t r
    by_cases hc : 0 ≤ r ∧ r ≤ t ∧ t ≤ T
    · obtain ⟨V, hV, hd⟩ := exists_dual_op (h.upE r t hc.1 hc.2.1 hc.2.2)
      exact ⟨V, fun _ _ _ => ⟨hV, hd⟩⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc⟩
  have hA : ∀ σ : ℝ, ∃ V : NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2), 0 ≤ σ → σ ≤ T →
      ‖V‖ ≤ K ∧ ∀ (z : NegSobolev d γ) (φ : Torus d → ℝ), gfmCls (γ + 2) φ →
        NegSobolev.eval (V z) φ = NegSobolev.eval z (Lb σ φ) := by
    intro σ
    by_cases hc : 0 ≤ σ ∧ σ ≤ T
    · obtain ⟨V, hV, hd⟩ := gfev_exists_dual_op2 (h.gen σ hc.1 hc.2)
      exact ⟨V, fun _ _ => ⟨hV, hd⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose VH hVH using hH
  choose VE hVE using hE
  choose A hA' using hA
  exact ⟨VH, VE, A, ⟨fun t r h1 h2 h3 => (hVH t r h1 h2 h3).1, fun t r h1 h2 h3 => (hVE t r h1 h2 h3).1,
    fun σ h1 h2 => (hA' σ h1 h2).1, fun t r h1 h2 h3 => (hVH t r h1 h2 h3).2,
    fun t r h1 h2 h3 => (hVE t r h1 h2 h3).2, fun σ h1 h2 => (hA' σ h1 h2).2⟩⟩

section Fields

variable {γ T K : ℝ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ} {Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ}
  {VH : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ}
  {VE : ℝ → ℝ → NegSobolev d (γ + 2) →L[ℝ] NegSobolev d (γ + 2)}
  {A : ℝ → NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2)}
  (h : GfmAbs γ T K Up Lb) (o : GfmOps γ T K Up Lb VH VE A)

include h o

theorem gfm_self_H {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) : VH t t = 1 := by
  refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
  have hc : gfmCls γ φ := (h.upH t t ht0 le_rfl htT).smooth φ hφ
  rw [o.dualH t t ht0 le_rfl htT z φ hc, h.selfH t ht0 htT φ hc]
  rfl

theorem gfm_self_E {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) : VE t t = 1 := by
  refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
  have hc : gfmCls (γ + 2) φ := (h.upE t t ht0 le_rfl htT).smooth φ hφ
  rw [o.dualE t t ht0 le_rfl htT z φ hc, h.selfE t ht0 htT φ hc]
  rfl

theorem gfm_comp_H {s r t : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    (VH t r).comp (VH r s) = VH t s := by
  refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
  have hr0 : 0 ≤ r := hs.trans hsr
  have hc : gfmCls γ φ := (h.upH r t hr0 hrt htT).smooth φ hφ
  have hc' : gfmCls γ (Up r t φ) := h.clsH r t hr0 hrt htT φ hc
  rw [ContinuousLinearMap.comp_apply, o.dualH t r hr0 hrt htT _ φ hc,
    o.dualH r s hs hsr (hrt.trans htT) z _ hc', h.cocH s r t hs hsr hrt htT φ hc,
    o.dualH t s hs (hsr.trans hrt) htT z φ hc]

theorem gfm_comp_E {s r t : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    (VE t r).comp (VE r s) = VE t s := by
  refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
  have hr0 : 0 ≤ r := hs.trans hsr
  have hc : gfmCls (γ + 2) φ := (h.upE r t hr0 hrt htT).smooth φ hφ
  have hc' : gfmCls (γ + 2) (Up r t φ) := h.clsE r t hr0 hrt htT φ hc
  rw [ContinuousLinearMap.comp_apply, o.dualE t r hr0 hrt htT _ φ hc,
    o.dualE r s hs hsr (hrt.trans htT) z _ hc', h.cocE s r t hs hsr hrt htT φ hc,
    o.dualE t s hs (hsr.trans hrt) htT z φ hc]

theorem gfm_intertwine {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) :
    (VE t r).comp (gfmJ γ) = (gfmJ γ).comp (VH t r) := by
  refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
  have hE : gfmCls (γ + 2) φ := (h.upE r t hr hrt htT).smooth φ hφ
  have hH : gfmCls γ φ := (h.upH r t hr hrt htT).smooth φ hφ
  simp only [ContinuousLinearMap.comp_apply, gfmJ_apply]
  rw [o.dualE t r hr hrt htT _ φ hE, gfev_eval_embed (by linarith : γ ≤ γ + 2),
    gfev_eval_embed (by linarith : γ ≤ γ + 2), o.dualH t r hr hrt htT z φ hH]

end Fields

end HRS.GF
