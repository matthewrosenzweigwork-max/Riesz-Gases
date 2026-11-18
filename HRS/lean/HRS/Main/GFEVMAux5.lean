import HRS.Main.GFEVMAux4

/-!
# Packet GFEVM, part 5: continuity of `σ ↦ A_σ`, the mild identity, the derivative, and the abstract evolution
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

section Mild

variable {γ T K : ℝ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ} {Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ}
  {VH : ℝ → ℝ → NegSobolev d γ →L[ℝ] NegSobolev d γ}
  {VE : ℝ → ℝ → NegSobolev d (γ + 2) →L[ℝ] NegSobolev d (γ + 2)}
  {A : ℝ → NegSobolev d γ →L[ℝ] NegSobolev d (γ + 2)}
  (h : GfmAbs γ T K Up Lb) (o : GfmOps γ T K Up Lb VH VE A)

include h o

theorem gfm_A_cont : ContinuousOn A (Set.Icc 0 T) := by
  rw [Metric.continuousOn_iff]
  intro σ₀ hσ₀ ε hε
  obtain ⟨δ, hδ, hδ'⟩ := h.gencont σ₀ hσ₀.1 hσ₀.2 (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun σ hσ hdist => ?_⟩
  rw [dist_eq_norm]
  have := gfev_dual_diff (h.gen σ hσ.1 hσ.2) (h.gen σ₀ hσ₀.1 hσ₀.2) (by positivity : (0 : ℝ) ≤ ε / 2)
    (fun φ hφ => hδ' σ hσ.1 hσ.2 (by rwa [Real.dist_eq] at hdist) φ hφ) (A σ) (A σ₀)
    (fun z φ hφ => o.dualA σ hσ.1 hσ.2 z φ hφ) (fun z φ hφ => o.dualA σ₀ hσ₀.1 hσ₀.2 z φ hφ)
  linarith

theorem gfm_F_cont {t : ℝ} (htT : t ≤ T) (x : NegSobolev d γ) :
    ContinuousOn (fun σ => VE t σ (A σ x)) (Set.Icc 0 t) := by
  refine gfev_continuousOn_clm_apply (X := ℝ) (S := Set.Icc 0 t) (Vf := fun σ => VE t σ)
    (w := fun σ => A σ x) (fun y => ?_) K (fun σ hσ => o.bdE t σ hσ.1 hσ.2 htT) ?_
  · exact (gfm_cont_E h o y).comp (Continuous.prodMk continuous_const continuous_id).continuousOn
      (fun σ hσ => ⟨hσ.1, hσ.2, htT⟩)
  · exact ((ContinuousLinearMap.apply ℝ (NegSobolev d (γ + 2)) x).continuous.comp_continuousOn
      ((gfm_A_cont h o).mono (Set.Icc_subset_Icc le_rfl htT)))

theorem gfm_mild {t u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu't : u' ≤ t) (htT : t ≤ T)
    (x : NegSobolev d γ) :
    VE t u' (gfmJ γ x) - VE t u (gfmJ γ x) = -∫ σ in u..u', VE t σ (A σ x) := by
  refine eq_of_eval_smooth fun φ hφ => ?_
  have hφE : gfmCls (γ + 2) φ := (h.upE u t hu (huu'.trans hu't) htT).smooth φ hφ
  set ℓ : NegSobolev d (γ + 2) →L[ℝ] ℝ := innerSL ℝ (lpOf (γ + 2) hφE.2) with hℓdef
  have hℓ : ∀ w, ℓ w = NegSobolev.eval w φ := fun w => by
    rw [eval_eq_inner _ w hφE.2, hℓdef, innerSL_apply_apply, real_inner_comm]
  have hint : IntervalIntegrable (fun σ => VE t σ (A σ x)) volume u u' :=
    ((gfm_F_cont h o htT x).mono (by rw [Set.uIcc_of_le huu']; exact Set.Icc_subset_Icc hu hu't)).intervalIntegrable
  have e2 : NegSobolev.eval (∫ σ in u..u', VE t σ (A σ x)) φ =
      ∫ σ in u..u', NegSobolev.eval (VE t σ (A σ x)) φ := by
    rw [← hℓ, ← ContinuousLinearMap.intervalIntegral_comp_comm ℓ hint]
    simp_rw [hℓ]
  have e3 : ∀ σ ∈ Set.uIcc u u', NegSobolev.eval (VE t σ (A σ x)) φ =
      NegSobolev.eval x (Lb σ (Up σ t φ)) := by
    intro σ hσ
    rw [Set.uIcc_of_le huu'] at hσ
    have hσ0 : 0 ≤ σ := hu.trans hσ.1
    have hσt : σ ≤ t := hσ.2.trans hu't
    rw [o.dualE t σ hσ0 hσt htT _ φ hφE,
      o.dualA σ hσ0 (hσt.trans htT) x _ (h.clsE σ t hσ0 hσt htT φ hφE)]
  have eneg : NegSobolev.eval (-∫ σ in u..u', VE t σ (A σ x)) φ =
      -NegSobolev.eval (∫ σ in u..u', VE t σ (A σ x)) φ := by
    rw [← hℓ, ← hℓ, map_neg]
  rw [eval_sub_left _ _ hφE.2, o.dualE t u' (hu.trans huu') hu't htT _ φ hφE,
    o.dualE t u hu (huu'.trans hu't) htT _ φ hφE, gfmJ_apply,
    gfev_eval_embed (by linarith : γ ≤ γ + 2), gfev_eval_embed (by linarith : γ ≤ γ + 2), eneg, e2,
    intervalIntegral.integral_congr e3, ← h.duh t u u' hu huu' hu't htT φ hφ x]
  ring

theorem gfm_deriv {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (x : NegSobolev d γ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun r' => VE t r' (gfmJ γ x)) (-(VE t r (A r x))) (Set.Icc 0 t) r := by
  refine gfev_hasDerivWithinAt_of_increments (x := fun r' => VE t r' (gfmJ γ x))
    (f := fun σ => -(VE t σ (A σ x))) ht0 (gfm_F_cont h o htT x).neg ?_ hr
  intro u hu u' hu' huu'
  rw [gfm_mild h o hu.1 huu' hu'.2 htT x, intervalIntegral.integral_neg]

end Mild

/-- The abstract evolution: from `GfmAbs` to an `EvolData E_γ E_{γ+2}` satisfying `IsEvolution` and `TwoLevel`. -/
theorem gfm_abs_main {γ T K : ℝ} {Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ}
    {Lb : ℝ → (Torus d → ℝ) → Torus d → ℝ} (h : GfmAbs γ T K Up Lb) :
    ∃ EV : EvolData (NegSobolev d γ) (NegSobolev d (γ + 2)),
      EV.IsEvolution T ∧ EV.TwoLevel T K ∧ (∀ z, EV.j z = NegSobolev.embed (γ + 2) z) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ (z : NegSobolev d (γ + 2)) (φ : Torus d → ℝ), Torus.IsSmooth φ →
        NegSobolev.eval (EV.VE t u z) φ = NegSobolev.eval z (Up u t φ)) := by
  obtain ⟨VH, VE, A, o⟩ := gfm_exists_ops h
  let EV : EvolData (NegSobolev d γ) (NegSobolev d (γ + 2)) :=
    { j := gfmJ γ, VH := VH, VE := VE, D := ⊤,
      A := fun σ => (A σ).toLinearMap.comp (⊤ : Submodule ℝ (NegSobolev d γ)).subtype }
  refine ⟨EV, ⟨?_, ?_, fun t ht => gfm_self_H h o ht.1 ht.2, fun t ht => gfm_self_E h o ht.1 ht.2,
    fun s r t hs hsr hrt htT => gfm_comp_H h o hs hsr hrt htT,
    fun s r t hs hsr hrt htT => gfm_comp_E h o hs hsr hrt htT,
    fun r t hr hrt htT => gfm_intertwine h o hr hrt htT,
    fun y => gfm_cont_E h o y, ?_⟩, ⟨rfl, ?_, ?_, ?_⟩, fun z => rfl, ?_⟩
  · exact gfev_embed_injective (by linarith)
  · show Dense ((⊤ : Submodule ℝ (NegSobolev d γ)) : Set (NegSobolev d γ))
    rw [Submodule.top_coe]
    exact dense_univ
  · intro t ht x r hr
    exact gfm_deriv h o ht.1 ht.2 x.1 hr
  · exact (gfmJ_norm_le γ).trans h.hK
  · intro r t hr hrt htT
    exact ⟨o.bdH t r hr hrt htT, o.bdE t r hr hrt htT⟩
  · intro r hr x
    have h1 := (A r).le_opNorm (x : NegSobolev d γ)
    exact h1.trans (mul_le_mul_of_nonneg_right (o.bdA r hr.1 hr.2) (norm_nonneg _))
  · intro u t hu hut htT z φ hφ
    exact o.dualE t u hu hut htT z φ ((h.upE u t hu hut htT).smooth φ hφ)

end HRS.GF
