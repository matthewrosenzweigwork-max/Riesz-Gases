import HRS.MS.ThmFixAux1

/-!
# THM-4 (second half) and pointwise rigidity

Abstract setting `ThmSetting K r B`.  Main statements:

* `minimizer_of_fixedpoint` : if `μ ∈ Cset r M` and `μ =ᵐ Tmap K r β μ` (with `0 < β`, `1 ≤ M`), then for every
  probability density `l` with the integrability conjuncts of `fe_identity` (integrable entropy integrand
  `l log (l / r)` and product-integrable `K l l`) one has `G μ ≤ G l`, and `G l = G μ` implies
  `l =ᵐ μ`.
* `fixedpoints_ae_eq` : two a.e.-fixed points in `Cset r M` agree a.e.
* `Tmap_congr_ae`, `thermalRep_eq_of_fixedpoints` : the Euler map sees only the a.e. class of `μ`, hence the
  representatives `thermalRep μ := Tmap K r β μ` of two a.e.-fixed points agree at every point.
* `thermalRep_mem_Cset`, `thermalRep_ae_eq`, `thermalRep_fixed` : `thermalRep μ ∈ Cset r M`, `thermalRep μ =ᵐ μ`,
  and `thermalRep μ x = Tmap K r β (thermalRep μ) x` for every `x`.
* `pointwise_fixedpoints_eq` : two everywhere-fixed points in `Cset r M` are equal everywhere.

Adjustment relative to the sketch: the finite-energy hypothesis `FiniteG l` is spelled as the two integrability
conjuncts `hlent`, `hlK` of `fe_identity` (both are needed so that the Bochner integrals are not junk values).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

section Fix2

variable {K : Euc d → Euc d → ℝ} {r : Euc d → ℝ} {B : ℝ}

/-- The pointwise representative of the thermal density attached to `μ`. -/
def thermalRep (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (β : ℝ) (μ : Euc d → ℝ) : Euc d → ℝ :=
  Tmap K r β μ

/-- Core identity: for an a.e. fixed point `μ`, `G l - G μ = β⁻¹ H(l | Tμ) + ½ E_K(l - μ)` with both terms `≥ 0`. -/
lemma t4_key (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {μ : Euc d → ℝ} (hμ : μ ∈ Cset r M) (hfix : μ =ᵐ[volume] Tmap K r β μ)
    {l : Euc d → ℝ} (hl : HRS.Whole.IsProbDensity l)
    (hlent : Integrable fun x => l x * Real.log (l x / r x))
    (hlK : Integrable (fun p : Euc d × Euc d => K p.1 p.2 * l p.1 * l p.2)
      ((volume : Measure (Euc d)).prod volume)) :
    0 ≤ relEnt l (Tmap K r β μ) ∧ 0 ≤ pairE K (l - μ) (l - μ) ∧
      Gfun K r β l - Gfun K r β μ =
        β⁻¹ * relEnt l (Tmap K r β μ) + (1 / 2) * pairE K (l - μ) (l - μ) := by
  have hνprob := (Tmap_isProbDensity_le hS hβ.le hμ.1).1
  have hνpos := Tmap_pos hS hβ.le hμ.1
  obtain ⟨hlT, hμT, hdiff, hid⟩ := fe_identity hS hβ hM hμ hl hlent hlK
  have hμ0 : relEnt μ (Tmap K r β μ) = 0 :=
    (relEnt_eq_zero_iff hμ.1 hνprob hνpos hμT).2 hfix
  have h1 : 0 ≤ relEnt l (Tmap K r β μ) := relEnt_nonneg hl hνprob hνpos hlT
  have hli := t012_integrable_of_prob hl
  have hμi := t012_integrable_of_prob hμ.1
  have h2 : 0 ≤ pairE K (l - μ) (l - μ) := by
    refine hS.k2 (l - μ) (hli.sub hμi) hdiff.abs ?_
    show ∫ x, (l x - μ x) = 0
    rw [integral_sub hli hμi, hl.integral_one, hμ.1.integral_one]
    norm_num
  refine ⟨h1, h2, ?_⟩
  rw [hid, hμ0]
  ring

/-- THM-4 (second half): an a.e. fixed point of the Euler map in `C_M` minimises `G` among all finite-energy
probability densities, and the minimiser is unique up to a.e. equality. -/
theorem minimizer_of_fixedpoint (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {μ : Euc d → ℝ} (hμ : μ ∈ Cset r M) (hfix : μ =ᵐ[volume] Tmap K r β μ) :
    (∀ l : Euc d → ℝ, HRS.Whole.IsProbDensity l →
      Integrable (fun x => l x * Real.log (l x / r x)) →
      Integrable (fun p : Euc d × Euc d => K p.1 p.2 * l p.1 * l p.2)
        ((volume : Measure (Euc d)).prod volume) →
      Gfun K r β μ ≤ Gfun K r β l) ∧
    (∀ l : Euc d → ℝ, HRS.Whole.IsProbDensity l →
      Integrable (fun x => l x * Real.log (l x / r x)) →
      Integrable (fun p : Euc d × Euc d => K p.1 p.2 * l p.1 * l p.2)
        ((volume : Measure (Euc d)).prod volume) →
      Gfun K r β l = Gfun K r β μ → l =ᵐ[volume] μ) := by
  refine ⟨fun l hl hlent hlK => ?_, fun l hl hlent hlK hG => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := t4_key hS hβ hM hμ hfix hl hlent hlK
    have : 0 ≤ β⁻¹ * relEnt l (Tmap K r β μ) := mul_nonneg (inv_nonneg.2 hβ.le) h1
    linarith
  · obtain ⟨h1, h2, h3⟩ := t4_key hS hβ hM hμ hfix hl hlent hlK
    have hνprob := (Tmap_isProbDensity_le hS hβ.le hμ.1).1
    have hνpos := Tmap_pos hS hβ.le hμ.1
    obtain ⟨hlT, _, _, _⟩ := fe_identity hS hβ hM hμ hl hlent hlK
    have h4 : 0 ≤ β⁻¹ * relEnt l (Tmap K r β μ) := mul_nonneg (inv_nonneg.2 hβ.le) h1
    have h5 : β⁻¹ * relEnt l (Tmap K r β μ) = 0 := by linarith
    have h6 : relEnt l (Tmap K r β μ) = 0 := by
      rcases mul_eq_zero.1 h5 with h | h
      · exact absurd h (inv_ne_zero hβ.ne')
      · exact h
    have hlν := (relEnt_eq_zero_iff hl hνprob hνpos hlT).1 h6
    exact hlν.trans hfix.symm

/-- Two a.e. fixed points of the Euler map in `C_M` agree a.e. -/
theorem fixedpoints_ae_eq (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {μ₁ μ₂ : Euc d → ℝ} (h₁ : μ₁ ∈ Cset r M) (h₂ : μ₂ ∈ Cset r M)
    (f₁ : μ₁ =ᵐ[volume] Tmap K r β μ₁) (f₂ : μ₂ =ᵐ[volume] Tmap K r β μ₂) :
    μ₁ =ᵐ[volume] μ₂ := by
  have a1 := minimizer_of_fixedpoint hS hβ hM h₁ f₁
  have a2 := minimizer_of_fixedpoint hS hβ hM h₂ f₂
  have e2 := t3_ent_integrable hS hM h₂
  have p2 := t3_pairE_integrable hS h₂ h₂
  have e1 := t3_ent_integrable hS hM h₁
  have p1 := t3_pairE_integrable hS h₁ h₁
  have g12 := a1.1 μ₂ h₂.1 e2 p2
  have g21 := a2.1 μ₁ h₁.1 e1 p1
  exact (a1.2 μ₂ h₂.1 e2 p2 (le_antisymm g21 g12)).symm

/-- The Euler map depends on `μ` only through its a.e. class. -/
theorem Tmap_congr_ae (K : Euc d → Euc d → ℝ) (r : Euc d → ℝ) (β : ℝ) {μ μ' : Euc d → ℝ}
    (h : μ =ᵐ[volume] μ') : Tmap K r β μ = Tmap K r β μ' := by
  have hu : ∀ x, ∫ y, K x y * μ y = ∫ y, K x y * μ' y := fun x =>
    integral_congr_ae (by filter_upwards [h] with y hy; rw [hy])
  funext x
  unfold Tmap
  simp_rw [hu]

/-- Pointwise rigidity: the representatives `Tμ₁`, `Tμ₂` of two a.e. fixed points in `C_M` agree everywhere. -/
theorem thermalRep_eq_of_fixedpoints (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {μ₁ μ₂ : Euc d → ℝ} (h₁ : μ₁ ∈ Cset r M) (h₂ : μ₂ ∈ Cset r M)
    (f₁ : μ₁ =ᵐ[volume] Tmap K r β μ₁) (f₂ : μ₂ =ᵐ[volume] Tmap K r β μ₂) (x : Euc d) :
    thermalRep K r β μ₁ x = thermalRep K r β μ₂ x := by
  have := Tmap_congr_ae K r β (fixedpoints_ae_eq hS hβ hM h₁ h₂ f₁ f₂)
  exact congrFun this x

theorem thermalRep_mem_Cset (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 ≤ β)
    (hexp : Real.exp (β * B) ≤ M) {μ : Euc d → ℝ} (hμ : HRS.Whole.IsProbDensity μ) :
    thermalRep K r β μ ∈ Cset r M :=
  Tmap_mem_Cset hS hβ hexp hμ

theorem thermalRep_ae_eq {β : ℝ} {μ : Euc d → ℝ} (hfix : μ =ᵐ[volume] Tmap K r β μ) :
    thermalRep K r β μ =ᵐ[volume] μ := hfix.symm

/-- The representative is an everywhere fixed point. -/
theorem thermalRep_fixed {β : ℝ} {μ : Euc d → ℝ} (hfix : μ =ᵐ[volume] Tmap K r β μ) (x : Euc d) :
    thermalRep K r β μ x = Tmap K r β (thermalRep K r β μ) x :=
  (congrFun (Tmap_congr_ae K r β (thermalRep_ae_eq hfix)) x).symm

/-- Two everywhere fixed points of the Euler map in `C_M` coincide at every point. -/
theorem pointwise_fixedpoints_eq (hS : ThmSetting K r B) {β M : ℝ} (hβ : 0 < β) (hM : 1 ≤ M)
    {ρ₁ ρ₂ : Euc d → ℝ} (h₁ : ρ₁ ∈ Cset r M) (h₂ : ρ₂ ∈ Cset r M)
    (f₁ : ∀ x, ρ₁ x = Tmap K r β ρ₁ x) (f₂ : ∀ x, ρ₂ x = Tmap K r β ρ₂ x) (x : Euc d) :
    ρ₁ x = ρ₂ x := by
  have a1 : ρ₁ =ᵐ[volume] Tmap K r β ρ₁ := ae_of_all _ f₁
  have a2 : ρ₂ =ᵐ[volume] Tmap K r β ρ₂ := ae_of_all _ f₂
  have := Tmap_congr_ae K r β (fixedpoints_ae_eq hS hβ hM h₁ h₂ a1 a2)
  rw [f₁ x, f₂ x, this]

end Fix2

end HRS.MS.Thm

end
