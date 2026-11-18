import HRS.Commutator.Whole.DECAux
import HRS.Commutator.Whole.Energy

/-!
# Packet CMX-DEC, helper file 2: good kernels and the pairing formula on `ν = μ_N - μ`

`DecGood ρ K`: the kernel `K` is measurable, symmetric, and `K(a,·)ρ` is integrable for every `a`
and `K ρ ⊗ ρ` is integrable (the integrability package used by the note's Fubini steps).
`dec_pair2_formula` writes `𝒞_K(ν) = N⁻¹ ∑_i Φ(X_i) - ∫ ρ Φ` with `Φ(x) = N⁻¹ ∑_j K(x,X_j) - ∫ K(x,·)ρ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.DEC

variable {d : ℕ}

/-- Integrability package for a kernel against the signed density `ρ`. -/
structure DecGood (ρ : Euc d → ℝ) (K : Euc d → Euc d → ℝ) : Prop where
  meas : Measurable (fun q : Euc d × Euc d => K q.1 q.2)
  symm : ∀ x y, K x y = K y x
  F1 : ∀ a, Integrable (fun y => K a y * ρ y)
  F2 : Integrable (fun q : Euc d × Euc d => K q.1 q.2 * ρ q.1 * ρ q.2)

theorem DecGood.congr' {ρ : Euc d → ℝ} {K K' : Euc d → Euc d → ℝ} (h : DecGood ρ K)
    (hK : ∀ x y, K x y = K' x y) : DecGood ρ K' := by
  have e : K = K' := funext fun x => funext fun y => hK x y
  subst e
  exact h

theorem DecGood.add {ρ : Euc d → ℝ} {K₁ K₂ : Euc d → Euc d → ℝ} (h₁ : DecGood ρ K₁)
    (h₂ : DecGood ρ K₂) : DecGood ρ (fun x y => K₁ x y + K₂ x y) where
  meas := h₁.meas.add h₂.meas
  symm := fun x y => by simp only [h₁.symm x y, h₂.symm x y]
  F1 := fun a => ((h₁.F1 a).add (h₂.F1 a)).congr (ae_of_all _ fun y => by
    simp only [Pi.add_apply, add_mul])
  F2 := (h₁.F2.add h₂.F2).congr (ae_of_all _ fun q => by simp only [Pi.add_apply, add_mul])

theorem DecGood.sub {ρ : Euc d → ℝ} {K₁ K₂ : Euc d → Euc d → ℝ} (h₁ : DecGood ρ K₁)
    (h₂ : DecGood ρ K₂) : DecGood ρ (fun x y => K₁ x y - K₂ x y) where
  meas := h₁.meas.sub h₂.meas
  symm := fun x y => by simp only [h₁.symm x y, h₂.symm x y]
  F1 := fun a => ((h₁.F1 a).sub (h₂.F1 a)).congr (ae_of_all _ fun y => by
    simp only [Pi.sub_apply, sub_mul])
  F2 := (h₁.F2.sub h₂.F2).congr (ae_of_all _ fun q => by simp only [Pi.sub_apply, sub_mul])

/-- The potential `Φ_K(x) = N⁻¹ ∑_j K(x, X_j) - ∫ K(x,y) ρ(y) dy`. -/
def decPhi (ρ : Euc d → ℝ) {N : ℕ} (X : Fin N → Euc d) (K : Euc d → Euc d → ℝ) (x : Euc d) : ℝ :=
  (1 / (N : ℝ)) * ∑ j, K x (X j) - ∫ y, K x y * ρ y

theorem decPhi_meas {ρ : Euc d → ℝ} (hρm : Measurable ρ) {N : ℕ} (X : Fin N → Euc d)
    {K : Euc d → Euc d → ℝ} (hG : DecGood ρ K) : Measurable (decPhi ρ X K) := by
  unfold decPhi
  have h1 : Measurable (fun x => ∑ j, K x (X j)) :=
    Finset.measurable_sum _ fun j _ => hG.meas.comp (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun x => ∫ y, K x y * ρ y) :=
    param_measurable (μ := volume) (J := fun x y => K x y * ρ y)
      (hG.meas.mul (hρm.comp measurable_snd))
  exact (h1.const_mul _).sub h2

/-- Pointwise form of `ρ Φ_K`. -/
theorem decPhi_pt {ρ : Euc d → ℝ} {N : ℕ} (X : Fin N → Euc d) (K : Euc d → Euc d → ℝ)
    (hG : DecGood ρ K) (x : Euc d) :
    ρ x * decPhi ρ X K x =
      (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y := by
  have hint : ∫ y, K x y * ρ x * ρ y = ρ x * ∫ y, K x y * ρ y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  unfold decPhi
  have hsum : ∑ j, K x (X j) = ∑ j, K (X j) x := Finset.sum_congr rfl fun j _ => hG.symm x (X j)
  rw [hint, hsum, ← Finset.sum_mul]
  ring

theorem decPhi_integrable {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) {N : ℕ} (X : Fin N → Euc d)
    {K : Euc d → Euc d → ℝ} (hG : DecGood ρ K) :
    Integrable (fun x => ρ x * decPhi ρ X K x) := by
  have hpt : ∀ x, ρ x * decPhi ρ X K x =
      (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y :=
    fun x => decPhi_pt X K hG x
  have hi1 : Integrable (fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun j _ => hG.F1 (X j)
  have hi2 : Integrable (fun x => ∫ y, K x y * ρ x * ρ y) := hG.F2.integral_prod_left
  have heq : (fun x => ρ x * decPhi ρ X K x) =
      fun x => (1 / (N : ℝ)) * ∑ j, K (X j) x * ρ x - ∫ y, K x y * ρ x * ρ y :=
    funext hpt
  rw [heq]
  exact hi1.sub hi2


/-- The pairing formula on `ν = μ_N - μ`: `𝒞_K(ν) = N⁻¹ ∑_i Φ_K(X_i) - ∫ ρ Φ_K`. -/
theorem pair2_formula {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Fin N → Euc d) {K : Euc d → Euc d → ℝ} (hG : DecGood ρ K) :
    (chargeOf X ρ).pair2 K =
      (1 / (N : ℝ)) * ∑ i, decPhi ρ X K (X i) - ∫ x, ρ x * decPhi ρ X K x := by
  have hinner : ∀ x, (chargeOf X ρ).int (fun y => K x y) = decPhi ρ X K x := by
    intro x
    have hsm : StronglyMeasurable (fun y => K x y) :=
      (hG.meas.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
    have hint : Integrable (fun y => ρ y * K x y) :=
      (hG.F1 x).congr (ae_of_all _ fun y => mul_comm _ _)
    have e : ∫ y, ρ y * K x y = ∫ y, K x y * ρ y :=
      integral_congr_ae (ae_of_all _ fun y => mul_comm _ _)
    rw [energyAux_charge_int ρ hρ hN X (fun y => K x y) hsm hint]
    simp only [decPhi, e]
  have hPhi : (chargeOf X ρ).pair2 K = (chargeOf X ρ).int (decPhi ρ X K) := by
    unfold SMeas.pair2
    simp only [hinner]
  rw [hPhi, energyAux_charge_int ρ hρ hN X (decPhi ρ X K)
    (decPhi_meas hρ.measurable X hG).stronglyMeasurable (decPhi_integrable hρ X hG)]

theorem decPhi_add {ρ : Euc d → ℝ} {N : ℕ} (X : Fin N → Euc d) {K₁ K₂ : Euc d → Euc d → ℝ}
    (h₁ : DecGood ρ K₁) (h₂ : DecGood ρ K₂) (x : Euc d) :
    decPhi ρ X (fun x y => K₁ x y + K₂ x y) x = decPhi ρ X K₁ x + decPhi ρ X K₂ x := by
  have e : ∫ y, (K₁ x y + K₂ x y) * ρ y = (∫ y, K₁ x y * ρ y) + ∫ y, K₂ x y * ρ y := by
    refine Eq.trans ?_ (integral_add (h₁.F1 x) (h₂.F1 x))
    congr 1
    funext y
    ring
  simp only [decPhi]
  rw [e, Finset.sum_add_distrib]
  ring

/-- Additivity of the pairing in the kernel (both kernels good). -/
theorem pair2_add {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : Fin N → Euc d) {K₁ K₂ : Euc d → Euc d → ℝ} (h₁ : DecGood ρ K₁) (h₂ : DecGood ρ K₂) :
    (chargeOf X ρ).pair2 (fun x y => K₁ x y + K₂ x y) =
      (chargeOf X ρ).pair2 K₁ + (chargeOf X ρ).pair2 K₂ := by
  have hfun : decPhi ρ X (fun x y => K₁ x y + K₂ x y) =
      fun x => decPhi ρ X K₁ x + decPhi ρ X K₂ x := funext (decPhi_add X h₁ h₂)
  have hI : ∫ x, ρ x * (decPhi ρ X K₁ x + decPhi ρ X K₂ x) =
      (∫ x, ρ x * decPhi ρ X K₁ x) + ∫ x, ρ x * decPhi ρ X K₂ x := by
    refine Eq.trans ?_ (integral_add (decPhi_integrable hρ X h₁) (decPhi_integrable hρ X h₂))
    congr 1
    funext x
    ring
  rw [pair2_formula hρ hN X (h₁.add h₂), pair2_formula hρ hN X h₁,
    pair2_formula hρ hN X h₂, hfun, hI]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-! ### Commutator kernels -/

theorem dec_commKer_meas {F : Euc d → Euc d} {v : Euc d → Euc d} (hF : Measurable F)
    (hv : Measurable v) : Measurable (fun q : Euc d × Euc d => commKer F v q.1 q.2) := by
  unfold commKer
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).inner
    (hF.comp (measurable_fst.sub measurable_snd))

theorem dec_commKer_symm {F : Euc d → Euc d} (hF : ∀ z, F (-z) = -F z) (v : Euc d → Euc d)
    (x y : Euc d) : commKer F v x y = commKer F v y x := by
  unfold commKer
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun e => h e.symm
    rw [if_neg h, if_neg h', show y - x = -(x - y) by abel, hF, show v y - v x = -(v x - v y) by abel,
      inner_neg_left, inner_neg_right, neg_neg]

theorem dec_commKer_diag (F : Euc d → Euc d) (v : Euc d → Euc d) (x : Euc d) :
    commKer F v x x = 0 := by
  unfold commKer
  simp

theorem dec_commKer_split (F : Euc d → Euc d) (v : Euc d → Euc d) (x y : Euc d) :
    commKer F v x y = commKer F (Pleq 1 v) x y + commKer F (Pgt 1 v) x y := by
  unfold commKer
  by_cases h : x = y
  · simp [h]
  · rw [if_neg h, if_neg h, if_neg h, ← inner_add_left]
    congr 1
    simp only [Pgt]
    abel

/-- A bounded measurable symmetric kernel is good (for every finite-mass-compact density). -/
theorem dec_good_bdd {ρ : Euc d → ℝ} (hρ : BddCptDensity ρ) {K : Euc d → Euc d → ℝ}
    (hm : Measurable (fun q : Euc d × Euc d => K q.1 q.2)) (hs : ∀ x y, K x y = K y x) {C : ℝ}
    (hC : ∀ x y, ‖K x y‖ ≤ C) : DecGood ρ K := by
  have hint : Integrable ρ := (energyAux_bddCpt_integrable ρ hρ).1
  refine ⟨hm, hs, fun a => ?_, ?_⟩
  · have hf : AEStronglyMeasurable (fun y => K a y) volume :=
      (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact hint.bdd_mul hf (ae_of_all _ fun y => hC a y)
  · have hg : Integrable (fun q : Euc d × Euc d => ρ q.1 * ρ q.2) := by
      rw [Measure.volume_eq_prod]
      exact Integrable.mul_prod hint hint
    have hf : AEStronglyMeasurable (fun q : Euc d × Euc d => K q.1 q.2) volume :=
      hm.aestronglyMeasurable
    exact (hg.bdd_mul hf (ae_of_all _ fun q => hC q.1 q.2)).congr
      (ae_of_all _ fun q => by simp only [mul_assoc])


end HRS.Commutator.Whole.DEC
