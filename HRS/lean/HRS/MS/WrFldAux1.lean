import HRS.MS.WrCal

/-!
# HRS.MS.WrFldAux1 -- the calibrated weak potential `weakPotE` and `RN = fieldLaw` (WR-12b, part 1)

Packet WR-12b of `docs/SUPP_FOUND_PACKETS.md` (track D, T3 NEW part).  Euclidean port of
`HRS/Equilibrium/CalibratedReference.lean:945 weakPot`, `:978 fieldLaw_eq_tilted`, `:1000 RN_eq_fieldLaw`,
where the torus `RefHyp` is replaced by the hypotheses `EWeakKernel μ a q` (`WrKerAux1`) and
`CalFeat Ψ B` (`WrCal`), and the feature space is an arbitrary real Hilbert space `H`.

* `weakPotE hK ha hβ h t ht : WeakPotential μ`: `φ = β (q*μ) + ⟪t, Ξ⟫`, pair kernel `q`, `M = β a + 1`,
  `M' = 0`, `γ = a`, under the hypothesis `|⟪t, Ξ x⟫| ≤ 1` for all `x`.
* `wr12b_fieldLaw_eq_tilted`: `fieldLaw V ψ lam n = μ^n.tilted (∑ ψ(y_i) - lam * pairEnergy V y)`.
* `RN_eq_fieldLaw`: `RN q μ Ψ β N = fieldLaw (weakPotE ..) (weakPotE ..).φ (β / N) N` for `t = tN`.
* `RN_eq_pinnedLaw`: the same as `pinnedLaw V (β/N) N (empty pin configuration)`.

No hypothesis of the torus statement is dropped except the `RefHyp` ones that are replaced by the
`EWeakKernel`/`CalFeat` structures; `0 ≤ a` is explicit (the structure `EWeakKernel` allows any real `a`).
Helper lemmas carry the prefix `wr12b_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External

variable {d : ℕ}

/-! ### `fieldLaw` as a tilted measure (generic space) -/

section Tilt

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- If `exp (∑ ψ - lam · pairEnergy)` is integrable, `fieldLaw` is the corresponding tilted measure. -/
theorem wr12b_fieldLaw_eq_tilted {V : WeakPotential μ} {ψ : E → ℝ} {lam : ℝ} {n : ℕ}
    (hint : Integrable (fun y : Fin n → E => Real.exp (∑ i, ψ (y i) - lam * External.pairEnergy V y))
      (Measure.pi fun _ : Fin n => μ)) :
    fieldLaw V ψ lam n = (Measure.pi fun _ : Fin n => μ).tilted
      (fun y => ∑ i, ψ (y i) - lam * External.pairEnergy V y) := by
  have hZ : ENNReal.ofReal (∫ y, Real.exp (∑ i, ψ (y i) - lam * External.pairEnergy V y)
      ∂(Measure.pi fun _ : Fin n => μ)) = fieldNorm V ψ lam n := by
    unfold fieldNorm fieldWeight
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hZpos := integral_exp_pos (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun y : Fin n → E => ∑ i, ψ (y i) - lam * External.pairEnergy V y) hint
  unfold fieldLaw Measure.tilted
  congr 1
  funext y
  unfold fieldDensity fieldWeight
  rw [ENNReal.ofReal_div_of_pos hZpos, hZ, div_eq_mul_inv]

/-- For a field bounded above and `lam ≥ 0` the exponential weight is integrable. -/
theorem wr12b_integrable_exp_field {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ}
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    Integrable (fun y : Fin n → E => Real.exp (∑ i, ψ (y i) - lam * External.pairEnergy V y))
      (Measure.pi fun _ : Fin n => μ) := by
  have hm : Measurable fun y : Fin n → E =>
      Real.exp (∑ i, ψ (y i) - lam * External.pairEnergy V y) :=
    Real.measurable_exp.comp ((Finset.measurable_sum _ fun i _ =>
      hψ.measurable.comp (measurable_pi_apply i)).sub
        ((measurable_pairEnergy V).const_mul _))
  refine Integrable.of_bound hm.aestronglyMeasurable (Real.exp (n * M))
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  have h1 : ∑ i, ψ (y i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hψ.le _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 := mul_nonneg hlam (pairEnergy_nonneg V y)
  linarith

end Tilt

/-! ### The calibrated weak potential -/

section Pot

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Euc d → Euc d → ℝ}
  {Ψ : Euc d → H} {B β : ℝ} {N : ℕ}

lemma wr12b_measurable_inner_Xi (h : CalFeat Ψ B) (t : H) :
    Measurable fun x => inner ℝ t (Xi μ Ψ x) :=
  (continuous_const.inner h.continuous_Xi).measurable

lemma wr12b_integral_inner_Xi (h : CalFeat Ψ B) (t : H) :
    ∫ x, inner ℝ t (Xi μ Ψ x) ∂μ = 0 := by
  have hint : Integrable (Xi μ Ψ) μ := h.integrable_Ψ.sub (integrable_const _)
  rw [integral_inner hint t]
  have : ∫ x, Xi μ Ψ x ∂μ = 0 := by
    unfold Xi
    rw [integral_sub h.integrable_Ψ (integrable_const _)]
    simp
  rw [this, inner_zero_right]

/-- **The calibrated weak potential** `φ = β (q*μ) + ⟪t, Ξ⟫` (`CalibratedReference.lean:945 weakPot`):
pair kernel `q`, `M = β a + 1`, `M' = 0`, `γ = a`, provided `|⟪t, Ξ⟫| ≤ 1`. -/
def weakPotE (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B) (t : H)
    (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ 1) : WeakPotential μ where
  φ := fun x => β * rowIntE q μ x + inner ℝ t (Xi μ Ψ x)
  q := q
  M := β * a + 1
  M' := 0
  γ := a
  measurable_φ := (hK.wr1_measurable_rowInt.const_mul β).add (wr12b_measurable_inner_Xi h t)
  measurable_q := hK.meas
  q_nonneg := hK.nonneg
  q_symm := hK.symm
  γ_nonneg := ha
  φ_le := fun x => by
    have h1 : β * rowIntE q μ x ≤ β * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ
    have h2 := (le_abs_self _).trans (ht x)
    linarith
  integrable_φ := by
    refine Integrable.of_bound
      ((hK.wr1_measurable_rowInt.const_mul β).add (wr12b_measurable_inner_Xi h t)).aestronglyMeasurable
      (β * a + 1) (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 0 ≤ β * rowIntE q μ x := mul_nonneg hβ (hK.wr1_rowInt_nonneg x)
    have h1' : β * rowIntE q μ x ≤ β * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ
    have h2 := abs_le.1 (ht x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h2.1, h2.2]
  neg_le_integral_φ := by
    have hi1 : Integrable (fun x => β * rowIntE q μ x) μ :=
      Integrable.of_bound (hK.wr1_measurable_rowInt.const_mul β).aestronglyMeasurable (β * a)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ (hK.wr1_rowInt_nonneg x))]
          exact mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ)
    have hi2 : Integrable (fun x => inner ℝ t (Xi μ Ψ x)) μ :=
      Integrable.of_bound (wr12b_measurable_inner_Xi h t).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact ht x)
    rw [integral_add hi1 hi2, wr12b_integral_inner_Xi h t, add_zero]
    have : 0 ≤ ∫ x, β * rowIntE q μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hβ (hK.wr1_rowInt_nonneg x)
    simpa using this
  integrable_q := hK.wr1_integrable_row
  row_le := fun x => hK.wr1_rowInt_le ha x

section Fields

variable (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B) (t : H)
  (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ 1)

@[simp] lemma weakPotE_φ (x : Euc d) :
    (weakPotE hK ha hβ h t ht).φ x = β * rowIntE q μ x + inner ℝ t (Xi μ Ψ x) := rfl

@[simp] lemma weakPotE_q : (weakPotE hK ha hβ h t ht).q = q := rfl

@[simp] lemma weakPotE_M : (weakPotE hK ha hβ h t ht).M = β * a + 1 := rfl

@[simp] lemma weakPotE_M' : (weakPotE hK ha hβ h t ht).M' = 0 := rfl

@[simp] lemma weakPotE_γ : (weakPotE hK ha hβ h t ht).γ = a := rfl

lemma weakPotE_pairEnergy {n : ℕ} (y : Fin n → Euc d) :
    External.pairEnergy (weakPotE hK ha hβ h t ht) y = External.pairEnergy (mkV_E hK ha hβ) y := rfl

end Fields

/-! ### `R_N = fieldLaw` -/

/-- The calibrated weak reference `R_N` is the weak ensemble of `weakPotE` with `φ = β q*μ + ⟪t_N, Ξ⟫`,
pair coefficient `β / N` and `N` free coordinates (`CalibratedReference.lean:1000 RefHyp.RN_eq_fieldLaw`). -/
theorem RN_eq_fieldLaw (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B)
    (hN : 0 < N) (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) :
    RN q μ Ψ β N = fieldLaw (weakPotE hK ha hβ h (tN q μ Ψ β N) ht)
      (weakPotE hK ha hβ h (tN q μ Ψ β N) ht).φ (β / N) N := by
  obtain ⟨V, hV⟩ : ∃ V : WeakPotential μ, V = weakPotE hK ha hβ h (tN q μ Ψ β N) ht := ⟨_, rfl⟩
  obtain ⟨V0, hV0⟩ : ∃ V0 : WeakPotential μ, V0 = mkV_E hK ha hβ := ⟨_, rfl⟩
  rw [← hV]
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ0 := isField_pinField V0 hlam (fun e : Empty => e.elim)
  have hVφ : V.φ = fun x => β * rowIntE q μ x + inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x) := by
    rw [hV]; rfl
  have hVq : V.q = q := by rw [hV]; rfl
  have hV0q : V0.q = q := by rw [hV0]; rfl
  have hpe : ∀ y : Fin N → Euc d, External.pairEnergy V y = External.pairEnergy V0 y := by
    intro y; simp only [External.pairEnergy, hVq, hV0q]
  have hψ : IsField μ V.φ V.M V.M' :=
    ⟨V.measurable_φ, V.φ_le, V.integrable_φ, V.neg_le_integral_φ⟩
  have hR0 : pairGibbsLawE q N β μ
      = fieldLaw V0 (pinField V0 (β / N) (fun e : Empty => e.elim)) (β / N) N := by
    rw [hV0]; exact pairGibbsLawE_eq_pinnedLaw_E hK ha hβ hN
  have hpin : pinField V0 (β / N) (fun e : Empty => e.elim) = fun x => β * rowIntE q μ x := by
    funext x; simp [pinField, hV0, mkV_E]
  have hint0 := wr12b_integrable_exp_field (V := V0) hψ0 hlam N
  rw [hpin] at hR0 hint0
  rw [wr12b_fieldLaw_eq_tilted (V := V0) (ψ := fun x => β * rowIntE q μ x) (lam := β / N) (n := N) hint0] at hR0
  have hint := wr12b_integrable_exp_field (V := V) hψ hlam N
  unfold RN
  rw [hR0, tilted_tilted hint0, wr12b_fieldLaw_eq_tilted (V := V) (ψ := V.φ) (lam := β / N) (n := N) hint]
  congr 1
  funext X
  simp only [Pi.add_apply, Yf, hVφ, Finset.sum_add_distrib, hpe]
  ring

/-- `R_N` as a pinned ensemble with the empty pin configuration. -/
theorem RN_eq_pinnedLaw (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B)
    (hN : 0 < N) (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 1) :
    RN q μ Ψ β N = pinnedLaw (weakPotE hK ha hβ h (tN q μ Ψ β N) ht) (β / N) N
      (fun e : Empty => e.elim) := by
  rw [RN_eq_fieldLaw hK ha hβ h hN ht]
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField]

end Pot

end HRS.MS.Wr
