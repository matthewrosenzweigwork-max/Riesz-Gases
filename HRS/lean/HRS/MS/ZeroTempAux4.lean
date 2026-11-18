import HRS.MS.ZeroTempAux3

/-!
# SA11, packet A4: extension of bounded linear maps from the jets, evaluation functionals

* `sa11_ext ℓ`: the continuous extension `W^{m,p} → E` of a linear map `ℓ : C_c^∞ → E` bounded by `C ‖J φ‖`
  (`LinearMap.extendOfNorm`); `sa11_ext_apply`, `sa11_ext_norm_le`, `sa11_ext_unique`.
* `sa11_evMeas μ` (`φ ↦ ∫ φ dμ` for a probability measure `μ`), `sa11_ev x` (`φ ↦ φ(x)`), `‖ev x - ev y‖ ≤ C‖x - y‖`.
* `sa11_ae_eq_of_repr`: two `W^{-m,p'}`-valued maps that agree on every jet a.s. (for each jet separately) are a.s. equal
  (a countable dense family of jets gives one null set).
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa11_wJet_zero (f : Euc d → ℝ) (x : Euc d) : wJet m f x (wZero d m) = f x := by
  show partialDeriv (wZero d m).2 f x = f x
  rw [show partialDeriv (wZero d m).2 f = f from sa11_partialDeriv_zero (wZero d m).2 f]

theorem sa11_isProb {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := by
  have hint : Integrable ρ :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

/-! ### The extension operator -/

section Ext

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The continuous extension to `W^{m,p}` of a linear map on `C_c^∞` bounded by the jet norm. -/
def sa11_ext (ℓ : sa11_V d →ₗ[ℝ] E) : WmpSpace d m p →L[ℝ] E :=
  ℓ.extendOfNorm (sa11_J (d := d) (m := m) (p := p))

theorem sa11_ext_apply (ℓ : sa11_V d →ₗ[ℝ] E) {C : ℝ}
    (hC : ∀ φ, ‖ℓ φ‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖) (φ : sa11_V d) :
    sa11_ext (m := m) (p := p) ℓ (sa11_J (m := m) (p := p) φ) = ℓ φ :=
  LinearMap.extendOfNorm_eq (sa11_denseRange_J (d := d) (m := m) (p := p)) ⟨C, hC⟩ φ

theorem sa11_ext_norm_le (ℓ : sa11_V d →ₗ[ℝ] E) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ φ, ‖ℓ φ‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖) :
    ‖sa11_ext (m := m) (p := p) ℓ‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (sa11_denseRange_J (d := d) (m := m) (p := p)) hC0 hC

theorem sa11_ext_unique (ℓ : sa11_V d →ₗ[ℝ] E) {C : ℝ}
    (hC : ∀ φ, ‖ℓ φ‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖) (L : WmpSpace d m p →L[ℝ] E)
    (hL : ∀ φ, L (sa11_J (m := m) (p := p) φ) = ℓ φ) : L = sa11_ext (m := m) (p := p) ℓ := by
  symm
  refine LinearMap.extendOfNorm_unique (sa11_denseRange_J (d := d) (m := m) (p := p)) C hC L ?_
  ext φ
  exact hL φ

/-- Two continuous linear maps on `W^{m,p}` agreeing on all jets agree. -/
theorem sa11_clm_ext {L₁ L₂ : WmpSpace d m p →L[ℝ] E}
    (h : ∀ φ, L₁ (sa11_J (m := m) (p := p) φ) = L₂ (sa11_J (m := m) (p := p) φ)) : L₁ = L₂ := by
  have : (L₁ : WmpSpace d m p → E) ∘ sa11_J (m := m) (p := p) = (L₂ : WmpSpace d m p → E) ∘ sa11_J (m := m) (p := p) :=
    funext h
  exact ContinuousLinearMap.ext (congrFun (DenseRange.equalizer sa11_denseRange_J L₁.continuous L₂.continuous this))

end Ext

/-! ### Evaluation functionals -/

section Eval

variable (hd : 1 ≤ d)

/-- the linear map `φ ↦ ∫ φ dμ` on `C_c^∞` -/
def sa11_intL (μ : Measure (Euc d)) [IsFiniteMeasure μ] : sa11_V d →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, φ.1 x ∂μ
  map_add' a b := by
    have ha := a.2.1.continuous.integrable_of_hasCompactSupport a.2.2 (μ := μ)
    have hb := b.2.1.continuous.integrable_of_hasCompactSupport b.2.2 (μ := μ)
    exact integral_add ha hb
  map_smul' c a := by
    exact integral_const_mul c _

theorem sa11_intL_bound (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m) {C : ℝ}
    (hC : ∀ φ : sa11_V d, ∀ i ≤ mStar d, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i φ.1 x‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (φ : sa11_V d) :
    ‖sa11_intL μ φ‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖ := by
  have hb : ∀ x, ‖φ.1 x‖ ≤ C * ‖sa11_J (m := m) (p := p) φ‖ := fun x => by
    have := hC φ 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => φ.1 x) (C := C * ‖sa11_J (m := m) (p := p) φ‖)
    (Filter.Eventually.of_forall hb)
  show ‖∫ x, φ.1 x ∂μ‖ ≤ _
  simpa using this

end Eval

/-! ### The evaluation functionals with the embedding constant fixed -/

section EvalConst

variable (hd : 1 ≤ d) (hm : mStar d + ⌊(d : ℝ) / p⌋₊ + 1 ≤ m)

include hd hm

/-- The embedding constant of `sa11_embed`. -/
def sa11_Cemb : ℝ := Classical.choose (sa11_embed (m := m) (p := p) hd hm)

theorem sa11_Cemb_nonneg : 0 ≤ sa11_Cemb (m := m) (p := p) hd hm :=
  (Classical.choose_spec (sa11_embed (m := m) (p := p) hd hm)).1

theorem sa11_Cemb_spec : ∀ φ : sa11_V d, ∀ i ≤ mStar d, ∀ x : Euc d,
    ‖iteratedFDeriv ℝ i φ.1 x‖ ≤ sa11_Cemb (m := m) (p := p) hd hm * ‖sa11_J (m := m) (p := p) φ‖ :=
  (Classical.choose_spec (sa11_embed (m := m) (p := p) hd hm)).2

/-- `φ ↦ ∫ φ dμ`, extended to `W^{m,p}`. -/
def sa11_evMeas (μ : Measure (Euc d)) [IsProbabilityMeasure μ] : WmpSpace d m p →L[ℝ] ℝ :=
  sa11_ext (sa11_intL μ)

theorem sa11_evMeas_apply (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (φ : sa11_V d) :
    sa11_evMeas (m := m) (p := p) μ (sa11_J (m := m) (p := p) φ) = ∫ x, φ.1 x ∂μ :=
  sa11_ext_apply (sa11_intL μ) (sa11_intL_bound hm (sa11_Cemb_spec (m := m) (p := p) hd hm) μ) φ

theorem sa11_evMeas_norm_le (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    ‖sa11_evMeas (m := m) (p := p) μ‖ ≤ sa11_Cemb (m := m) (p := p) hd hm :=
  sa11_ext_norm_le (sa11_intL μ) (sa11_Cemb_nonneg hd hm)
    (sa11_intL_bound hm (sa11_Cemb_spec (m := m) (p := p) hd hm) μ)

/-- evaluation at a point -/
def sa11_ev (x : Euc d) : WmpSpace d m p →L[ℝ] ℝ := sa11_evMeas (m := m) (p := p) (Measure.dirac x)

theorem sa11_ev_apply (x : Euc d) (φ : sa11_V d) :
    sa11_ev (m := m) (p := p) x (sa11_J (m := m) (p := p) φ) = φ.1 x := by
  unfold sa11_ev
  rw [sa11_evMeas_apply hd hm, integral_dirac]

theorem sa11_ev_norm_le (x : Euc d) : ‖sa11_ev (m := m) (p := p) x‖ ≤ sa11_Cemb (m := m) (p := p) hd hm :=
  sa11_evMeas_norm_le hd hm _

/-- `x ↦ δ_x ∈ (W^{m,p})^*` is Lipschitz. -/
theorem sa11_ev_lip (x y : Euc d) :
    ‖sa11_ev (m := m) (p := p) x - sa11_ev (m := m) (p := p) y‖ ≤
      sa11_Cemb (m := m) (p := p) hd hm * ‖x - y‖ := by
  set Cm := sa11_Cemb (m := m) (p := p) hd hm with hCm
  have hC0 : 0 ≤ Cm := sa11_Cemb_nonneg hd hm
  set ℓ : sa11_V d →ₗ[ℝ] ℝ := sa11_intL (Measure.dirac x) - sa11_intL (Measure.dirac y) with hℓ
  have hℓφ : ∀ φ : sa11_V d, ℓ φ = φ.1 x - φ.1 y := by
    intro φ
    simp [hℓ, sa11_intL, integral_dirac]
  have hbound : ∀ φ : sa11_V d, ‖ℓ φ‖ ≤ (Cm * ‖x - y‖) * ‖sa11_J (m := m) (p := p) φ‖ := by
    intro φ
    rw [hℓφ]
    have hder : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ φ.1 z‖ ≤ Cm * ‖sa11_J (m := m) (p := p) φ‖ := by
      intro z _
      have h1 := sa11_Cemb_spec (m := m) (p := p) hd hm φ 1 (by unfold mStar; omega) z
      rwa [norm_iteratedFDeriv_one] at h1
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ.1) (s := Set.univ)
      (fun z _ => (φ.2.1.differentiable (by simp)) z) hder convex_univ (Set.mem_univ y) (Set.mem_univ x)
    calc ‖φ.1 x - φ.1 y‖ ≤ Cm * ‖sa11_J (m := m) (p := p) φ‖ * ‖x - y‖ := hmv
      _ = _ := by ring
  have hEq : sa11_ev (m := m) (p := p) x - sa11_ev (m := m) (p := p) y = sa11_ext (m := m) (p := p) ℓ := by
    refine sa11_ext_unique ℓ hbound _ fun φ => ?_
    rw [ContinuousLinearMap.sub_apply, sa11_ev_apply hd hm, sa11_ev_apply hd hm, hℓφ]
  rw [hEq]
  exact sa11_ext_norm_le ℓ (mul_nonneg hC0 (norm_nonneg _)) hbound

theorem sa11_ev_continuous : Continuous (fun x : Euc d => sa11_ev (m := m) (p := p) x) := by
  have hlip : LipschitzWith ⟨sa11_Cemb (m := m) (p := p) hd hm, sa11_Cemb_nonneg (m := m) (p := p) hd hm⟩
      (fun x : Euc d => sa11_ev (m := m) (p := p) x) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact sa11_ev_lip hd hm x y
  exact hlip.continuous

end EvalConst

/-! ### Countable dense families of jets; almost sure identities -/

section AeEq

/-- A countable family of `C_c^∞` functions whose jets are dense in `W^{m,p}`. -/
theorem sa11_exists_countable_dense :
    ∃ D : Set (sa11_V d), D.Countable ∧ Dense (sa11_J (d := d) (m := m) (p := p) '' D) := by
  haveI : Fact (ENNReal.ofReal p ≠ ⊤) := ⟨ENNReal.ofReal_ne_top⟩
  obtain ⟨T, hTS, hTc, hST⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (Set.range (sa11_J (d := d) (m := m) (p := p)))).exists_countable_dense_subset
  haveI : Countable T := hTc.to_subtype
  have hex : ∀ F : T, ∃ y : sa11_V d, sa11_J (d := d) (m := m) (p := p) y = F.1 := fun F => hTS F.2
  choose ψ hψ using hex
  refine ⟨Set.range ψ, Set.countable_range ψ, ?_⟩
  have himg : sa11_J (d := d) (m := m) (p := p) '' Set.range ψ = T := by
    ext F
    constructor
    · rintro ⟨_, ⟨F', rfl⟩, rfl⟩
      rw [hψ F']
      exact F'.2
    · intro hF
      exact ⟨ψ ⟨F, hF⟩, ⟨⟨F, hF⟩, rfl⟩, hψ ⟨F, hF⟩⟩
  rw [himg, Dense]
  intro F
  have h1 : F ∈ closure (Set.range (sa11_J (d := d) (m := m) (p := p))) := sa11_denseRange_J F
  exact closure_minimal hST isClosed_closure h1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two dual-valued maps that agree on each jet almost surely (null set depending on the jet) are almost surely equal. -/
theorem sa11_ae_eq_of_repr (P : Measure Ω) (L₁ L₂ : Ω → WmpSpace d m p →L[ℝ] ℝ)
    (h : ∀ φ : sa11_V d, ∀ᵐ ζ ∂P, L₁ ζ (sa11_J (m := m) (p := p) φ) = L₂ ζ (sa11_J (m := m) (p := p) φ)) :
    ∀ᵐ ζ ∂P, L₁ ζ = L₂ ζ := by
  obtain ⟨D, hDc, hDd⟩ := sa11_exists_countable_dense (d := d) (m := m) (p := p)
  have hall : ∀ᵐ ζ ∂P, ∀ φ ∈ D, L₁ ζ (sa11_J (m := m) (p := p) φ) = L₂ ζ (sa11_J (m := m) (p := p) φ) :=
    (MeasureTheory.ae_ball_iff hDc).2 fun φ _ => h φ
  filter_upwards [hall] with ζ hζ
  have hcl : IsClosed {F : WmpSpace d m p | L₁ ζ F = L₂ ζ F} :=
    isClosed_eq (L₁ ζ).continuous (L₂ ζ).continuous
  have hsub : sa11_J (d := d) (m := m) (p := p) '' D ⊆ {F : WmpSpace d m p | L₁ ζ F = L₂ ζ F} := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact hζ φ hφ
  have hall' : ∀ F : WmpSpace d m p, L₁ ζ F = L₂ ζ F := fun F =>
    closure_minimal hsub hcl (hDd F)
  exact ContinuousLinearMap.ext hall'

/-- A bound `|L(Jφ)| ≤ b ‖Jφ‖` on each jet (almost surely, null set depending on the jet) gives `‖L‖ ≤ b` almost surely. -/
theorem sa11_norm_le_of_repr (P : Measure Ω) (L : Ω → WmpSpace d m p →L[ℝ] ℝ) (b : Ω → ℝ) (hb : ∀ ζ, 0 ≤ b ζ)
    (h : ∀ φ : sa11_V d, ∀ᵐ ζ ∂P, |L ζ (sa11_J (m := m) (p := p) φ)| ≤ b ζ * ‖sa11_J (m := m) (p := p) φ‖) :
    ∀ᵐ ζ ∂P, ‖L ζ‖ ≤ b ζ := by
  obtain ⟨D, hDc, hDd⟩ := sa11_exists_countable_dense (d := d) (m := m) (p := p)
  have hall : ∀ᵐ ζ ∂P, ∀ φ ∈ D, |L ζ (sa11_J (m := m) (p := p) φ)| ≤ b ζ * ‖sa11_J (m := m) (p := p) φ‖ :=
    (MeasureTheory.ae_ball_iff hDc).2 fun φ _ => h φ
  filter_upwards [hall] with ζ hζ
  have hcl : IsClosed {F : WmpSpace d m p | |L ζ F| ≤ b ζ * ‖F‖} :=
    isClosed_le (continuous_abs.comp (L ζ).continuous) (continuous_const.mul continuous_norm)
  have hsub : sa11_J (d := d) (m := m) (p := p) '' D ⊆ {F : WmpSpace d m p | |L ζ F| ≤ b ζ * ‖F‖} := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact hζ φ hφ
  refine (L ζ).opNorm_le_bound (hb ζ) fun F => ?_
  have := closure_minimal hsub hcl (hDd F)
  simpa [Real.norm_eq_abs] using this

end AeEq

end HRS.MS.ZeroTemp
