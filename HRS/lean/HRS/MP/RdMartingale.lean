import HRS.Whole.AppendixALemmas2
import HRS.MP.HNegInfra
import HRS.MP.KolmChentsov
import HRS.Prob.HilbertBDG
import HRS.Main.GFB3Aux9
import HRS.Uniform.Q07cAux5

/-!
# Packet MPRMART: S.A.24 on `ℝ^d`, parts (a) and (b), conditional on the kernel bound (S.A.22)

Namespace `HRS.MP.RdMart`, helper names `mrm_`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.RdMart

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra

variable {d : ℕ}

/-! ### Part I: the pairing with a smooth test as a Hilbert space functional -/

theorem mrm_pairing_add {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (F G : HNeg d Γ) :
    HNeg.pairing φ (F + G) = HNeg.pairing φ F + HNeg.pairing φ G := by
  rw [mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2]
  show (inner ℂ (mhn_psiLp hφ.2) ((F : HNegSubmodule d Γ).1 + (G : HNegSubmodule d Γ).1 :
      Lp ℂ 2 (sobolevMeasure d Γ))).re = _
  rw [inner_add_right, Complex.add_re]

theorem mrm_pairing_smul {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (c : ℝ) (F : HNeg d Γ) :
    HNeg.pairing φ (c • F) = c * HNeg.pairing φ F := by
  rw [mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2]
  show (inner ℂ (mhn_psiLp hφ.2) (c • (F : HNegSubmodule d Γ).1 :
      Lp ℂ 2 (sobolevMeasure d Γ))).re = _
  rw [inner_smul_right_eq_smul, Complex.smul_re, smul_eq_mul]

theorem mrm_pairing_zero {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) :
    HNeg.pairing φ (0 : HNeg d Γ) = 0 := by
  have := mrm_pairing_smul hφ 0 (0 : HNeg d Γ)
  simpa using this

/-- Riesz representative of the pairing with a smooth test. -/
theorem mrm_riesz {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) :
    ∃ g : HNeg d Γ, ∀ F : HNeg d Γ, inner ℝ g F = HNeg.pairing φ F := by
  let ℓ : HNeg d Γ →ₗ[ℝ] ℝ :=
    { toFun := fun F => HNeg.pairing φ F
      map_add' := mrm_pairing_add hφ
      map_smul' := fun c F => by simpa using mrm_pairing_smul hφ c F }
  let ℓc : HNeg d Γ →L[ℝ] ℝ := ℓ.mkContinuous (HRS.Whole.sobolevNorm Γ φ) (fun F => by
    have := hneg_pairing_le hφ F
    simpa [ℓ, Real.norm_eq_abs, mul_comm] using this)
  refine ⟨(InnerProductSpace.toDual ℝ (HNeg d Γ)).symm ℓc, fun F => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl


theorem mrm_grad_component (f : Euc d → ℝ) (x : Euc d) (j : Fin d) :
    gradient f x j = fderiv ℝ f x (EuclideanSpace.single j 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j 1) (y := fderiv ℝ f x)
  have h2 : inner ℝ (gradient f x) (EuclideanSpace.single j (1 : ℝ)) = gradient f x j := by
    rw [EuclideanSpace.inner_single_right]; simp
  rw [← h2]
  exact h

/-- The gradient component of the propagator is jointly measurable in `(r, x)` on `[0,t]`
(and cut off by `0` outside): either a classical adjoint solution exists, and its gradient is
continuous on `[0,t] × ℝ^d`, or the propagator is `0`. -/
theorem mrm_meas_grad (Cf : WholeCoeff d) (t : ℝ) (φ : Euc d → ℝ) (j : Fin d) :
    Measurable (fun p : ℝ × Euc d =>
      if p.1 ∈ Set.Icc (0 : ℝ) t then gradient (propagatorW Cf p.1 t φ) p.2 j else 0) := by
  classical
  by_cases hex : ∃ f, IsClassicalAdjointW Cf t φ f
  · set f := hex.choose with hf
    have hspec : IsClassicalAdjointW Cf t φ f := hex.choose_spec
    have hprop : ∀ r, propagatorW Cf r t φ = f r := fun r => by
      unfold propagatorW; rw [dif_pos hex]
    have hc := hspec.cont_c2 1 (by norm_num)
    have hcont : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
        gradient (f p.1) p.2 j := by
      have h1 : (fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2 j) =
          fun p => (iteratedFDeriv ℝ 1 (f p.1) p.2) (fun _ => EuclideanSpace.single j 1) := by
        funext p
        rw [mrm_grad_component, iteratedFDeriv_one_apply]
      rw [h1]
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => Euc d) ℝ
        (fun _ => EuclideanSpace.single j 1)).continuous.comp hc
    have hmeasS : MeasurableSet (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) :=
      measurableSet_Icc.prod MeasurableSet.univ
    set F : ℝ × Euc d → ℝ := fun p =>
      if p.1 ∈ Set.Icc (0 : ℝ) t then gradient (propagatorW Cf p.1 t φ) p.2 j else 0 with hF
    refine measurable_of_restrict_of_restrict_compl hmeasS ?_ ?_
    · have h1 : Set.domRestrict (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) F =
          fun p => gradient (f (⟨p.1.1, p.2.1⟩ : Set.Icc (0 : ℝ) t)) p.1.2 j := by
        funext p
        have hp : p.1.1 ∈ Set.Icc (0 : ℝ) t := p.2.1
        simp only [Set.domRestrict_apply, hF, if_pos hp, hprop]
      rw [h1]
      have hg : Continuous (fun p : ↥(Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))) =>
          ((⟨p.1.1, p.2.1⟩ : Set.Icc (0 : ℝ) t), p.1.2)) := by
        refine Continuous.prodMk ?_ ?_
        · exact Continuous.subtype_mk (continuous_fst.comp (continuous_subtype_val)) _
        · exact continuous_snd.comp continuous_subtype_val
      exact (hcont.comp hg).measurable
    · have h1 : Set.domRestrict (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d)))ᶜ F = fun _ => 0 := by
        funext p
        have hp : p.1.1 ∉ Set.Icc (0 : ℝ) t := fun h => p.2 ⟨h, Set.mem_univ _⟩
        simp only [Set.domRestrict_apply, hF, if_neg hp]
      rw [h1]
      exact measurable_const
  · have : ∀ r, propagatorW Cf r t φ = 0 := fun r => by
      unfold propagatorW; rw [dif_neg hex]
    have h0 : ∀ (r : ℝ) (x : Euc d), gradient (propagatorW Cf r t φ) x j = 0 := by
      intro r x
      rw [this r]
      have : gradient (0 : Euc d → ℝ) x = 0 := gradient_fun_const x (0 : ℝ)
      rw [this]; rfl
    simp only [h0, ite_self]
    exact measurable_const

/-! ### Frames and measurability of `H^{-Γ}`-valued maps through pairings -/

/-- A smooth Parseval system of `HNeg d Γ`. -/
def mrm_e (d : ℕ) (Γ : ℝ) : ℕ → Euc d → ℝ := Classical.choose (hneg_parseval d Γ)

theorem mrm_e_test (Γ : ℝ) (ℓ : ℕ) : IsSobolevTest Γ (mrm_e d Γ ℓ) :=
  (Classical.choose_spec (hneg_parseval d Γ)).1 ℓ

theorem mrm_e_parseval (Γ : ℝ) (F : HNeg d Γ) :
    HasSum (fun ℓ => (HNeg.pairing (mrm_e d Γ ℓ) F) ^ 2) (‖F‖ ^ 2) :=
  (Classical.choose_spec (hneg_parseval d Γ)).2 F

/-- Two `H^{-Γ}`-valued maps with a.s. equal pairings against the Parseval system (on an event
`p`) agree a.s. (on `p`). -/
theorem mrm_ae_eq_of_pairings {Γ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {F G : Ω → HNeg d Γ} (p : Ω → Prop)
    (h : ∀ ℓ, ∀ᵐ ζ ∂μ, p ζ → HNeg.pairing (mrm_e d Γ ℓ) (F ζ) =
      HNeg.pairing (mrm_e d Γ ℓ) (G ζ)) : ∀ᵐ ζ ∂μ, p ζ → F ζ = G ζ := by
  filter_upwards [ae_all_iff.2 h] with ζ hζ hp
  have hs := mrm_e_parseval Γ (F ζ - G ζ)
  have h0 : ∀ ℓ, HNeg.pairing (mrm_e d Γ ℓ) (F ζ - G ζ) = 0 := fun ℓ => by
    rw [mhn_pairing_sub (mrm_e_test Γ ℓ), hζ ℓ hp, sub_self]
  have hs0 : HasSum (fun _ : ℕ => (0 : ℝ)) (‖F ζ - G ζ‖ ^ 2) := by
    convert hs using 2 with ℓ
    rw [h0 ℓ]; simp
  have := hs0.unique hasSum_zero
  have h2 : ‖F ζ - G ζ‖ = 0 := by
    have := pow_eq_zero_iff (n := 2) (a := ‖F ζ - G ζ‖) (by norm_num) |>.1 this
    exact this
  exact sub_eq_zero.1 (norm_eq_zero.1 h2)

theorem mrm_measurable_of_pairings {Γ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Ω → HNeg d Γ}
    (h : ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ → Measurable (fun ζ => HNeg.pairing φ (F ζ))) :
    Measurable F := by
  obtain ⟨φ, hφ, -, hnorm⟩ := hneg_norming d Γ
  exact (hneg_measurable_iff hφ hnorm F).2 fun n => h _ (hφ n)

/-! ### Part II: the integrands of the thermal stochastic convolution -/

/-- The kernel family: Riesz representatives with the pairing, increment and sup bounds. -/
structure MrmKern (Cf : WholeCoeff d) (T : ℝ) (q : ℕ) (C₁ : ℝ)
    (Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)) : Prop where
  nonneg : 0 ≤ C₁
  pair : ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ (x : Euc d) (φ : Euc d → ℝ),
    IsSobolevTest (q : ℝ) φ → HNeg.pairing φ (Kern j r t x) = gradient (propagatorW Cf r t φ) x j
  incr : ∀ (j : Fin d) (r s' t : ℝ), 0 ≤ r → r ≤ s' → s' ≤ t → t ≤ T → ∀ x : Euc d,
    ‖Kern j r t x - Kern j r s' x‖ ≤ C₁ * |t - s'| * (1 + ‖x‖)
  bdd : ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d, ‖Kern j r t x‖ ≤ C₁

theorem mrmKern_exists (Cf : WholeCoeff d) (T : ℝ) (q : ℕ) (C₁ : ℝ)
    (hker : KernelBoundRd Cf T q C₁) :
    ∃ Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ), MrmKern Cf T q |C₁| Kern := by
  classical
  obtain ⟨h1, h2⟩ := hker
  let Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ) := fun j r t x =>
    if h : 0 ≤ r ∧ r ≤ t ∧ t ≤ T then (h1 j r t h.1 h.2.1 h.2.2 x).exists.choose else 0
  have hpair : ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ (x : Euc d) (φ : Euc d → ℝ),
      IsSobolevTest (q : ℝ) φ → HNeg.pairing φ (Kern j r t x) =
        gradient (propagatorW Cf r t φ) x j := by
    intro j r t hr hrt htT x φ hφ
    have h : 0 ≤ r ∧ r ≤ t ∧ t ≤ T := ⟨hr, hrt, htT⟩
    simp only [Kern, dif_pos h]
    exact (h1 j r t hr hrt htT x).exists.choose_spec φ hφ
  have hb := h2 Kern hpair
  refine ⟨Kern, ⟨abs_nonneg _, hpair, fun j r s' t hr hrs hst htT x => ?_,
    fun j r t hr hrt htT x => ?_⟩⟩
  · refine (hb j r s' t hr hrs hst htT x).1.trans ?_
    gcongr
    exact le_abs_self _
  · exact (hb j r t t hr hrt le_rfl htT x).2.trans (le_abs_self _)

section Integrand

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {N : ℕ}

/-- The scalar integrand of `IsStochConvW`. -/
def mrmPhi (Cf : WholeCoeff d) (cN : ℝ) (t : ℝ) (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (φ : Euc d → ℝ) : ℝ → Ω → Fin N × Fin d → ℝ :=
  fun r ζ ia => if r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ then
    cN * gradient (propagatorW Cf r t φ) (X (Real.toNNReal r) ζ ia.1) ia.2 else 0

/-- The `H^{-q}`-valued integrand `c_N K_j^{r,t}(x_i^r) 1_{r ≤ t ∧ τ}`. -/
def mrmZ {q : ℕ} (Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)) (cN : ℝ) (t : ℝ) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → Fin N × Fin d → HNeg d (q : ℝ) :=
  fun r ζ ia => if r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ then
    cN • Kern ia.2 r t (X (Real.toNNReal r) ζ ia.1) else 0

variable {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)}

theorem mrmZ_pair (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) {t : ℝ} (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    (r : ℝ) (ζ : Ω) (ia : Fin N × Fin d) :
    HNeg.pairing φ (mrmZ Kern cN t τ X r ζ ia) = mrmPhi Cf cN t τ X φ r ζ ia := by
  unfold mrmZ mrmPhi
  by_cases h : r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ
  · simp only [if_pos h]
    rw [mrm_pairing_smul hφ, hK.pair _ r t h.1.1 h.1.2 htT _ φ hφ]
  · simp only [if_neg h]
    exact mrm_pairing_zero hφ

theorem mrmZ_norm (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) {t : ℝ} (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (r : ℝ) (ζ : Ω) (ia : Fin N × Fin d) :
    ‖mrmZ Kern cN t τ X r ζ ia‖ ≤ |cN| * C₁ := by
  unfold mrmZ
  by_cases h : r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ
  · simp only [if_pos h]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK.bdd _ r t h.1.1 h.1.2 htT _) (abs_nonneg _)
  · simp only [if_neg h, norm_zero]
    exact mul_nonneg (abs_nonneg _) hK.nonneg

theorem mrmPhi_progressive {ℱ : Filtration ℝ mΩ} (cN : ℝ) {t : ℝ} (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0)) (φ : Euc d → ℝ)
    (ia : Fin N × Fin d) :
    IsProgressive ℱ (fun r ζ => mrmPhi Cf cN t τ X φ r ζ ia) := by
  have hXi : IsProgressive ℱ (fun r ζ => ofNNRealTime X r ζ ia.1) := fun i =>
    (measurable_pi_apply ia.1).comp (hXp i)
  have hg := isProgressive_comp_measurable' (fun r ζ => ofNNRealTime X r ζ ia.1) hXi
    (fun r (x : Euc d) => if r ∈ Set.Icc (0 : ℝ) t then gradient (propagatorW Cf r t φ) x ia.2
      else 0) (mrm_meas_grad Cf t φ ia.2)
  have hprod := hτ.mul ((isProgressive_const ℱ cN).mul hg)
  have heq : (fun r ζ => mrmPhi Cf cN t τ X φ r ζ ia) = fun r ζ =>
      (if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0) * (cN * (if r ∈ Set.Icc (0 : ℝ) t then
        gradient (propagatorW Cf r t φ) (ofNNRealTime X r ζ ia.1) ia.2 else 0)) := by
    funext r ζ
    unfold mrmPhi
    by_cases h1 : r ∈ Set.Icc (0 : ℝ) t
    · have hT' : ¬ T < r := not_lt.2 (h1.2.trans htT)
      by_cases h2 : r ≤ τ ζ <;> simp [h1, h2, hT', ofNNRealTime]
    · simp [h1, ofNNRealTime]
  rw [heq]
  exact hprod

theorem mrmZ_progressive {ℱ : Filtration ℝ mΩ} (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) {t : ℝ}
    (htT : t ≤ T) (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0))
    (ia : Fin N × Fin d) :
    IsProgressive ℱ (fun r ζ => mrmZ Kern cN t τ X r ζ ia) := by
  intro i
  refine @mrm_measurable_of_pairings d (q : ℝ) (Set.Iic i × Ω)
    (Subtype.instMeasurableSpace.prod (ℱ i)) (fun p => mrmZ Kern cN t τ X p.1 p.2 ia) ?_
  intro φ hφ
  have h : (fun p : Set.Iic i × Ω => HNeg.pairing φ (mrmZ Kern cN t τ X p.1 p.2 ia)) =
      fun p => mrmPhi Cf cN t τ X φ p.1 p.2 ia := by
    funext p
    exact mrmZ_pair hK cN htT τ X hφ _ _ ia
  rw [h]
  exact mrmPhi_progressive cN htT τ X hXp hτ φ ia i

end Integrand

/-! ### Part III: the Hilbert-valued Itô integral of a bounded progressive integrand -/

section HilbertIto

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {κ : Type} [Fintype κ]

theorem mrm_isHS_of_bdd {Z : ℝ → Ω → κ → H} (hp : ∀ k, IsProgressive ℱ (fun r ω => Z r ω k))
    (B : ℝ) (hB : ∀ r ω k, ‖Z r ω k‖ ≤ B) (T' : ℝ) : IsHSIntegrand P ℱ T' Z := by
  refine ⟨hp, fun r ω => Summable.of_finite, ?_⟩
  have hpt : ∀ r ω, ∑' k : κ, ‖Z r ω k‖ₑ ^ 2 ≤ (Fintype.card κ : ℝ≥0∞) * ENNReal.ofReal B ^ 2 := by
    intro r ω
    rw [tsum_fintype]
    calc ∑ k : κ, ‖Z r ω k‖ₑ ^ 2 ≤ ∑ _k : κ, ENNReal.ofReal B ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine pow_le_pow_left' ?_ 2
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hB r ω k)
      _ = _ := by simp
  unfold hsSqIntegralOn
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun r => hpt r ω) ?_
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, measure_univ, mul_one]
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)

/-- The scalar integrand `⟨Z, x⟩` of a bounded progressive `H`-valued integrand is in `L²`. -/
theorem mrm_isProgL2_inner {Z : ℝ → Ω → κ → H} (hp : ∀ k, IsProgressive ℱ (fun r ω => Z r ω k))
    (B : ℝ) (hB : ∀ r ω k, ‖Z r ω k‖ ≤ B) (x : H) :
    IsProgressiveL2 P ℱ (fun r ω k => inner ℝ (Z r ω k) x) := by
  refine IsProgressiveL2.of_bounded P (isProgressive_pi (u := fun k r ω => inner ℝ (Z r ω k) x)
    fun k i => ((hp k) i).inner measurable_const) (B * ‖x‖) fun r ω k => ?_
  rw [← Real.norm_eq_abs]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB r ω k) (norm_nonneg _))

open HRS.GF HRS.Uniform.Q07c in
/-- The continuous `H`-valued Itô integral of a bounded progressive integrand over a finite index
set: continuity, adaptedness, the martingale structure with covariation `hsCovForm Z`, and the
a.s. identification of its coordinates with the real Itô integrals. -/
theorem mrm_hilbert_version {W' : ℝ≥0 → Ω → κ → ℝ} (hW : IsBrownianFiltration P ℱ W')
    {Z : ℝ → Ω → κ → H} (hZ : ∀ T', IsHSIntegrand P ℱ T' Z) :
    ∃ M : ℝ → Ω → H, (∀ ω, Continuous fun τ => M τ ω) ∧ (∀ τ, Measurable[ℱ τ] (M τ)) ∧
      (∀ T', IsHilbertMartingaleWithCovariation P ℱ T' M (fun r ω => hsCovForm (Z r ω))) ∧
      ∀ (x : H) (τ : ℝ), 0 ≤ τ → (fun ω => inner ℝ (M τ ω) x) =ᵐ[P]
        itoIntegral P ℱ W' (fun r ω k => inner ℝ (Z r ω k) x) τ := by
  have hWc : IsCylindricalBrownian P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hW
  obtain ⟨Mart, hc, had, hz, hJ⟩ := gfb3_exists_hilbert_version hWc hZ
  have hMart : IsHilbertItoIntegral P ℱ W' Z Mart := by
    refine ⟨hc, had, hz, ?_⟩
    intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω h
    rw [h]
    rfl
  refine ⟨Mart, hc, had, fun T' => isHM_of_ito hWc hZ hc had hz hJ T', fun x τ hτ => ?_⟩
  exact gfb3_pair_ito hW hMart x (pc_isProgressiveL2_inner hZ x Finset.univ) hτ

end HilbertIto

section Exists

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {N : ℕ} {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)}

open HRS.GF HRS.Uniform.Q07c in
/-- Existence of a stochastic convolution in the sense of `IsStochConvW`, for any `τ` with progressive
indicator (the Hilbert-valued integral of the kernel integrand). -/
theorem mrm_exists_stochConv {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0)) :
    ∃ M : ℝ → Ω → HNeg d (q : ℝ), IsStochConvW P ℱ W' Cf cN q T X τ M := by
  have key : ∀ t : ℝ, ∃ Mt : Ω → HNeg d (q : ℝ), Measurable Mt ∧
      (t ∈ Set.Icc (0 : ℝ) T → ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        ∀ᵐ ζ ∂P, HNeg.pairing φ (Mt ζ) = itoIntegral P ℱ W' (mrmPhi Cf cN t τ X φ) t ζ) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · have hZ : ∀ T', IsHSIntegrand P ℱ T' (mrmZ Kern cN t τ X) := fun T' =>
        mrm_isHS_of_bdd (fun ia => mrmZ_progressive hK cN ht.2 τ X hXp hτ ia) (|cN| * C₁)
          (fun r ζ ia => mrmZ_norm hK cN ht.2 τ X r ζ ia) T'
      obtain ⟨M, hc, had, hM, hpair⟩ := mrm_hilbert_version hW hZ
      refine ⟨M t, (had t).mono (ℱ.le t) le_rfl, fun _ φ hφ => ?_⟩
      obtain ⟨g, hg⟩ := mrm_riesz hφ
      have hint : (fun r ω ia => inner ℝ (mrmZ Kern cN t τ X r ω ia) g) =
          mrmPhi Cf cN t τ X φ := by
        funext r ω ia
        rw [real_inner_comm, hg, mrmZ_pair hK cN ht.2 τ X hφ]
      filter_upwards [hpair g t ht.1] with ζ hζ
      rw [← hg, real_inner_comm]
      rw [hint] at hζ
      exact hζ
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h ht⟩
  choose Mt hMt hpt using key
  refine ⟨fun t => Mt t, fun t => hMt t, fun t ht φ hφ => ?_⟩
  exact hpt t ht φ hφ

end Exists

/-! ### The pointwise bound on the integrand of the difference -/

section Pointwise

variable {Ω : Type} {N : ℕ} {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)}

theorem mrm_secondMoment_empirical (hN : 0 < N) (x : EucConfig d N) :
    secondMomentOf (HRS.Whole.empirical x) = (N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := by
  unfold secondMomentOf
  exact HRS.Whole.pair_empirical hN x _

theorem mrm_secondMoment_nonneg (x : EucConfig d N) : 0 ≤ secondMomentOf (HRS.Whole.empirical x) :=
  integral_nonneg fun _ => sq_nonneg _

theorem mrm_sum_sq_bound (hN : 0 < N) (x : EucConfig d N) :
    ∑ i, (1 + ‖x i‖) ^ 2 ≤ 2 * N * (1 + secondMomentOf (HRS.Whole.empirical x)) := by
  rw [mrm_secondMoment_empirical hN]
  have h2 : ∀ i, (1 + ‖x i‖) ^ 2 ≤ 2 + 2 * ‖x i‖ ^ 2 := fun i => by
    nlinarith [sq_nonneg (1 - ‖x i‖)]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc ∑ i, (1 + ‖x i‖) ^ 2 ≤ ∑ i, (2 + 2 * ‖x i‖ ^ 2) := Finset.sum_le_sum fun i _ => h2 i
    _ = 2 * N + 2 * ∑ i, ‖x i‖ ^ 2 := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
        ring
    _ = _ := by field_simp

theorem mrm_diff_sq (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) (hN : 0 < N) (hcN : cN ^ 2 * N ≤ 2)
    {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    ∑ ia : Fin N × Fin d, ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ ^ 2 ≤
      if r ≤ τ ζ then 4 * d * C₁ ^ 2 * |t - s'| ^ 2 *
        (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) +
          (if s' < r then 2 * d * C₁ ^ 2 else 0) else 0 := by
  have hC₁ := hK.nonneg
  set x := X (Real.toNNReal r) ζ with hx
  have hm := mrm_secondMoment_nonneg x
  by_cases hrτ : r ≤ τ ζ
  · rw [if_pos hrτ]
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hA : 0 ≤ 4 * (d : ℝ) * C₁ ^ 2 * |t - s'| ^ 2 * (1 + secondMomentOf (HRS.Whole.empirical x)) := by
      positivity
    by_cases hrs : r ≤ s'
    · rw [if_neg (not_lt.2 hrs), add_zero]
      have hb : ∀ ia : Fin N × Fin d,
          ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ ≤
            |cN| * (C₁ * |t - s'| * (1 + ‖x ia.1‖)) := by
        intro ia
        unfold mrmZ
        rw [if_pos ⟨hr, hrτ⟩, if_pos ⟨⟨hr.1, hrs⟩, hrτ⟩, ← smul_sub, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hK.incr ia.2 r s' t hr.1 hrs hst htT _) (abs_nonneg _)
      calc ∑ ia : Fin N × Fin d, ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ ^ 2
          ≤ ∑ ia : Fin N × Fin d, (|cN| * (C₁ * |t - s'| * (1 + ‖x ia.1‖))) ^ 2 :=
            Finset.sum_le_sum fun ia _ => pow_le_pow_left₀ (norm_nonneg _) (hb ia) 2
        _ = d * (cN ^ 2 * (C₁ * |t - s'|) ^ 2 * ∑ i, (1 + ‖x i‖) ^ 2) := by
            rw [Fintype.sum_prod_type]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [mul_pow, mul_pow, sq_abs]
            ring
        _ ≤ d * (cN ^ 2 * (C₁ * |t - s'|) ^ 2 * (2 * N * (1 + secondMomentOf (HRS.Whole.empirical x)))) := by
            gcongr
            exact mrm_sum_sq_bound hN x
        _ = d * (cN ^ 2 * N) * (C₁ * |t - s'|) ^ 2 * (2 * (1 + secondMomentOf (HRS.Whole.empirical x))) := by
            ring
        _ ≤ d * 2 * (C₁ * |t - s'|) ^ 2 * (2 * (1 + secondMomentOf (HRS.Whole.empirical x))) := by
            gcongr
        _ = _ := by ring
    · push_neg at hrs
      rw [if_pos hrs]
      have hb : ∀ ia : Fin N × Fin d,
          ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ ≤ |cN| * C₁ := by
        intro ia
        have h0 : mrmZ Kern cN s' τ X r ζ ia = 0 := by
          unfold mrmZ
          rw [if_neg]
          rintro ⟨h1, -⟩
          exact absurd h1.2 (not_le.2 hrs)
        rw [h0, sub_zero]
        exact mrmZ_norm hK cN htT τ X r ζ ia
      calc ∑ ia : Fin N × Fin d, ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ ^ 2
          ≤ ∑ _ia : Fin N × Fin d, (|cN| * C₁) ^ 2 :=
            Finset.sum_le_sum fun ia _ => pow_le_pow_left₀ (norm_nonneg _) (hb ia) 2
        _ = (N * d) * (cN ^ 2 * C₁ ^ 2) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast
            rw [mul_pow, sq_abs]
        _ = d * (cN ^ 2 * N) * C₁ ^ 2 := by ring
        _ ≤ d * 2 * C₁ ^ 2 := by gcongr
        _ ≤ _ := by linarith
  · rw [if_neg hrτ]
    have h0 : ∀ ia : Fin N × Fin d,
        mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia = 0 := by
      intro ia
      unfold mrmZ
      rw [if_neg (fun h => hrτ h.2), if_neg (fun h => hrτ h.2), sub_zero]
    simp [h0]

end Pointwise

/-- The BDG constant for `p = 4` of the dimension-free Hilbert BDG inequality. -/
def mrmCb : ℝ := (HilbertBDG.hilbert_bdg 4 (by norm_num)).choose

theorem mrmCb_nonneg : 0 ≤ mrmCb := (HilbertBDG.hilbert_bdg 4 (by norm_num)).choose_spec.1

section BDG

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {κ : Type} [Fintype κ]

open HRS.Uniform.Q07c in
theorem mrm_bdg_four {M : ℝ → Ω → H} {Z : ℝ → Ω → κ → H} {t : ℝ} (ht : 0 ≤ t)
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M (fun r ω => hsCovForm (Z r ω))) :
    ∫⁻ ω, ‖M t ω‖ₑ ^ 4 ∂P ≤ ENNReal.ofReal mrmCb *
      ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑ k, ‖Z r ω k‖ₑ ^ 2) ^ 2 ∂P := by
  have h := (HilbertBDG.hilbert_bdg 4 (by norm_num)).choose_spec.2 Ω P ℱ H t M _ hM
  have e1 : ∀ ω, ‖M t ω‖ₑ ^ 4 ≤ (⨆ u ∈ Set.Icc (0 : ℝ) t, ‖M u ω‖ₑ) ^ (4 : ℝ) := by
    intro ω
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    exact pow_le_pow_left' (le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) t) => ‖M u ω‖ₑ) t
      ⟨ht, le_rfl⟩) 4
  have e2 : ∀ r ω, ENNReal.ofReal (traceNormForm (hsCovForm (Z r ω))) = ∑ k, ‖Z r ω k‖ₑ ^ 2 := by
    intro r ω
    rw [traceNormForm_hsCovForm_eq Summable.of_finite, tsum_fintype,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  calc ∫⁻ ω, ‖M t ω‖ₑ ^ 4 ∂P ≤ ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ) t, ‖M u ω‖ₑ) ^ (4 : ℝ) ∂P :=
        lintegral_mono e1
    _ ≤ _ := h
    _ = _ := by
        congr 1
        refine lintegral_congr fun ω => ?_
        simp only [e2]
        rw [show (4 : ℝ) / 2 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

end BDG

/-! ### The fourth moment of an increment, for `τ` with a bounded `∫ 1[r ≤ τ] (1 + m)` -/

section Fourth

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {N : ℕ} {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- an integrand vanishing after `b` has an integral that is constant after `b` -/
theorem mrm_ito_stop {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ι → ℝ} {Φ : ℝ → Ω → ι → ℝ}
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) (b : ℝ)
    (hz : ∀ r, b < r → ∀ ω k, Φ r ω k = 0) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W Φ t ω = itoIntegral P ℱ W Φ (min t b) ω := by
  have h := itoIntegral_stopIntegrand hW hΦ (τ := fun _ => (b : WithTop ℝ)) (isStoppingTime_const ℱ b)
  have e : stopIntegrand Φ (fun _ => (b : WithTop ℝ)) = Φ := by
    funext r ω
    by_cases hr : r ≤ b
    · have : ω ∈ {ω : Ω | (r : WithTop ℝ) ≤ (fun _ : Ω => (b : WithTop ℝ)) ω} := by
        simpa using hr
      simp only [stopIntegrand, Set.indicator_of_mem this]
    · funext k
      have : ω ∉ {ω : Ω | (r : WithTop ℝ) ≤ (fun _ : Ω => (b : WithTop ℝ)) ω} := by
        simpa using hr
      simp only [stopIntegrand, Set.indicator_of_notMem this, Pi.zero_apply]
      exact (hz r (not_le.1 hr) ω k).symm
  rw [e] at h
  filter_upwards [h] with ω hω t
  rw [hω t]
  exact stoppedProcess_apply_coe (M := itoIntegral P ℱ W Φ) (σ := fun _ => (b : WithTop ℝ))
    (ω := ω) (c := b) rfl t

theorem mrm_phi_eq_inner (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) {t : ℝ} (htT : t ≤ T)
    (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    {g : HNeg d (q : ℝ)} (hg : ∀ F : HNeg d (q : ℝ), inner ℝ g F = HNeg.pairing φ F) :
    (fun r ω ia => inner ℝ (mrmZ Kern cN t τ X r ω ia) g) = mrmPhi Cf cN t τ X φ := by
  funext r ω ia
  rw [real_inner_comm, hg, mrmZ_pair hK cN htT τ X hφ]

theorem mrm_phi_L2 (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) {t : ℝ} (htT : t ≤ T)
    (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0))
    {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ) :
    IsProgressiveL2 P ℱ (mrmPhi Cf cN t τ X φ) := by
  obtain ⟨g, hg⟩ := mrm_riesz hφ
  rw [← mrm_phi_eq_inner hK cN htT τ X hφ hg]
  exact mrm_isProgL2_inner (fun ia => mrmZ_progressive hK cN htT τ X hXp hτ ia) (|cN| * C₁)
    (fun r ζ ia => mrmZ_norm hK cN htT τ X r ζ ia) g

open HRS.GF HRS.Uniform.Q07c in
/-- The increment `M t - M s'` of a stochastic convolution is a.s. the time-`t` value of the
Hilbert-valued integral of the difference of the two kernel integrands. -/
theorem mrm_diff_exists (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern)
    (cN : ℝ) (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N) (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0))
    {M : ℝ → Ω → HNeg d (q : ℝ)} (hM : IsStochConvW P ℱ W' Cf cN q T X τ M)
    {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) :
    ∃ M' : ℝ → Ω → HNeg d (q : ℝ),
      (∀ T', IsHilbertMartingaleWithCovariation P ℱ T' M' (fun r ω => hsCovForm
        (fun ia => mrmZ Kern cN t τ X r ω ia - mrmZ Kern cN s' τ X r ω ia))) ∧
      ∀ᵐ ζ ∂P, M' t ζ = M t ζ - M s' ζ := by
  have h0t : 0 ≤ t := hs'.trans hst
  have hsT : s' ≤ T := hst.trans htT
  have hZdp : ∀ ia : Fin N × Fin d, IsProgressive ℱ
      (fun r ω => mrmZ Kern cN t τ X r ω ia - mrmZ Kern cN s' τ X r ω ia) := fun ia i =>
    (mrmZ_progressive hK cN htT τ X hXp hτ ia i).sub (mrmZ_progressive hK cN hsT τ X hXp hτ ia i)
  have hB : ∀ r ω (ia : Fin N × Fin d),
      ‖mrmZ Kern cN t τ X r ω ia - mrmZ Kern cN s' τ X r ω ia‖ ≤ |cN| * C₁ + |cN| * C₁ :=
    fun r ω ia => (norm_sub_le _ _).trans
      (add_le_add (mrmZ_norm hK cN htT τ X r ω ia) (mrmZ_norm hK cN hsT τ X r ω ia))
  obtain ⟨M', hc, had, hMc, hpair⟩ := mrm_hilbert_version hW
    (fun T' => mrm_isHS_of_bdd hZdp (|cN| * C₁ + |cN| * C₁) hB T')
  refine ⟨M', hMc, ?_⟩
  have hae : ∀ ℓ, ∀ᵐ ζ ∂P, True → HNeg.pairing (mrm_e d (q : ℝ) ℓ) (M' t ζ) =
      HNeg.pairing (mrm_e d (q : ℝ) ℓ) (M t ζ - M s' ζ) := by
    intro ℓ
    have hφ := mrm_e_test (d := d) (q : ℝ) ℓ
    obtain ⟨g, hg⟩ := mrm_riesz hφ
    have ht : t ∈ Set.Icc (0 : ℝ) T := ⟨h0t, htT⟩
    have hs : s' ∈ Set.Icc (0 : ℝ) T := ⟨hs', hsT⟩
    have hΦt := mrm_phi_L2 (P := P) hK cN htT τ X hXp hτ hφ
    have hΦs := mrm_phi_L2 (P := P) hK cN hsT τ X hXp hτ hφ
    have hz : ∀ r, s' < r → ∀ ω k, mrmPhi Cf cN s' τ X (mrm_e d (q : ℝ) ℓ) r ω k = 0 := by
      intro r hr ω k
      unfold mrmPhi
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact absurd h1.2 (not_le.2 hr)
    have hint : (fun r ω ia => inner ℝ (mrmZ Kern cN t τ X r ω ia - mrmZ Kern cN s' τ X r ω ia) g) =
        fun r ω ia => mrmPhi Cf cN t τ X (mrm_e d (q : ℝ) ℓ) r ω ia -
          mrmPhi Cf cN s' τ X (mrm_e d (q : ℝ) ℓ) r ω ia := by
      funext r ω ia
      rw [inner_sub_left]
      have e1 := congrFun (congrFun (congrFun (mrm_phi_eq_inner hK cN htT τ X hφ hg) r) ω) ia
      have e2 := congrFun (congrFun (congrFun (mrm_phi_eq_inner hK cN hsT τ X hφ hg) r) ω) ia
      rw [e1, e2]
    have h4 : ∀ᵐ ζ ∂P, HNeg.pairing (mrm_e d (q : ℝ) ℓ) (M t ζ) =
        itoIntegral P ℱ W' (mrmPhi Cf cN t τ X (mrm_e d (q : ℝ) ℓ)) t ζ := hM.2 t ht _ hφ
    have h5 : ∀ᵐ ζ ∂P, HNeg.pairing (mrm_e d (q : ℝ) ℓ) (M s' ζ) =
        itoIntegral P ℱ W' (mrmPhi Cf cN s' τ X (mrm_e d (q : ℝ) ℓ)) s' ζ := hM.2 s' hs _ hφ
    filter_upwards [hpair g t h0t, itoIntegral_sub hW hΦt hΦs, mrm_ito_stop hW hΦs s' hz, h4, h5]
      with ζ h1 h2 h3 h4 h5 _
    rw [mhn_pairing_sub hφ, h4, h5, ← hg, real_inner_comm, h1, hint, h2 t, h3 t,
      min_eq_right hst]
  filter_upwards [mrm_ae_eq_of_pairings (fun _ => True) hae] with ζ hζ
  exact hζ trivial


theorem mrm_inner_le (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ) (hN : 0 < N) (hcN : cN ^ 2 * N ≤ 2)
    {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {L : ℝ}
    (hLζ : ∫⁻ r in Set.Icc (0 : ℝ) T, (if r ≤ τ ζ then ENNReal.ofReal
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) ≤
        ENNReal.ofReal L) (hL0 : 0 ≤ L) :
    ∫⁻ r in Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d,
      ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ₑ ^ 2 ≤
      ENNReal.ofReal (4 * d * C₁ ^ 2 * |t - s'| ^ 2 * L + 2 * d * C₁ ^ 2 * (t - s')) := by
  set A : ℝ := 4 * (d : ℝ) * C₁ ^ 2 * |t - s'| ^ 2 with hAdef
  set b : ℝ := 2 * (d : ℝ) * C₁ ^ 2 with hbdef
  have hA : 0 ≤ A := by positivity
  have hb : 0 ≤ b := by positivity
  have hts : 0 ≤ t - s' := sub_nonneg.2 hst
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d,
      ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ₑ ^ 2 ≤
        ENNReal.ofReal A * (if r ≤ τ ζ then ENNReal.ofReal
          (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) +
        ENNReal.ofReal b * (Set.Ioi s').indicator (fun _ => (1 : ℝ≥0∞)) r := by
    intro r hr
    have h := mrm_diff_sq hK cN hN hcN hs' hst htT τ X ζ hr
    have hm := mrm_secondMoment_nonneg (X (Real.toNNReal r) ζ)
    have e : ∑ ia : Fin N × Fin d,
        ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ₑ ^ 2 =
        ENNReal.ofReal (∑ ia : Fin N × Fin d,
          ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      refine Finset.sum_congr rfl fun ia _ => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [e]
    by_cases hrτ : r ≤ τ ζ
    · rw [if_pos hrτ] at h ⊢
      refine (ENNReal.ofReal_le_ofReal h).trans ?_
      have hAm : 0 ≤ A * (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) := by
        positivity
      by_cases hsr : s' < r
      · rw [if_pos hsr]
        have : (Set.Ioi s').indicator (fun _ => (1 : ℝ≥0∞)) r = 1 := by
          simp [Set.indicator, hsr]
        rw [this, mul_one, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add hAm hb]
      · rw [if_neg hsr]
        have : (Set.Ioi s').indicator (fun _ => (1 : ℝ≥0∞)) r = 0 := by
          simp [Set.indicator, hsr]
        rw [this, mul_zero, add_zero, add_zero, ← ENNReal.ofReal_mul hA]
    · rw [if_neg hrτ] at h ⊢
      refine (ENNReal.ofReal_le_ofReal h).trans ?_
      simp
  have hind : ∫⁻ r in Set.Icc (0 : ℝ) t, (Set.Ioi s').indicator (fun _ => (1 : ℝ≥0∞)) r ≤
      ENNReal.ofReal (t - s') := by
    rw [lintegral_indicator_const measurableSet_Ioi, one_mul,
      Measure.restrict_apply measurableSet_Ioi]
    refine (measure_mono (t := Set.Ioc s' t) ?_).trans (by rw [Real.volume_Ioc])
    rintro r ⟨hrs, -, hrt⟩
    exact ⟨hrs, hrt⟩
  have hmeas : Measurable fun r : ℝ => ENNReal.ofReal b * (Set.Ioi s').indicator
      (fun _ => (1 : ℝ≥0∞)) r :=
    (measurable_const.indicator measurableSet_Ioi).const_mul _
  calc ∫⁻ r in Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d,
        ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ₑ ^ 2
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, (ENNReal.ofReal A * (if r ≤ τ ζ then ENNReal.ofReal
          (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) +
        ENNReal.ofReal b * (Set.Ioi s').indicator (fun _ => (1 : ℝ≥0∞)) r) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = (∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal A * (if r ≤ τ ζ then ENNReal.ofReal
          (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0)) +
        ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal b * (Set.Ioi s').indicator
          (fun _ => (1 : ℝ≥0∞)) r := lintegral_add_right _ hmeas
    _ = ENNReal.ofReal A * (∫⁻ r in Set.Icc (0 : ℝ) t, (if r ≤ τ ζ then ENNReal.ofReal
          (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0)) +
        ENNReal.ofReal b * ∫⁻ r in Set.Icc (0 : ℝ) t, (Set.Ioi s').indicator
          (fun _ => (1 : ℝ≥0∞)) r := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal L + ENNReal.ofReal b * ENNReal.ofReal (t - s') := by
        exact add_le_add (mul_le_mul' le_rfl
          ((lintegral_mono_set (Set.Icc_subset_Icc_right htT)).trans hLζ))
          (mul_le_mul' le_rfl hind)
    _ = _ := by
        rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hb,
          ← ENNReal.ofReal_add (mul_nonneg hA hL0) (mul_nonneg hb hts)]


open HRS.Uniform.Q07c in
theorem mrm_fourth_aux (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ)
    (hN : 0 < N) (hcN : cN ^ 2 * N ≤ 2) (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0)) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ᵐ ζ ∂P, ∫⁻ r in Set.Icc (0 : ℝ) T, (if r ≤ τ ζ then ENNReal.ofReal
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) ≤
        ENNReal.ofReal L)
    {M : ℝ → Ω → HNeg d (q : ℝ)} (hM : IsStochConvW P ℱ W' Cf cN q T X τ M)
    {s' t : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t) (htT : t ≤ T) :
    ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (mrmCb * (8 * (d : ℝ) ^ 2 * C₁ ^ 4) * (4 * L ^ 2 * T ^ 2 + 1) *
        |t - s'| ^ 2) := by
  have h0t : 0 ≤ t := hs'.trans hst
  obtain ⟨M', hM', hae⟩ := mrm_diff_exists hW hK cN τ X hXp hτ hM hs' hst htT
  set B : ℝ := 4 * d * C₁ ^ 2 * |t - s'| ^ 2 * L + 2 * d * C₁ ^ 2 * (t - s') with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ t - s' := sub_nonneg.2 hst
    positivity
  have hT0 : t - s' ≤ T := by linarith
  have hts : 0 ≤ t - s' := sub_nonneg.2 hst
  have habs : |t - s'| = t - s' := abs_of_nonneg hts
  calc ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P = ∫⁻ ζ, ‖M' t ζ‖ₑ ^ 4 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ζ h
        rw [h]
    _ ≤ ENNReal.ofReal mrmCb * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d,
        ‖mrmZ Kern cN t τ X r ζ ia - mrmZ Kern cN s' τ X r ζ ia‖ₑ ^ 2) ^ 2 ∂P :=
        mrm_bdg_four (Z := fun r ω ia => mrmZ Kern cN t τ X r ω ia - mrmZ Kern cN s' τ X r ω ia)
          h0t (hM' t)
    _ ≤ ENNReal.ofReal mrmCb * ∫⁻ _ζ, ENNReal.ofReal B ^ 2 ∂P := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [hL] with ζ hLζ
        exact pow_le_pow_left' (mrm_inner_le hK cN hN hcN hs' hst htT τ X ζ hLζ hL0) 2
    _ = ENNReal.ofReal (mrmCb * B ^ 2) := by
        rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_pow hB0,
          ← ENNReal.ofReal_mul mrmCb_nonneg]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : B ^ 2 ≤ 8 * (d : ℝ) ^ 2 * C₁ ^ 4 * (4 * L ^ 2 * T ^ 2 + 1) * |t - s'| ^ 2 := by
          rw [habs]
          have h1 : (t - s') ^ 2 ≤ T ^ 2 := by
            have : 0 ≤ t - s' := hts
            nlinarith
          have h2 : (t - s') ^ 4 ≤ T ^ 2 * (t - s') ^ 2 := by
            calc (t - s') ^ 4 = (t - s') ^ 2 * (t - s') ^ 2 := by ring
              _ ≤ T ^ 2 * (t - s') ^ 2 := by gcongr
          have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 * C₁ ^ 4 := by positivity
          have e : B ^ 2 ≤ 2 * (4 * d * C₁ ^ 2 * (t - s') ^ 2 * L) ^ 2 +
              2 * (2 * d * C₁ ^ 2 * (t - s')) ^ 2 := by
            rw [hB, habs]
            nlinarith [sq_nonneg (4 * (d : ℝ) * C₁ ^ 2 * (t - s') ^ 2 * L -
              2 * d * C₁ ^ 2 * (t - s'))]
          refine e.trans ?_
          have e2 : 2 * (4 * (d : ℝ) * C₁ ^ 2 * (t - s') ^ 2 * L) ^ 2 +
              2 * (2 * d * C₁ ^ 2 * (t - s')) ^ 2 =
              ((d : ℝ) ^ 2 * C₁ ^ 4) * (32 * L ^ 2 * (t - s') ^ 4 + 8 * (t - s') ^ 2) := by ring
          rw [e2]
          have e3 : 8 * (d : ℝ) ^ 2 * C₁ ^ 4 * (4 * L ^ 2 * T ^ 2 + 1) * (t - s') ^ 2 =
              ((d : ℝ) ^ 2 * C₁ ^ 4) * (32 * L ^ 2 * (T ^ 2 * (t - s') ^ 2) + 8 * (t - s') ^ 2) := by
            ring
          rw [e3]
          refine mul_le_mul_of_nonneg_left ?_ hd
          have : 32 * L ^ 2 * (t - s') ^ 4 ≤ 32 * L ^ 2 * (T ^ 2 * (t - s') ^ 2) := by
            gcongr
          linarith
        calc mrmCb * B ^ 2 ≤ mrmCb * (8 * (d : ℝ) ^ 2 * C₁ ^ 4 * (4 * L ^ 2 * T ^ 2 + 1) *
              |t - s'| ^ 2) := mul_le_mul_of_nonneg_left hsq mrmCb_nonneg
          _ = _ := by ring

theorem mrm_fourth (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ)
    (hN : 0 < N) (hcN : cN ^ 2 * N ≤ 2) (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0)) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ᵐ ζ ∂P, ∫⁻ r in Set.Icc (0 : ℝ) T, (if r ≤ τ ζ then ENNReal.ofReal
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) ≤
        ENNReal.ofReal L)
    {M : ℝ → Ω → HNeg d (q : ℝ)} (hM : IsStochConvW P ℱ W' Cf cN q T X τ M)
    {s' t : ℝ} (hs' : s' ∈ Set.Icc (0 : ℝ) T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (mrmCb * (8 * (d : ℝ) ^ 2 * C₁ ^ 4) * (4 * L ^ 2 * T ^ 2 + 1) *
        |t - s'| ^ 2) := by
  rcases le_total s' t with h | h
  · exact mrm_fourth_aux hW hK cN hN hcN τ X hXp hτ hL0 hL hM hs'.1 h ht.2
  · have := mrm_fourth_aux hW hK cN hN hcN τ X hXp hτ hL0 hL hM ht.1 h hs'.2
    have e : ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P = ∫⁻ ζ, ‖M s' ζ - M t ζ‖ₑ ^ 4 ∂P := by
      refine lintegral_congr fun ζ => ?_
      rw [enorm_sub_rev]
    rw [e, abs_sub_comm]
    exact this

end Fourth



/-! ### Part V: the localization time `τ_{N,L}` -/

section Theta

/-- A level crossing of the integral `u ↦ ∫_{[0,u]} g` is already seen at a rational time before `u`. -/
theorem mrm_theta_rat {g : ℝ → ℝ} {L u : ℝ} (hL : 0 ≤ L) (hu0 : 0 ≤ u)
    (h : L < ∫ s in Set.Icc (0 : ℝ) u, g s) :
    ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < u ∧ L < ∫ s in Set.Icc (0 : ℝ) q, g s := by
  have hint : IntegrableOn g (Set.Icc (0 : ℝ) u) := by
    by_contra hni
    rw [integral_undef hni] at h
    linarith
  have hupos : 0 < u := by
    rcases hu0.eq_or_lt with h0 | h0
    · subst h0
      simp at h
      linarith
    · exact h0
  have heq : ∀ v : ℝ, 0 ≤ v → ∫ s in Set.Icc (0 : ℝ) v, g s = ∫ s in (0 : ℝ)..v, g s := fun v hv => by
    rw [intervalIntegral.integral_of_le hv, integral_Icc_eq_integral_Ioc]
  have hcont : ContinuousOn (fun v => ∫ s in (0 : ℝ)..v, g s) (Set.uIcc 0 u) :=
    intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le hu0])
  rw [Set.uIcc_of_le hu0] at hcont
  have hcu := hcont u ⟨hu0, le_rfl⟩
  have h' : L < ∫ s in (0 : ℝ)..u, g s := by rwa [← heq u hu0]
  have hev := hcu.eventually (lt_mem_nhds h')
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεv⟩ := hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (u - ε / 2) < u from
    max_lt hupos (by linarith))
  have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
  have hq3 : u - ε / 2 < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq1
  refine ⟨q, hq0.le, hq2, ?_⟩
  rw [heq q hq0.le]
  refine hεv (y := (q : ℝ)) ?_ ⟨hq0.le, hq2.le⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

variable {Ω : Type*} {N : ℕ}

theorem mrm_le_tau_iff (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {T L : ℝ} (hL : 0 < L) {r : ℝ}
    (hrT : r ≤ T) :
    r ≤ tauNL T L X ζ ↔
      ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → (q : ℝ) < r → thetaN X ζ q ≤ L := by
  classical
  unfold tauNL
  by_cases h : ∃ u ∈ Set.Icc (0 : ℝ) T, L < thetaN X ζ u
  · rw [if_pos h]
    have hne : {u | u ∈ Set.Icc (0 : ℝ) T ∧ L < thetaN X ζ u}.Nonempty := by
      obtain ⟨u, hu, hlt⟩ := h
      exact ⟨u, hu, hlt⟩
    have hbdd : BddBelow {u | u ∈ Set.Icc (0 : ℝ) T ∧ L < thetaN X ζ u} :=
      ⟨0, fun u hu => hu.1.1⟩
    rw [le_csInf_iff hbdd hne]
    constructor
    · intro hall q hq0 hqT hqr
      by_contra hlt
      push Not at hlt
      have := hall q ⟨⟨hq0, hqT⟩, hlt⟩
      linarith
    · intro hall u hu
      by_contra hlt
      push Not at hlt
      obtain ⟨⟨hu0, huT⟩, hΘ⟩ := hu
      obtain ⟨q, hq0, hqu, hΘq⟩ := mrm_theta_rat hL.le hu0 hΘ
      have := hall q hq0 (by linarith) (by linarith)
      exact absurd hΘq (not_lt.2 this)
  · rw [if_neg h]
    push Not at h
    simp only [hrT, true_iff]
    intro q hq0 hqT _
    exact h q ⟨hq0, hqT⟩

end Theta

section ThetaProg

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {N : ℕ} {ℱ : Filtration ℝ mΩ}

theorem mrm_measurable_secondMoment (hN : 0 < N) :
    Measurable (fun x : EucConfig d N => secondMomentOf (HRS.Whole.empirical x)) := by
  have : (fun x : EucConfig d N => secondMomentOf (HRS.Whole.empirical x)) =
      fun x => (N : ℝ)⁻¹ * ∑ i, ‖x i‖ ^ 2 := funext fun x => mrm_secondMoment_empirical hN x
  rw [this]
  exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).norm).pow_const 2) _

theorem mrm_gF_progressive (hN : 0 < N) {X : ℝ≥0 → Ω → EucConfig d N}
    (hXp : IsProgressive ℱ (ofNNRealTime X)) :
    IsProgressive ℱ (fun r ζ => 1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) :=
  fun i => measurable_const.add ((mrm_measurable_secondMoment hN).comp (hXp i))

theorem mrm_theta_adapted (hN : 0 < N) {X : ℝ≥0 → Ω → EucConfig d N}
    (hXp : IsProgressive ℱ (ofNNRealTime X)) (u : ℝ) :
    Measurable[ℱ u] (fun ζ => thetaN X ζ u) :=
  measurable_setIntegral_progressive (mrm_gF_progressive hN hXp) u

theorem mrm_tau_progressive (hN : 0 < N) {X : ℝ≥0 → Ω → EucConfig d N}
    (hXp : IsProgressive ℱ (ofNNRealTime X)) {T L : ℝ} (hL : 0 < L) :
    IsProgressive ℱ (fun r ζ => if r ≤ tauNL T L X ζ ∨ T < r then (1 : ℝ) else 0) := by
  intro i
  let S : Set (Set.Iic i × Ω) := {p | T < (p.1 : ℝ) ∨ ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T →
    (q : ℝ) < p.1 → thetaN X p.2 q ≤ L}
  have hSq : ∀ q : ℚ, MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
      {p : Set.Iic i × Ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → (q : ℝ) < p.1 → thetaN X p.2 q ≤ L} := by
    intro q
    by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T
    · by_cases hqi : (q : ℝ) ≤ i
      · have h1 : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
            {p : Set.Iic i × Ω | (p.1 : ℝ) ≤ q} :=
          (measurable_subtype_coe.comp measurable_fst) measurableSet_Iic
        have h2 : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
            {p : Set.Iic i × Ω | thetaN X p.2 q ≤ L} := by
          have hm : @Measurable (Set.Iic i × Ω) Ω (Subtype.instMeasurableSpace.prod (ℱ i)) (ℱ i)
              Prod.snd := @measurable_snd (Set.Iic i) Ω Subtype.instMeasurableSpace (ℱ i)
          have hθ : Measurable[ℱ i] (fun ζ => thetaN X ζ q) :=
            (mrm_theta_adapted hN hXp q).mono (ℱ.mono hqi) le_rfl
          exact (hθ.comp hm) measurableSet_Iic
        have : {p : Set.Iic i × Ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → (q : ℝ) < p.1 →
            thetaN X p.2 q ≤ L} = {p : Set.Iic i × Ω | (p.1 : ℝ) ≤ q} ∪
              {p : Set.Iic i × Ω | thetaN X p.2 q ≤ L} := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_union, hq.1, hq.2, forall_const]
          constructor
          · intro h
            by_cases hp : (q : ℝ) < p.1
            · exact Or.inr (h hp)
            · exact Or.inl (not_lt.1 hp)
          · rintro (h | h) hp
            · exact absurd hp (not_lt.2 h)
            · exact h
        rw [this]
        exact h1.union h2
      · have : {p : Set.Iic i × Ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → (q : ℝ) < p.1 →
            thetaN X p.2 q ≤ L} = Set.univ := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          intro _ _ hp
          exact absurd (lt_of_lt_of_le hp p.1.2).le hqi
        rw [this]
        exact MeasurableSet.univ
    · have : {p : Set.Iic i × Ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → (q : ℝ) < p.1 →
          thetaN X p.2 q ≤ L} = Set.univ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h1, h2⟩ hq
      rw [this]
      exact MeasurableSet.univ
  have hSm : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)] S := by
    have hT1 : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
        {p : Set.Iic i × Ω | T < (p.1 : ℝ)} :=
      (measurable_subtype_coe.comp measurable_fst) measurableSet_Ioi
    have : S = {p : Set.Iic i × Ω | T < (p.1 : ℝ)} ∪
        ⋂ q : ℚ, {p : Set.Iic i × Ω | 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → (q : ℝ) < p.1 →
          thetaN X p.2 q ≤ L} := by
      ext p
      simp only [S, Set.mem_setOf_eq, Set.mem_union, Set.mem_iInter]
    rw [this]
    exact hT1.union (MeasurableSet.iInter hSq)
  have hfun : (fun p : Set.Iic i × Ω =>
      if (p.1 : ℝ) ≤ tauNL T L X p.2 ∨ T < (p.1 : ℝ) then (1 : ℝ) else 0) =
      S.indicator (fun _ => 1) := by
    funext p
    by_cases hT' : T < (p.1 : ℝ)
    · have hp : p ∈ S := Or.inl hT'
      simp [Set.indicator_of_mem hp, hT']
    · push Not at hT'
      have hiff := mrm_le_tau_iff X p.2 hL hT'
      by_cases hle : (p.1 : ℝ) ≤ tauNL T L X p.2
      · have hp : p ∈ S := Or.inr (hiff.1 hle)
        simp [Set.indicator_of_mem hp, hle]
      · have hp : p ∉ S := by
          rintro (h | h)
          · exact absurd h (not_lt.2 hT')
          · exact hle (hiff.2 h)
        simp [Set.indicator_of_notMem hp, hle, not_lt.2 hT']
  show Measurable[Subtype.instMeasurableSpace.prod (ℱ i)]
    (fun p : Set.Iic i × Ω => if (p.1 : ℝ) ≤ tauNL T L X p.2 ∨ T < (p.1 : ℝ) then (1 : ℝ) else 0)
  rw [hfun]
  exact measurable_const.indicator hSm

end ThetaProg

/-! ### Pathwise properties of `Θ_N` on the continuity event, and the stopping time -/

section Good

variable {Ω : Type*} {N : ℕ} {X : ℝ≥0 → Ω → EucConfig d N} {ζ : Ω}

theorem mrm_g_ge_one (x : EucConfig d N) : 1 ≤ 1 + secondMomentOf (HRS.Whole.empirical x) := by
  have := mrm_secondMoment_nonneg x
  linarith

theorem mrm_g_cont (hN : 0 < N) (hg : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    Continuous fun r : ℝ => 1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) := by
  have : (fun r : ℝ => 1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) =
      fun r => 1 + (N : ℝ)⁻¹ * ∑ i, ‖X (Real.toNNReal r) ζ i‖ ^ 2 :=
    funext fun r => by rw [mrm_secondMoment_empirical hN]
  rw [this]
  refine continuous_const.add (continuous_const.mul (continuous_finset_sum _ fun i _ => ?_))
  exact ((hg i).comp continuous_real_toNNReal).norm.pow 2

theorem mrm_theta_interval (u : ℝ) (hu : 0 ≤ u) : thetaN X ζ u = ∫ s in (0 : ℝ)..u,
    (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal s) ζ))) := by
  unfold thetaN
  rw [intervalIntegral.integral_of_le hu, integral_Icc_eq_integral_Ioc]

theorem mrm_theta_nonpos (u : ℝ) (hu : u ≤ 0) : thetaN X ζ u = 0 := by
  unfold thetaN
  exact setIntegral_Icc_of_nonpos _ hu

theorem mrm_theta_step (hN : 0 < N) (hg : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : thetaN X ζ a + (b - a) ≤ thetaN X ζ b := by
  have hc := mrm_g_cont hN hg
  rw [mrm_theta_interval a ha, mrm_theta_interval b (ha.trans hab),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 a)
      (hc.intervalIntegrable a b)]
  have h1 : ∫ s in a..b, (1 : ℝ) ≤ ∫ s in a..b,
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal s) ζ))) :=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const (hc.intervalIntegrable a b)
      fun s _ => mrm_g_ge_one _
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
  linarith

theorem mrm_theta_cont (hN : 0 < N) (hg : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    Continuous fun u : ℝ => thetaN X ζ u := by
  have hc := mrm_g_cont hN hg
  have e : (fun u : ℝ => thetaN X ζ u) = fun u => ∫ s in (0 : ℝ)..max u 0,
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal s) ζ))) := by
    funext u
    rcases le_total u 0 with hu | hu
    · rw [mrm_theta_nonpos u hu, max_eq_right hu, intervalIntegral.integral_same]
    · rw [mrm_theta_interval u hu, max_eq_left hu]
  rw [e]
  exact (intervalIntegral.continuous_primitive (fun a b => hc.intervalIntegrable a b) 0).comp
    (continuous_id.max continuous_const)

theorem mrm_lintegral_theta (hN : 0 < N) (hg : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    {u : ℝ} (hu : 0 ≤ u) :
    ∫⁻ r in Set.Icc (0 : ℝ) u, ENNReal.ofReal
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) =
      ENNReal.ofReal (thetaN X ζ u) := by
  unfold thetaN
  rw [ofReal_integral_eq_lintegral_ofReal]
  · exact (mrm_g_cont hN hg).continuousOn.integrableOn_Icc
  · exact Eventually.of_forall fun r => (zero_le_one.trans (mrm_g_ge_one _))

/-- On the continuity event, the localized time integral of `1 + m_N` is at most `L`. -/
theorem mrm_tau_bound (hN : 0 < N) (hg : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {T L : ℝ}
    (hT : 0 ≤ T) (hL : 0 < L) :
    ∫⁻ r in Set.Icc (0 : ℝ) T, (if r ≤ tauNL T L X ζ then ENNReal.ofReal
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) ≤
        ENNReal.ofReal L := by
  classical
  have hmono : ∀ u v : ℝ, 0 ≤ u → u ≤ v → thetaN X ζ u ≤ thetaN X ζ v := fun u v hu huv => by
    have := mrm_theta_step hN hg hu huv
    linarith
  by_cases h : ∃ u ∈ Set.Icc (0 : ℝ) T, L < thetaN X ζ u
  · set A : Set ℝ := {u | u ∈ Set.Icc (0 : ℝ) T ∧ L < thetaN X ζ u} with hA
    have hne : A.Nonempty := by
      obtain ⟨u, hu, hlt⟩ := h
      exact ⟨u, hu, hlt⟩
    have hbdd : BddBelow A := ⟨0, fun u hu => hu.1.1⟩
    have hc : tauNL T L X ζ = sInf A := by
      unfold tauNL
      rw [if_pos h]
    have hc0 : 0 ≤ sInf A := le_csInf hne fun u hu => hu.1.1
    have hcT : sInf A ≤ T := by
      obtain ⟨u, hu⟩ := hne
      exact (csInf_le hbdd hu).trans hu.1.2
    have hΘc : thetaN X ζ (sInf A) ≤ L := by
      by_contra hlt
      push Not at hlt
      obtain ⟨q, hq0, hqc, hΘq⟩ := mrm_theta_rat (g := fun s => 1 + secondMomentOf
        (HRS.Whole.empirical (X (Real.toNNReal s) ζ))) hL.le hc0 hlt
      have hqA : (q : ℝ) ∈ A := ⟨⟨hq0, (hqc.le.trans hcT)⟩, hΘq⟩
      exact absurd (csInf_le hbdd hqA) (not_le.2 hqc)
    rw [hc]
    have hind : ∀ r : ℝ, (if r ≤ sInf A then ENNReal.ofReal (1 + secondMomentOf
        (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0) =
        (Set.Iic (sInf A)).indicator (fun r => ENNReal.ofReal (1 + secondMomentOf
        (HRS.Whole.empirical (X (Real.toNNReal r) ζ)))) r := by
      intro r
      by_cases hr : r ≤ sInf A
      · simp [Set.indicator, hr]
      · simp [Set.indicator, hr]
    simp_rw [hind]
    rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Set.Iic (sInf A) ∩ Set.Icc (0 : ℝ) T = Set.Icc 0 (sInf A) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.trans hcT⟩
    rw [hset, mrm_lintegral_theta hN hg hc0]
    exact ENNReal.ofReal_le_ofReal hΘc
  · push Not at h
    have hc : tauNL T L X ζ = T := by
      unfold tauNL
      rw [if_neg (by push Not; exact h)]
    rw [hc]
    calc ∫⁻ r in Set.Icc (0 : ℝ) T, (if r ≤ T then ENNReal.ofReal (1 + secondMomentOf
          (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) else 0)
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (1 + secondMomentOf
          (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) := by
          refine lintegral_mono fun r => ?_
          split_ifs <;> simp
      _ = ENNReal.ofReal (thetaN X ζ T) := mrm_lintegral_theta hN hg hT
      _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal (h T ⟨hT, le_rfl⟩)

end Good

section Stop

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : ℕ} {ℱ : Filtration ℝ mΩ}

/-- A stopping time of `ℱ` that agrees (on a measurable event of full measure) with `τ_{N,L}`,
in the sense that `r ≤ τ ↔ r ≤ τ_{N,L}` for `r ∈ [0,T]`. -/
theorem mrm_exists_stopping (hℱ : IsCompleteFiltration P ℱ) (hN : 0 < N)
    {X : ℝ≥0 → Ω → EucConfig d N} (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {T L : ℝ} (hL : 0 < L) :
    ∃ (G : Set Ω) (τ'' : Ω → WithTop ℝ), MeasurableSet G ∧ P Gᶜ = 0 ∧ IsStoppingTime ℱ τ'' ∧
      ∀ ζ ∈ G, (∀ i, Continuous fun t : ℝ≥0 => X t ζ i) ∧ τ'' ζ ≤ (T : WithTop ℝ) ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ T → ((r : WithTop ℝ) ≤ τ'' ζ ↔ r ≤ tauNL T L X ζ) := by
  classical
  have hae : P {ζ | ¬ ∀ i, Continuous fun t : ℝ≥0 => X t ζ i} = 0 := ae_iff.1 hcont
  obtain ⟨Nl, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hae
  have hGm : ∀ t, MeasurableSet[ℱ t] Nlᶜ := fun t => (hℱ t Nl hNm hN0).compl
  have hGgood : ∀ ζ ∈ Nlᶜ, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i := fun ζ hζ => by
    by_contra h
    exact hζ (hsub h)
  let Θh : ℝ → Ω → ℝ := fun u ζ => if ζ ∈ Nlᶜ then thetaN X ζ u else 0
  have hadapt : Adapted ℱ Θh := fun u =>
    Measurable.ite (hGm u) (mrm_theta_adapted hN hXp u) measurable_const
  have hcontΘ : ∀ ζ, Continuous fun u => Θh u ζ := fun ζ => by
    by_cases hζ : ζ ∈ Nlᶜ
    · simp only [Θh, if_pos hζ]
      exact mrm_theta_cont hN (hGgood ζ hζ)
    · simp only [Θh, if_neg hζ]
      exact continuous_const
  have hτ' := isStoppingTime_hittingAfter_Ici ℱ Θh hadapt hcontΘ L
  refine ⟨Nlᶜ, fun ζ => min (hittingAfter Θh (Set.Ici L) 0 ζ) (T : WithTop ℝ), ℱ.le 0 _ (hGm 0), ?_,
    hτ'.min_const T, ?_⟩
  · rw [compl_compl]
    exact hN0
  intro ζ hζ
  have hgood := hGgood ζ hζ
  have hΘ : ∀ u, Θh u ζ = thetaN X ζ u := fun u => by simp only [Θh, if_pos hζ]
  have hhit := fun t => hittingAfter_le_iff_of_isClosed Θh ζ (hcontΘ ζ) (isClosed_Ici (a := L)) 0 t
  have key : ∀ r : ℝ, ((r : WithTop ℝ) ≤ hittingAfter Θh (Set.Ici L) 0 ζ ↔
      ∀ u : ℝ, 0 ≤ u → u < r → thetaN X ζ u < L) := by
    intro r
    constructor
    · intro hr u hu0 hur
      by_contra hge
      push Not at hge
      have h1 : hittingAfter Θh (Set.Ici L) 0 ζ ≤ (u : WithTop ℝ) :=
        (hhit u).2 ⟨u, hu0, le_rfl, by rw [hΘ]; exact hge⟩
      have h2 : (r : WithTop ℝ) ≤ (u : WithTop ℝ) := hr.trans h1
      exact absurd (WithTop.coe_le_coe.1 h2) (not_le.2 hur)
    · intro h
      by_contra hlt
      push Not at hlt
      obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hcr : c < r := by
        rw [← hc] at hlt
        exact WithTop.coe_lt_coe.1 hlt
      obtain ⟨r', h0, hrc, hmem⟩ := (hhit c).1 (le_of_eq hc.symm)
      have := h r' h0 (lt_of_le_of_lt hrc hcr)
      rw [hΘ] at hmem
      exact absurd hmem (not_le.2 this)
  refine ⟨hgood, min_le_right _ _, fun r hr0 hrT => ?_⟩
  have hrT' : (r : WithTop ℝ) ≤ (T : WithTop ℝ) := WithTop.coe_le_coe.2 hrT
  rw [le_min_iff, key r, mrm_le_tau_iff X ζ hL hrT]
  simp only [hrT', and_true]
  constructor
  · intro h q hq0 hqT hqr
    exact (h q hq0 hqr).le
  · intro h u hu0 hur
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hur
    have hq0 : 0 ≤ (q : ℝ) := hu0.trans hq1.le
    have h1 := mrm_theta_step hN hgood hu0 hq1.le
    have h2 := h q hq0 (hq2.le.trans hrT) hq2
    linarith

end Stop

/-! ### The probability that the localization is active -/

section Prob

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {N : ℕ}

theorem mrm_prob_bound (hN : 0 < N) {X : ℝ≥0 → Ω → EucConfig d N}
    (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {T L : ℝ} (hT : 0 ≤ T)
    (hL : 0 < L) {m₂ : ℝ}
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal
      (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal t) ζ))) ∂P ≤ ENNReal.ofReal m₂) :
    P {ζ | tauNL T L X ζ < T} ≤ ENNReal.ofReal (T * (1 + max m₂ 0) / L) := by
  classical
  set m₂' : ℝ := max m₂ 0 with hm₂'
  have hm₂'0 : 0 ≤ m₂' := le_max_right _ _
  -- the event is contained in `{L < Θ_N(T)}` up to a null set
  have hsub : {ζ | tauNL T L X ζ < T} ⊆
      {ζ | ENNReal.ofReal L ≤ ENNReal.ofReal (thetaN X ζ T)} ∪
        {ζ | ¬ ∀ i, Continuous fun t : ℝ≥0 => X t ζ i} := by
    intro ζ hζ
    by_cases hg : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i
    · left
      by_contra hno
      simp only [Set.mem_setOf_eq, not_le] at hno
      have hΘ : thetaN X ζ T ≤ L := by
        have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by
          have h0 : 0 ≤ thetaN X ζ T := by
            rw [mrm_theta_interval T hT]
            refine intervalIntegral.integral_nonneg hT fun s _ => ?_
            exact zero_le_one.trans (mrm_g_ge_one _)
          exact h0)).1 hno
        exact this.le
      have hne : ¬ ∃ u ∈ Set.Icc (0 : ℝ) T, L < thetaN X ζ u := by
        rintro ⟨u, hu, hlt⟩
        have h1 := mrm_theta_step hN hg hu.1 hu.2
        have h2 := hu.2
        linarith
      have heq : tauNL T L X ζ = T := by
        unfold tauNL
        rw [if_neg hne]
      have h2 : tauNL T L X ζ < T := hζ
      rw [heq] at h2
      exact lt_irrefl _ h2
    · right
      exact hg
  have hnull : P {ζ | ¬ ∀ i, Continuous fun t : ℝ≥0 => X t ζ i} = 0 := ae_iff.1 hcont
  have hθmeas : Measurable fun ζ => thetaN X ζ T :=
    (mrm_theta_adapted hN hXp T).mono (ℱ.le T) le_rfl
  -- Markov
  have hmarkov : P {ζ | ENNReal.ofReal L ≤ ENNReal.ofReal (thetaN X ζ T)} ≤
      (∫⁻ ζ, ENNReal.ofReal (thetaN X ζ T) ∂P) / ENNReal.ofReal L :=
    meas_ge_le_lintegral_div hθmeas.ennreal_ofReal.aemeasurable
      (ENNReal.ofReal_pos.2 hL).ne' ENNReal.ofReal_ne_top
  -- the first moment of `Θ_N(T)`
  have hF := mrm_gF_progressive hN hXp
  have hFm := isProgressive_measurable_uncurry_min hF T
  have hmeasG : Measurable fun p : ℝ × Ω => ENNReal.ofReal
      (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal (min p.1 T)) p.2))) :=
    hFm.ennreal_ofReal
  have hmoment : ∫⁻ ζ, ENNReal.ofReal (thetaN X ζ T) ∂P ≤ ENNReal.ofReal (T * (1 + m₂')) := by
    have h1 : ∫⁻ ζ, ENNReal.ofReal (thetaN X ζ T) ∂P =
        ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal
          (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal (min r T)) ζ)))) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hcont] with ζ hg
      rw [← mrm_lintegral_theta hN hg hT]
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [min_eq_left hr.2]
    have hswap := lintegral_lintegral_swap (μ := P)
      (ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) T))
      (f := fun ζ r => ENNReal.ofReal (1 + secondMomentOf
        (HRS.Whole.empirical (X (Real.toNNReal (min r T)) ζ))))
      (hmeasG.comp measurable_swap).aemeasurable
    rw [h1, hswap]
    have h2 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal
        (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal (min r T)) ζ))) ∂P ≤
          ENNReal.ofReal (1 + m₂') := by
      intro r hr
      simp only [min_eq_left hr.2]
      calc ∫⁻ ζ, ENNReal.ofReal (1 + secondMomentOf (HRS.Whole.empirical
              (X (Real.toNNReal r) ζ))) ∂P
          ≤ ∫⁻ ζ, (1 + ENNReal.ofReal (secondMomentOf (HRS.Whole.empirical
              (X (Real.toNNReal r) ζ)))) ∂P := by
            refine lintegral_mono fun ζ => ?_
            calc ENNReal.ofReal (1 + secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ)))
                ≤ ENNReal.ofReal 1 + ENNReal.ofReal (secondMomentOf (HRS.Whole.empirical
                  (X (Real.toNNReal r) ζ))) := ENNReal.ofReal_add_le
              _ = _ := by rw [ENNReal.ofReal_one]
        _ = 1 + ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (HRS.Whole.empirical
              (X (Real.toNNReal r) ζ))) ∂P := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ 1 + ENNReal.ofReal m₂' := by
            gcongr
            exact (hm r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        _ = ENNReal.ofReal (1 + m₂') := by
            rw [ENNReal.ofReal_add zero_le_one hm₂'0, ENNReal.ofReal_one]
    calc ∫⁻ r in Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (1 + secondMomentOf
          (HRS.Whole.empirical (X (Real.toNNReal (min r T)) ζ))) ∂P
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (1 + m₂') :=
          setLIntegral_mono' measurableSet_Icc h2
      _ = ENNReal.ofReal (T * (1 + m₂')) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  calc P {ζ | tauNL T L X ζ < T}
      ≤ P ({ζ | ENNReal.ofReal L ≤ ENNReal.ofReal (thetaN X ζ T)} ∪
        {ζ | ¬ ∀ i, Continuous fun t : ℝ≥0 => X t ζ i}) := measure_mono hsub
    _ ≤ P {ζ | ENNReal.ofReal L ≤ ENNReal.ofReal (thetaN X ζ T)} +
        P {ζ | ¬ ∀ i, Continuous fun t : ℝ≥0 => X t ζ i} := measure_union_le _ _
    _ ≤ (∫⁻ ζ, ENNReal.ofReal (thetaN X ζ T) ∂P) / ENNReal.ofReal L + 0 := by
        rw [hnull]
        exact add_le_add hmarkov le_rfl
    _ ≤ ENNReal.ofReal (T * (1 + m₂')) / ENNReal.ofReal L := by
        rw [add_zero]
        gcongr
    _ = ENNReal.ofReal (T * (1 + m₂') / L) := (ENNReal.ofReal_div_of_pos hL).symm

end Prob

/-! ### Locality: the localized convolution agrees with the full one on `{τ_{N,L} = T}` -/

section Local

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {N : ℕ} {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem mrm_tau_const_progressive (T : ℝ) :
    IsProgressive ℱ (fun r (ζ : Ω) => if r ≤ (fun _ : Ω => T) ζ ∨ T < r then (1 : ℝ) else 0) := by
  have : (fun r (ζ : Ω) => if r ≤ (fun _ : Ω => T) ζ ∨ T < r then (1 : ℝ) else 0) =
      fun _ _ => 1 := by
    funext r ζ
    exact if_pos (le_or_gt r T)
  rw [this]
  exact isProgressive_const ℱ 1

theorem mrm_local (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ)
    (hN : 0 < N) {X : ℝ≥0 → Ω → EucConfig d N} (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {L : ℝ} (hL : 0 < L)
    {M ML : ℝ → Ω → HNeg d (q : ℝ)}
    (hM : IsStochConvW P ℱ W' Cf cN q T X (fun _ => T) M)
    (hML : IsStochConvW P ℱ W' Cf cN q T X (tauNL T L X) ML) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ζ ∂P, tauNL T L X ζ = T → ML t ζ = M t ζ := by
  obtain ⟨G, τ'', hGm, hG0, hτ'', hG⟩ := mrm_exists_stopping hW.complete hN hXp hcont (T := T) hL
  have hGae : ∀ᵐ ζ ∂P, ζ ∈ G := ae_iff.2 hG0
  have hτT := mrm_tau_const_progressive (ℱ := ℱ) (Ω := Ω) T
  have hτL := mrm_tau_progressive (T := T) (L := L) hN hXp hL
  have hae : ∀ ℓ, ∀ᵐ ζ ∂P, (tauNL T L X ζ = T) → HNeg.pairing (mrm_e d (q : ℝ) ℓ) (ML t ζ) =
      HNeg.pairing (mrm_e d (q : ℝ) ℓ) (M t ζ) := by
    intro ℓ
    have hφ := mrm_e_test (d := d) (q : ℝ) ℓ
    set φ := mrm_e d (q : ℝ) ℓ with hφdef
    have hΦT := mrm_phi_L2 (P := P) hK cN ht.2 (fun _ => T) X hXp hτT hφ
    have hΦL := mrm_phi_L2 (P := P) hK cN ht.2 (tauNL T L X) X hXp hτL hφ
    have hΦS := hΦT.stopIntegrand hτ''
    have hcongr : ∀ᵐ ζ ∂P, ∀ s, itoIntegral P ℱ W' (stopIntegrand (mrmPhi Cf cN t (fun _ => T) X φ) τ'') s ζ =
        itoIntegral P ℱ W' (mrmPhi Cf cN t (tauNL T L X) X φ) s ζ := by
      refine itoIntegral_congr hW hΦS hΦL fun T' => ?_
      unfold sqIntegralOn
      have h0 : ∀ᵐ ζ ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T', ∑ k, ‖stopIntegrand
          (mrmPhi Cf cN t (fun _ => T) X φ) τ'' s ζ k - mrmPhi Cf cN t (tauNL T L X) X φ s ζ k‖ₑ ^ 2
            = 0 := by
        filter_upwards [hGae] with ζ hζ
        have : ∀ s, ∀ k, stopIntegrand (mrmPhi Cf cN t (fun _ => T) X φ) τ'' s ζ k -
            mrmPhi Cf cN t (tauNL T L X) X φ s ζ k = 0 := by
          intro s k
          obtain ⟨-, -, hiff⟩ := hG ζ hζ
          unfold stopIntegrand mrmPhi
          by_cases hs : s ∈ Set.Icc (0 : ℝ) t
          · have hsT : s ≤ T := hs.2.trans ht.2
            have h1 := hiff s hs.1 hsT
            by_cases hle : s ≤ tauNL T L X ζ
            · have h2 : (s : WithTop ℝ) ≤ τ'' ζ := h1.2 hle
              have h3 : ζ ∈ {ω | (s : WithTop ℝ) ≤ τ'' ω} := h2
              simp only [Set.indicator_of_mem h3, if_pos (And.intro hs hsT),
                if_pos (And.intro hs hle), sub_self]
            · have h2 : ¬ (s : WithTop ℝ) ≤ τ'' ζ := fun h => hle (h1.1 h)
              have h3 : ζ ∉ {ω | (s : WithTop ℝ) ≤ τ'' ω} := h2
              simp only [Set.indicator_of_notMem h3, Pi.zero_apply, if_neg (fun h : s ∈ Set.Icc (0 : ℝ) t ∧ s ≤ tauNL T L X ζ => hle h.2),
                sub_self]
          · simp only [if_neg (fun h : s ∈ Set.Icc (0 : ℝ) t ∧ s ≤ tauNL T L X ζ => hs h.1), sub_zero]
            by_cases h3 : ζ ∈ {ω | (s : WithTop ℝ) ≤ τ'' ω}
            · simp [Set.indicator_of_mem h3, hs]
            · simp [Set.indicator_of_notMem h3]
        simp [this]
      exact (lintegral_congr_ae h0).trans lintegral_zero
    have hMLp : ∀ᵐ ζ ∂P, HNeg.pairing φ (ML t ζ) =
        itoIntegral P ℱ W' (mrmPhi Cf cN t (tauNL T L X) X φ) t ζ := hML.2 t ht φ hφ
    have hMp : ∀ᵐ ζ ∂P, HNeg.pairing φ (M t ζ) =
        itoIntegral P ℱ W' (mrmPhi Cf cN t (fun _ => T) X φ) t ζ := hM.2 t ht φ hφ
    filter_upwards [hGae, hcongr, itoIntegral_stopIntegrand hW hΦT hτ'', hMLp, hMp]
      with ζ hζ hc hs hML' hM' hτ
    obtain ⟨-, hτle, hiff⟩ := hG ζ hζ
    have hτeq : τ'' ζ = (T : WithTop ℝ) := by
      refine le_antisymm hτle ?_
      exact (hiff T (ht.1.trans ht.2) le_rfl).2 hτ.ge
    rw [hML', hM', ← hc t, hs t, stoppedProcess_apply_coe (M := itoIntegral P ℱ W'
      (mrmPhi Cf cN t (fun _ => T) X φ)) (σ := τ'') (ω := ζ) (c := T) hτeq t, min_eq_left ht.2]
  filter_upwards [mrm_ae_eq_of_pairings (fun ζ => tauNL T L X ζ = T) hae] with ζ hζ
  exact hζ

end Local

/-! ### Part VI: assembly with the Kolmogorov-Chentsov construction -/

section KC

open HRS.MP.KC

/-- The Kolmogorov-Chentsov constants for `p = 4`, `β = 1`. -/
def mrmR : ℝ := (mkc_consts (β := (1 : ℝ)) (p := (4 : ℝ)) one_pos (by norm_num)).choose

def mrmQ : ℝ := (mkc_consts (β := (1 : ℝ)) (p := (4 : ℝ)) one_pos (by norm_num)).choose_spec.choose

theorem mrmRQ_spec : 0 < mrmR ∧ mrmR < 1 ∧ 0 < mrmQ ∧ mrmQ < 1 ∧
    1 ≤ mrmQ * 2 ^ (1 : ℝ) * mrmR ^ (4 : ℝ) :=
  (mkc_consts (β := (1 : ℝ)) (p := (4 : ℝ)) one_pos (by norm_num)).choose_spec.choose_spec

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {Ω : Type*}

/-- `mkc_Zc` depends only on the dyadic skeleton. -/
theorem mrm_mkc_congr (X Y : ℝ → Ω → E) {T : ℝ} (hT : 0 < T) (r : ℝ) (ζ : Ω)
    (h : ∀ n k : ℕ, k ≤ 2 ^ n → X (mkc_pt T n k) ζ = Y (mkc_pt T n k) ζ) (t : ℝ) :
    mkc_Zc X T r t ζ = mkc_Zc Y T r t ζ := by
  have hG : ζ ∈ mkc_Gs X T r ↔ ζ ∈ mkc_Gs Y T r := by
    simp only [mkc_Gs, mkc_G, mkc_Inc, mkc_xs, Set.mem_iUnion, Set.mem_setOf_eq]
    refine exists_congr fun m => forall_congr' fun n => forall_congr' fun k => ?_
    refine forall_congr' fun hk => ?_
    rw [h n (k + 1) (by omega), h n k (by omega)]
  unfold mkc_Zc
  by_cases hX : ζ ∈ mkc_Gs X T r
  · rw [if_pos hX, if_pos (hG.1 hX)]
    congr 1
    funext n
    exact h n _ (mkc_idx_le hT (max_le hT.le (min_le_right _ _)) n)
  · rw [if_neg hX, if_neg (fun h' => hX (hG.2 h'))]

variable [MeasurableSpace Ω]

theorem mrm_kc_compare_ae (P : Measure Ω) (X Y : ℝ → Ω → E) {T : ℝ} (hT : 0 < T) (r : ℝ)
    (B : Set Ω)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, ζ ∉ B → X t ζ = Y t ζ) :
    ∀ᵐ ζ ∂P, ζ ∉ B → ∀ t, mkc_Zc X T r t ζ = mkc_Zc Y T r t ζ := by
  have h1 : ∀ᵐ ζ ∂P, ∀ n k : ℕ, k ≤ 2 ^ n → ζ ∉ B → X (mkc_pt T n k) ζ = Y (mkc_pt T n k) ζ := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
    by_cases hk : k ≤ 2 ^ n
    · filter_upwards [h _ (mkc_pt_mem hT n k hk)] with ζ hζ _ hB
      exact hζ hB
    · exact Eventually.of_forall fun ζ hk' => absurd hk' hk
  filter_upwards [h1] with ζ hζ hB t
  exact mrm_mkc_congr X Y hT r ζ (fun n k hk => hζ n k hk hB) t

theorem mrm_kc_compare (P : Measure Ω) (X Y : ℝ → Ω → E) {T : ℝ} (hT : 0 < T) (r : ℝ)
    (B : Set Ω)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, ζ ∉ B → X t ζ = Y t ζ) :
    P {ζ | ∃ t ∈ Set.Icc (0 : ℝ) T, mkc_Zc Y T r t ζ ≠ mkc_Zc X T r t ζ} ≤ P B := by
  refine measure_mono_ae ?_
  filter_upwards [mrm_kc_compare_ae P X Y hT r B h] with ζ hζ hS
  by_contra hB
  obtain ⟨t, -, ht⟩ := hS
  exact ht (hζ hB t).symm

theorem mrm_omegaE_congr {F : Type*} [NormedAddCommGroup F] (z z' : ℝ → F) (T δ : ℝ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, z t = z' t) : omegaE z T δ = omegaE z' T δ := by
  unfold omegaE
  refine iSup_congr fun s => iSup_congr fun hs => iSup_congr fun t => iSup_congr fun ht => ?_
  rw [h s hs, h t ht]

/-- A uniform fourth-moment bound gives a modulus in probability for the Kolmogorov versions. -/
theorem mrm_kc_mod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z : ∀ N, ℝ → Ω N → E)
    (hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t)) (C : ℝ)
    (hmom : ∀ N : ℕ, 1 ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Z N t ζ - Z N s ζ‖ₑ ^ (4 : ℝ) ∂(P N) ≤
        ENNReal.ofReal (C * |t - s| ^ ((1 : ℝ) + 1)))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N),
        P N {ζ | ENNReal.ofReal ε < omegaE (fun t => mkc_Zc (Z N) T mrmR t ζ) T δ})
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hr0, hr1, hq0, hq1, hqr⟩ := mrmRQ_spec
  have hp : (0 : ℝ) < 4 := by norm_num
  refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
  obtain ⟨η', hη'pos, hη'le⟩ : ∃ η' : ℝ, 0 < η' ∧ ENNReal.ofReal η' ≤ η := by
    by_cases ht : η = ⊤
    · exact ⟨1, one_pos, by simp [ht]⟩
    · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' ht, by rw [ENNReal.ofReal_toReal ht]⟩
  have hη'pos' : (0 : ℝ≥0∞) < ENNReal.ofReal η' := ENNReal.ofReal_pos.2 hη'pos
  obtain ⟨lam, hlamb, hlam⟩ :=
    (((mkc_tail_tendsto hp (max C 0 * T ^ ((1 : ℝ) + 1)) mrmQ).eventually
      (gt_mem_nhds hη'pos')).and (eventually_gt_atTop (0 : ℝ))).exists
  obtain ⟨m, hm⟩ := mkc_small (c := mkc_c mrmR) (lam := lam) mrmR hr0.le hr1 hε
  have hpos : (0 : ℝ) < T / 2 ^ m := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
  refine iSup₂_le fun N hN => ?_
  refine le_trans ?_ hη'le
  refine le_trans (mkc_omega_prob (Z N) T mrmR (P N) (hZmeas N hN) hT hp (hmom N hN) hr0 hr1 hq0
    hq1 hqr hlam m hm.le hδ.2.le) hlamb.le

/-- Continuous versions for the unlocalized family, from localized families: `Z N` agrees with the
localized family `ZL L N` off an event `B L N` of probability `≤ C / L`, and the localized families
satisfy a fourth-moment bound. -/
theorem mrm_kc_main {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z : ∀ N, ℝ → Ω N → E)
    (hZ : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t)) (C : ℝ) (CL : ℕ → ℝ)
    (ZL : ℕ → ∀ N, ℝ → Ω N → E)
    (hZL : ∀ L N : ℕ, 1 ≤ L → 1 ≤ N → ∀ t, Measurable (ZL L N t))
    (hmom : ∀ L N : ℕ, 1 ≤ L → 1 ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖ZL L N t ζ - ZL L N s ζ‖ₑ ^ (4 : ℝ) ∂(P N) ≤
        ENNReal.ofReal (CL L * |t - s| ^ ((1 : ℝ) + 1)))
    (B : ℕ → ∀ N, Set (Ω N))
    (hB : ∀ L N : ℕ, 1 ≤ L → 1 ≤ N → P N (B L N) ≤ ENNReal.ofReal (C / L))
    (hag : ∀ L N : ℕ, 1 ≤ L → 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ᵐ ζ ∂(P N), ζ ∉ B L N → ZL L N t ζ = Z N t ζ) :
    ContVersionTight T P Z (fun N => mkc_Zc (Z N) T mrmR) := by
  obtain ⟨hr0, hr1, hq0, hq1, hqr⟩ := mrmRQ_spec
  have hp : (0 : ℝ) < 4 := by norm_num
  have hβ : (0 : ℝ) < 1 := one_pos
  have hverL : ∀ L N : ℕ, 1 ≤ L → 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      mkc_Zc (ZL L N) T mrmR t =ᵐ[P N] ZL L N t := fun L N hL hN t ht =>
    mkc_Zc_ae_eq (ZL L N) T mrmR (P N) (hZL L N hL hN) hT hp hβ (hmom L N hL hN) hr0 hr1 hq0 hq1
      hqr ht
  have hkey : ∀ L N : ℕ, 1 ≤ L → 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ᵐ ζ ∂(P N), ζ ∉ B L N → mkc_Zc (Z N) T mrmR t ζ = Z N t ζ := by
    intro L N hL hN t ht
    filter_upwards [mrm_kc_compare_ae (P N) (ZL L N) (Z N) hT mrmR (B L N) (hag L N hL hN),
      hverL L N hL hN t ht, hag L N hL hN t ht] with ζ h1 h2 h3 hζ
    exact (h1 hζ t).symm.trans (h2.trans (h3 hζ))
  have hlim : Tendsto (fun L : ℕ => ENNReal.ofReal (C / L)) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat C
    simpa using ENNReal.tendsto_ofReal this
  have hver : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ᵐ ζ ∂(P N), mkc_Zc (Z N) T mrmR t ζ = Z N t ζ := by
    intro N hN t ht
    have hle : ∀ L : ℕ, 1 ≤ L →
        P N {ζ | mkc_Zc (Z N) T mrmR t ζ ≠ Z N t ζ} ≤ ENNReal.ofReal (C / L) := by
      intro L hL
      refine le_trans (measure_mono_ae ?_) (hB L N hL hN)
      filter_upwards [hkey L N hL hN t ht] with ζ h1 h2
      by_contra hBζ
      exact h2 (h1 hBζ)
    have h0 : P N {ζ | mkc_Zc (Z N) T mrmR t ζ ≠ Z N t ζ} = 0 :=
      le_antisymm (ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hle⟩)) zero_le
    exact ae_iff.2 h0
  have hZc : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (mkc_Zc (Z N) T mrmR t) :=
    fun N hN t => mkc_Zc_meas (Z N) T mrmR hT hr0.le hr1 (hZ N hN) t
  have hcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(P N),
      Continuous fun t : Set.Icc (0 : ℝ) T => mkc_Zc (Z N) T mrmR t ζ :=
    fun N _ => ae_of_all _ (mkc_continuous (Z N) T mrmR hT hr0.le hr1)
  have hpath : ∀ N : ℕ, 1 ≤ N →
      Measurable fun ζ => contPathOf T (fun t => mkc_Zc (Z N) T mrmR t ζ) := by
    intro N hN
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have : (fun ζ => contPathOf T (fun t => mkc_Zc (Z N) T mrmR t ζ) s) =
        fun ζ => mkc_Zc (Z N) T mrmR s ζ := by
      funext ζ; exact mkc_contPathOf_apply (Z N) hT hr0.le hr1 ζ s
    rw [this]
    exact hZc N hN s
  have hmod : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N),
        P N {ζ | ENNReal.ofReal ε < omegaE (fun t => mkc_Zc (Z N) T mrmR t ζ) T δ})
      (𝓝[>] 0) (𝓝 0) := by
    intro ε hε
    refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
    obtain ⟨L, hL1, hLle⟩ : ∃ L : ℕ, 1 ≤ L ∧ ENNReal.ofReal (C / L) ≤ η / 2 :=
      ((ENNReal.tendsto_nhds_zero.1 hlim (η / 2) (ENNReal.half_pos hη.ne')).and
        (eventually_ge_atTop 1)).exists.imp fun L h => ⟨h.2, h.1⟩
    have hmodL := mrm_kc_mod T hT P (fun N => ZL L N)
      (fun N hN t => hZL L N hL1 hN t) (CL L) (fun N hN => hmom L N hL1 hN) ε hε
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hmodL (η / 2) (ENNReal.half_pos hη.ne')]
      with δ hδ
    refine iSup₂_le fun N hN => ?_
    have h1 : P N {ζ | ENNReal.ofReal ε < omegaE (fun t => mkc_Zc (Z N) T mrmR t ζ) T δ} ≤
        P N {ζ | ENNReal.ofReal ε < omegaE (fun t => mkc_Zc (ZL L N) T mrmR t ζ) T δ} +
          P N {ζ | ∃ t ∈ Set.Icc (0 : ℝ) T, mkc_Zc (Z N) T mrmR t ζ ≠ mkc_Zc (ZL L N) T mrmR t ζ} := by
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro ζ hζ
      by_cases hex : ∃ t ∈ Set.Icc (0 : ℝ) T,
          mkc_Zc (Z N) T mrmR t ζ ≠ mkc_Zc (ZL L N) T mrmR t ζ
      · exact Or.inr hex
      · left
        push Not at hex
        have := mrm_omegaE_congr (fun t => mkc_Zc (ZL L N) T mrmR t ζ)
          (fun t => mkc_Zc (Z N) T mrmR t ζ) T δ (fun t ht => (hex t ht).symm)
        simp only [Set.mem_setOf_eq] at hζ ⊢
        rwa [this]
    have h2 : P N {ζ | ∃ t ∈ Set.Icc (0 : ℝ) T,
        mkc_Zc (Z N) T mrmR t ζ ≠ mkc_Zc (ZL L N) T mrmR t ζ} ≤ η / 2 :=
      ((mrm_kc_compare (P N) (ZL L N) (Z N) hT mrmR (B L N) (hag L N hL1 hN)).trans
        (hB L N hL1 hN)).trans hLle
    have h3 : P N {ζ | ENNReal.ofReal ε <
        omegaE (fun t => mkc_Zc (ZL L N) T mrmR t ζ) T δ} ≤ η / 2 :=
      (le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) => P N {ζ | ENNReal.ofReal ε <
        omegaE (fun t => mkc_Zc (ZL L N) T mrmR t ζ) T δ}) N hN).trans hδ
    calc _ ≤ _ := h1
      _ ≤ η / 2 + η / 2 := add_le_add h3 h2
      _ = η := ENNReal.add_halves η
  refine ⟨hver, hcont, hpath, hmod, fun htight => ?_⟩
  refine HRS.MP.PathTight.path_tightness_criterion_proof T hT P
    (fun N t ζ => mkc_Zc (Z N) T mrmR t ζ) hZc hcont hpath (Set.Icc (0 : ℝ) T) subset_rfl
    subset_closure ?_ hmod
  intro t ht
  have hset : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (fun ζ => mkc_Zc (Z N) T mrmR t ζ)} =
      {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)} := by
    ext μ
    constructor
    · rintro ⟨N, hN, rfl⟩
      exact ⟨N, hN, Measure.map_congr (hver N hN t ht)⟩
    · rintro ⟨N, hN, rfl⟩
      exact ⟨N, hN, (Measure.map_congr (hver N hN t ht)).symm⟩
  rw [hset]
  exact htight t ht

end KC

/-! ### Part VII: the constants and the final assembly -/

section Final

open HRS.MP.KC

theorem mrm_cN_sq (S : WholeMainData d) {N : ℕ} (hN : 0 < N) :
    (S.sigma N * Real.sqrt (2 * S.invβ N) / N) ^ 2 * N ≤ 2 := by
  have hinv := S.hinvβ N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases h0 : S.invβ N = 0
  · simp [h0]
  · have hpos : 0 < S.invβ N := lt_of_le_of_ne hinv (Ne.symm h0)
    have hσ : S.sigma N ≤ Real.sqrt (N / S.invβ N) := by
      unfold WholeMainData.sigma sigmaScale
      rw [if_neg h0]
      exact min_le_right _ _
    have hσ0 : 0 ≤ S.sigma N := by
      unfold WholeMainData.sigma sigmaScale
      rw [if_neg h0]
      exact le_min (S.hκ N).le (Real.sqrt_nonneg _)
    have hσ2 : S.sigma N ^ 2 ≤ N / S.invβ N := by
      calc S.sigma N ^ 2 ≤ (Real.sqrt (N / S.invβ N)) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
        _ = N / S.invβ N := Real.sq_sqrt (by positivity)
    calc (S.sigma N * Real.sqrt (2 * S.invβ N) / N) ^ 2 * N
        = S.sigma N ^ 2 * (2 * S.invβ N) / N := by
          rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
          field_simp
      _ ≤ (N / S.invβ N) * (2 * S.invβ N) / N := by gcongr
      _ = 2 := by field_simp

theorem mrm_flow_cont {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω} {D : WholeDyn d}
    {T : ℝ} {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (h : SelectedFlowRd P D T X₀ W X) :
    ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h1⟩ | ⟨-, -, -, -, h1⟩
  · exact h1.cont
  · exact h1.toContact.cont
  · exact h1.cont

theorem mrm_tau_le {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {T L : ℝ}
    (hT : 0 ≤ T) : tauNL T L X ζ ≤ T := by
  classical
  unfold tauNL
  by_cases h : ∃ u ∈ Set.Icc (0 : ℝ) T, L < thetaN X ζ u
  · rw [if_pos h]
    obtain ⟨u, hu, hlt⟩ := h
    exact (csInf_le ⟨0, fun v hv => hv.1.1⟩ (show u ∈ {u | u ∈ Set.Icc (0 : ℝ) T ∧ L <
      thetaN X ζ u} from ⟨hu, hlt⟩)).trans hu.2
  · rw [if_neg h]

theorem mrm_hmom_conv {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {μ : Measure Ω}
    (f : Ω → E) (K : ℝ) (s t : ℝ)
    (h : ∫⁻ ζ, ‖f ζ‖ₑ ^ 4 ∂μ ≤ ENNReal.ofReal (K * |t - s| ^ 2)) :
    ∫⁻ ζ, ‖f ζ‖ₑ ^ (4 : ℝ) ∂μ ≤ ENNReal.ofReal (K * |t - s| ^ ((1 : ℝ) + 1)) := by
  have e1 : ∀ x : ℝ≥0∞, x ^ (4 : ℝ) = x ^ (4 : ℕ) := fun x => by
    exact_mod_cast ENNReal.rpow_natCast x 4
  have e2 : |t - s| ^ ((1 : ℝ) + 1) = |t - s| ^ 2 := by
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e1, e2]
  exact h

section PerN

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {N : ℕ} {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- The fourth moment of the increments of a localized convolution (`τ = τ_{N,L}`). -/
theorem mrm_stopped_fourth (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern)
    (cN : ℝ) (hN : 0 < N) (hcN : cN ^ 2 * N ≤ 2) {X : ℝ≥0 → Ω → EucConfig d N}
    (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {L : ℝ} (hL : 1 ≤ L) (hT : 0 ≤ T)
    {M : ℝ → Ω → HNeg d (q : ℝ)} (hM : IsStochConvW P ℱ W' Cf cN q T X (tauNL T L X) M)
    {s' t : ℝ} (hs' : s' ∈ Set.Icc (0 : ℝ) T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ζ, ‖M t ζ - M s' ζ‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (mrmCb * (8 * (d : ℝ) ^ 2 * C₁ ^ 4) * (4 * L ^ 2 * T ^ 2 + 1) *
        |t - s'| ^ 2) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  refine mrm_fourth hW hK cN hN hcN (tauNL T L X) X hXp (mrm_tau_progressive hN hXp hL0) hL0.le
    ?_ hM hs' ht
  filter_upwards [hcont] with ζ hg
  exact mrm_tau_bound hN hg hT hL0

/-- Off `{τ_{N,L} < T}` the localized and the full convolution agree (a.s., for each `t`). -/
theorem mrm_agree (hW : IsBrownianFiltration P ℱ W') (hK : MrmKern Cf T q C₁ Kern) (cN : ℝ)
    (hN : 0 < N) {X : ℝ≥0 → Ω → EucConfig d N} (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) {L : ℝ} (hL : 0 < L)
    (hT : 0 ≤ T) {M ML : ℝ → Ω → HNeg d (q : ℝ)}
    (hM : IsStochConvW P ℱ W' Cf cN q T X (fun _ => T) M)
    (hML : IsStochConvW P ℱ W' Cf cN q T X (tauNL T L X) ML) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ζ ∂P, ζ ∉ {ζ | tauNL T L X ζ < T} → ML t ζ = M t ζ := by
  filter_upwards [mrm_local hW hK cN hN hXp hcont hL hM hML ht] with ζ h hζ
  refine h (le_antisymm (mrm_tau_le X ζ hT) ?_)
  exact not_lt.1 hζ

end PerN

/-- **S.A.24 on `ℝ^d`, parts (a) and (b), conditional on the kernel bound of S.A.22**
(`path_martingale_modulus_rd` of `HRS.Whole.AppendixALemmas`, without the limit clause (c), with
`PathAdjointInput` replaced by the kernel bound `hker` of constant `C₁`). -/
theorem path_martingale_modulus_rd_of_kernel (s : ℝ) (fd : FieldDensityRd d s)
    (MB Λ ΛV G₀ νbar T C₁ C₀ m20 Ē : ℝ) :
    ∃ (C : ℝ) (CL : ℝ → ℝ), ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ),
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 → (∀ N : ℕ, 1 ≤ N → 𝔈 N ≤ Ē) →
      (∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) T (fd.Gamma + 2) C₁) →
      ∀ (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      (∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X) →
      ∀ (Mq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
      (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
        (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (fd.Gamma + 2) T (R N).X (fun _ => T) (Mq N)) →
      (∃ Zc, ContVersionTight T (fun N => (R N).P) Mq Zc) ∧
      (∀ L : ℝ, 1 ≤ L → ∀ (MqL : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        (∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
          (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (fd.Gamma + 2) T (R N).X
          (tauNL T L (R N).X) (MqL N)) →
        (∃ (Zc ZcL : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
          (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (Mq N) (Zc N)) ∧
          (∀ N : ℕ, 1 ≤ N → HasContVersion T (R N).P (MqL N) (ZcL N)) ∧
          (⨆ N : ℕ, ⨆ (_ : 1 ≤ N),
            (R N).P {ζ | ∃ t ∈ Set.Icc (0 : ℝ) T, ZcL N t ζ ≠ Zc N t ζ}) ≤ ENNReal.ofReal (C / L)) ∧
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖MqL N t ζ - MqL N s' ζ‖ₑ ^ 4 ∂(R N).P ≤ ENNReal.ofReal (CL L * |t - s'| ^ 2))) := by
  classical
  obtain ⟨Cm, hCm⟩ := moments_lemma (d := d) s MB Λ ΛV G₀ νbar T Ē (fd.Gamma + 5) (fd.Gamma + 5)
    (by omega)
  set CLfun : ℝ → ℝ := fun L => mrmCb * (8 * (d : ℝ) ^ 2 * |C₁| ^ 4) * (4 * L ^ 2 * T ^ 2 + 1)
    with hCLfun
  refine ⟨T * (1 + max (Cm * (1 + m20)) 0), CLfun, ?_⟩
  intro S hs hT hinv R 𝔈 hstd hĒ hker ℱ W' hfilt Mq hMq
  have hT0 : 0 < T := hT ▸ S.hT
  have hmom := hCm S hs hT hinv R 𝔈 C₀ m20 hstd hĒ
  -- the kernel families
  have hKex : ∀ N : ℕ, ∃ Kern : Fin d → ℝ → ℝ → Euc d → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ),
      1 ≤ N → MrmKern (S.coeff N) T (fd.Gamma + 2) |C₁| Kern := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨K, hK⟩ := mrmKern_exists (S.coeff N) T (fd.Gamma + 2) C₁ (hker N hN)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨fun _ _ _ _ => 0, fun h => absurd h hN⟩
  choose Kern hKern using hKex
  -- second moment bound
  have hm2 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal
      (secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ))) ∂(R N).P ≤
        ENNReal.ofReal (Cm * (1 + m20)) := by
    intro N hN t ht
    refine le_trans (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal ?_)
      (hmom N hN t (by rw [hT]; exact ht))
    have := HRS.Whole.Q09A.secondMomentOf_nonneg (d := d) (HRS.Whole.withDensityReal (S.ρ N t))
    linarith
  have hcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(R N).P, ∀ i, Continuous fun t : ℝ≥0 => (R N).X t ζ i :=
    fun N hN => mrm_flow_cont (hstd.flow N hN)
  -- localized families
  have hex : ∀ (L N : ℕ), ∃ M : ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ), 1 ≤ L → 1 ≤ N →
      IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N) (S.sigma N * Real.sqrt (2 * S.invβ N) / N)
        (fd.Gamma + 2) T (R N).X (tauNL T (L : ℝ) (R N).X) M := by
    intro L N
    by_cases h : 1 ≤ L ∧ 1 ≤ N
    · have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast h.1
      obtain ⟨M, hM⟩ := mrm_exists_stochConv (hfilt N h.2).brownian (hKern N h.2) _
        (tauNL T (L : ℝ) (R N).X) (R N).X (hfilt N h.2).progressive
        (mrm_tau_progressive (by omega) (hfilt N h.2).progressive hLpos)
      exact ⟨M, fun _ _ => hM⟩
    · exact ⟨fun _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ZL hZL using hex
  have hA : ContVersionTight T (fun N => (R N).P) Mq (fun N => mkc_Zc (Mq N) T mrmR) := by
    refine mrm_kc_main T hT0 (fun N => (R N).P) Mq (fun N hN t => (hMq N hN).1 t)
      (T * (1 + max (Cm * (1 + m20)) 0)) (fun L => CLfun (L : ℝ)) ZL
      (fun L N hL hN t => (hZL L N hL hN).1 t) ?_
      (fun L N => {ζ | tauNL T (L : ℝ) (R N).X ζ < T}) ?_ ?_
    · intro L N hL hN s' hs' t ht
      have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      exact mrm_hmom_conv (fun ζ => ZL L N t ζ - ZL L N s' ζ) _ s' t
        (mrm_stopped_fourth (hfilt N hN).brownian (hKern N hN) _ (by omega)
          (mrm_cN_sq S (by omega)) (hfilt N hN).progressive (hcont N hN) hL1 hT0.le
          (hZL L N hL hN) hs' ht)
    · intro L N hL hN
      have hL1 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      exact mrm_prob_bound (by omega) (hfilt N hN).progressive (hcont N hN) hT0.le hL1
        (hm2 N hN)
    · intro L N hL hN t ht
      have hL1 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      exact mrm_agree (hfilt N hN).brownian (hKern N hN) _ (by omega) (hfilt N hN).progressive
        (hcont N hN) hL1 hT0.le (hMq N hN) (hZL L N hL hN) ht
  refine ⟨⟨_, hA⟩, fun L hL MqL hMqL => ⟨⟨fun N => mkc_Zc (Mq N) T mrmR,
    fun N => mkc_Zc (MqL N) T mrmR, ?_, ?_, ?_⟩, ?_⟩⟩
  · intro N hN
    refine ⟨hA.1 N hN, ?_⟩
    filter_upwards [hA.2.1 N hN] with ζ h
    exact continuousOn_iff_continuous_domRestrict.2 h
  · intro N hN
    obtain ⟨hr0, hr1, hq0, hq1, hqr⟩ := mrmRQ_spec
    refine ⟨fun t ht => ?_, ?_⟩
    · refine mkc_Zc_ae_eq (MqL N) T mrmR (R N).P (fun t => (hMqL N hN).1 t) hT0
        (by norm_num) one_pos (C := CLfun L) ?_ hr0 hr1 hq0 hq1 hqr ht
      intro s' hs' t' ht'
      exact mrm_hmom_conv (fun ζ => MqL N t' ζ - MqL N s' ζ) _ s' t'
        (mrm_stopped_fourth (hfilt N hN).brownian (hKern N hN) _ (by omega)
          (mrm_cN_sq S (by omega)) (hfilt N hN).progressive (hcont N hN) hL hT0.le
          (hMqL N hN) hs' ht')
    · exact Eventually.of_forall fun ζ => continuousOn_iff_continuous_domRestrict.2
        (mkc_continuous (MqL N) T mrmR hT0 hr0.le hr1 ζ)
  · refine iSup₂_le fun N hN => ?_
    have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
    refine le_trans (mrm_kc_compare (R N).P (Mq N) (MqL N) hT0 mrmR
      {ζ | tauNL T L (R N).X ζ < T} (fun t ht => ?_)) ?_
    · filter_upwards [mrm_agree (hfilt N hN).brownian (hKern N hN) _ (by omega)
        (hfilt N hN).progressive (hcont N hN) hL0 hT0.le (hMq N hN) (hMqL N hN) ht] with ζ h hζ
      exact (h hζ).symm
    · exact mrm_prob_bound (by omega) (hfilt N hN).progressive (hcont N hN) hT0.le hL0 (hm2 N hN)
  · intro N hN s' hs' t ht
    exact mrm_stopped_fourth (hfilt N hN).brownian (hKern N hN) _ (by omega)
      (mrm_cN_sq S (by omega)) (hfilt N hN).progressive (hcont N hN) hL hT0.le (hMqL N hN) hs' ht

end Final

end HRS.MP.RdMart
