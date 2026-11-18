import HRS.MS.MainRdFieldAux1
import HRS.MP.RdMartingale
import HRS.MP.RdPropKernel

/-!
# S.A.6, packet P3: the kernel family at the index `Γ`, Riesz representatives of measures, the particle field

For one coefficient `Cf` with `AdjointInputOneD (Γ : ℝ) m_* Cf T Kad` (the `deriv` clause of `FieldAdjointInputRd` for one `N`):

* `sa6_kern_exists`: `Kern j r t x ∈ H^{-Γ}` with `⟨φ, Kern j r t x⟩ = ∂_j U^{r,t}φ(x)` and `‖Kern‖ ≤ max Kad 0`
  (as `rpk_kernel` at the index `Γ`, without the increment bound);
* `sa6_sob_bound`: `|φ(x)| ≤ Kad ‖φ‖_{H^Γ}` (the clause at `r = t`, order `0`, with `U^{t,t}φ = φ`);
* `sa6_riesz_meas`: the Riesz representative of `φ ↦ ∫ φ dμ` for a probability measure `μ`;
* `sa6_riesz_U`: the Riesz representative of `φ ↦ c (∫ U^{0,t}φ dμ₁ - ∫ U^{0,t}φ dμ₂)` (the initial term);
* `sa6_exists_field`: the particle field `σ(μ_N - μ)` as a measurable `H^{-Γ}`-valued random variable.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra

variable {d : ℕ}

lemma sa6_prop_terminal {Cf : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW Cf t φ f) : propagatorW Cf t t φ = φ := by
  unfold propagatorW
  rw [dif_pos h]
  exact h.choose_spec.terminal

lemma sa6_one_le_mStar : 1 ≤ mStar d := by unfold mStar; omega

lemma sa6_cd_mStar {f : Euc d → ℝ} (h : ContDiff ℝ (mStar d : ℕ) f) {k : ℕ} (hk : k ≤ mStar d) :
    ContDiff ℝ k f := h.of_le (by exact_mod_cast hk)

section Kern

variable {Cf : WholeCoeff d} {T Kad : ℝ} {Γ : ℕ}

/-- The kernel family: pairing identity and sup bound (no increment bound). -/
structure Sa6Kern (Cf : WholeCoeff d) (T : ℝ) (Γ : ℕ) (C₁ : ℝ)
    (Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)) : Prop where
  nonneg : 0 ≤ C₁
  pair : ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ (x : Euc d) (φ : Euc d → ℝ),
    IsSobolevTest (Γ : ℝ) φ → HNeg.pairing φ (Kern j r t x) = gradient (propagatorW Cf r t φ) x j
  zero : ∀ (j : Fin d) (r t : ℝ) (x : Euc d), ¬(0 ≤ r ∧ r ≤ t ∧ t ≤ T) → Kern j r t x = 0
  bdd : ∀ (j : Fin d) (r t : ℝ) (x : Euc d), ‖Kern j r t x‖ ≤ C₁

theorem sa6_kern_exists (hadj : AdjointInputOneD (Γ : ℝ) (mStar d) Cf T Kad) :
    ∃ Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ), Sa6Kern Cf T Γ (max Kad 0) Kern := by
  classical
  have hm1 := sa6_one_le_mStar (d := d)
  have hdiff : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
      Differentiable ℝ (propagatorW Cf r t φ) := fun r t hr hrt htT φ hφ =>
    ((hadj r t hr hrt htT φ hφ).2.1).differentiable (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hm1))
  have hlinP : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ φ' : Euc d → ℝ, ∀ c : ℝ,
      IsSobolevTest (Γ : ℝ) φ → IsSobolevTest (Γ : ℝ) φ' →
      propagatorW Cf r t (c • φ + φ') = c • propagatorW Cf r t φ + propagatorW Cf r t φ' := by
    intro r t hr hrt htT φ φ' c hφ hφ'
    have h := (hadj r t hr hrt htT φ' hφ').2.2.1 φ hφ c
    rw [add_comm (c • φ) φ', h, add_comm]
  have hbdP : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
      ∀ (j : Fin d) (x : Euc d), |gradient (propagatorW Cf r t φ) x j| ≤
        Kad * HRS.Whole.sobolevNorm (Γ : ℝ) φ := by
    intro r t hr hrt htT φ hφ j x
    rw [rpk_gradient_partial]
    exact (hadj r t hr hrt htT φ hφ).2.2.2 1 hm1 (fun _ => j) x
  have hex : ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ x : Euc d,
      ∃ k : HNeg d (Γ : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
        HNeg.pairing φ k = gradient (propagatorW Cf r t φ) x j := by
    intro j r t hr hrt htT x
    exact rpk_exists_rep (d := d) (Γ := (Γ : ℝ)) (fun φ => gradient (propagatorW Cf r t φ) x j)
      (max Kad 0)
      (fun φ φ' c hφ hφ' => by
        show gradient (propagatorW Cf r t (c • φ + φ')) x j = _
        rw [hlinP r t hr hrt htT φ φ' c hφ hφ']
        rw [rpk_gradient_comb (hdiff r t hr hrt htT φ hφ) (hdiff r t hr hrt htT φ' hφ')])
      (fun φ hφ => (hbdP r t hr hrt htT φ hφ j x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  let Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ) := fun j r t x =>
    if h : 0 ≤ r ∧ r ≤ t ∧ t ≤ T then (hex j r t h.1 h.2.1 h.2.2 x).choose else 0
  have hpair : ∀ (j : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ T → ∀ (x : Euc d) (φ : Euc d → ℝ),
      IsSobolevTest (Γ : ℝ) φ → HNeg.pairing φ (Kern j r t x) = gradient (propagatorW Cf r t φ) x j := by
    intro j r t hr hrt htT x φ hφ
    have h : 0 ≤ r ∧ r ≤ t ∧ t ≤ T := ⟨hr, hrt, htT⟩
    simp only [Kern, dif_pos h]
    exact (hex j r t hr hrt htT x).choose_spec φ hφ
  have hzero : ∀ (j : Fin d) (r t : ℝ) (x : Euc d), ¬(0 ≤ r ∧ r ≤ t ∧ t ≤ T) → Kern j r t x = 0 :=
    fun j r t x h => by simp only [Kern, dif_neg h]
  refine ⟨Kern, ⟨le_max_right _ _, hpair, hzero, fun j r t x => ?_⟩⟩
  by_cases h : 0 ≤ r ∧ r ≤ t ∧ t ≤ T
  · obtain ⟨hr, hrt, htT⟩ := h
    refine hneg_norm_le_of_pairing _ (max Kad 0) (le_max_right _ _) (fun φ hφ => ?_)
    rw [hpair j r t hr hrt htT x φ hφ]
    exact (hbdP r t hr hrt htT φ hφ j x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · rw [hzero j r t x h, norm_zero]
    exact le_max_right _ _

/-- Sobolev embedding from the adjoint input: `|φ(x)| ≤ Kad‖φ‖_{H^Γ}` (the clause at `r = t = 0`, order `0`). -/
theorem sa6_sob_bound (hT : 0 ≤ T) (hadj : AdjointInputOneD (Γ : ℝ) (mStar d) Cf T Kad)
    {φ : Euc d → ℝ} (hφ : IsSobolevTest (Γ : ℝ) φ) (x : Euc d) :
    |φ x| ≤ Kad * HRS.Whole.sobolevNorm (Γ : ℝ) φ := by
  obtain ⟨hex, -, -, hb⟩ := hadj 0 0 le_rfl le_rfl hT φ hφ
  have := hb 0 (Nat.zero_le _) (fun l => Fin.elim0 l) x
  have e : HRS.Whole.partialDeriv (fun l : Fin 0 => Fin.elim0 l) (propagatorW Cf 0 0 φ) x = φ x := by
    unfold partialDeriv
    rw [iteratedFDeriv_zero_apply, sa6_prop_terminal hex]
  rwa [e] at this

/-- The first derivative bound: `|∂_jU^{r,t}φ(x)| ≤ Kad‖φ‖`. -/
theorem sa6_grad_bound (hadj : AdjointInputOneD (Γ : ℝ) (mStar d) Cf T Kad)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) {φ : Euc d → ℝ}
    (hφ : IsSobolevTest (Γ : ℝ) φ) (x : Euc d) (j : Fin d) :
    |gradient (propagatorW Cf r t φ) x j| ≤ Kad * HRS.Whole.sobolevNorm (Γ : ℝ) φ := by
  rw [rpk_gradient_partial]
  exact (hadj r t hr hrt htT φ hφ).2.2.2 1 sa6_one_le_mStar (fun _ => j) x

/-- The zeroth derivative bound `|U^{r,t}φ(x)| ≤ Kad‖φ‖`. -/
theorem sa6_prop_bound (hadj : AdjointInputOneD (Γ : ℝ) (mStar d) Cf T Kad)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) {φ : Euc d → ℝ}
    (hφ : IsSobolevTest (Γ : ℝ) φ) (x : Euc d) :
    |propagatorW Cf r t φ x| ≤ Kad * HRS.Whole.sobolevNorm (Γ : ℝ) φ := by
  have := (hadj r t hr hrt htT φ hφ).2.2.2 0 (Nat.zero_le _) (fun l => Fin.elim0 l) x
  have e : HRS.Whole.partialDeriv (fun l : Fin 0 => Fin.elim0 l) (propagatorW Cf r t φ) x =
      propagatorW Cf r t φ x := by
    unfold partialDeriv
    rw [iteratedFDeriv_zero_apply]
  rwa [e] at this

/-! ### Copies of the integrand lemmas of `RdMartingale` for `Sa6Kern` -/

section Integrand

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {N : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}

theorem sa6_Z_pair (hK : Sa6Kern Cf T Γ C₁ Kern) (cN : ℝ) {t : ℝ} (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) {φ : Euc d → ℝ} (hφ : IsSobolevTest (Γ : ℝ) φ)
    (r : ℝ) (ζ : Ω) (ia : Fin N × Fin d) :
    HNeg.pairing φ (mrmZ Kern cN t τ X r ζ ia) = mrmPhi Cf cN t τ X φ r ζ ia := by
  unfold mrmZ mrmPhi
  by_cases h : r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ
  · simp only [if_pos h]
    rw [mrm_pairing_smul hφ, hK.pair _ r t h.1.1 h.1.2 htT _ φ hφ]
  · simp only [if_neg h]
    exact mrm_pairing_zero hφ

theorem sa6_Z_norm (hK : Sa6Kern Cf T Γ C₁ Kern) (cN : ℝ) {t : ℝ} (htT : t ≤ T) (τ : Ω → ℝ)
    (X : ℝ≥0 → Ω → EucConfig d N) (r : ℝ) (ζ : Ω) (ia : Fin N × Fin d) :
    ‖mrmZ Kern cN t τ X r ζ ia‖ ≤ |cN| * C₁ := by
  unfold mrmZ
  by_cases h : r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ τ ζ
  · simp only [if_pos h]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hK.bdd _ r t _) (abs_nonneg _)
  · simp only [if_neg h, norm_zero]
    exact mul_nonneg (abs_nonneg _) hK.nonneg

theorem sa6_Z_progressive {ℱ : Filtration ℝ mΩ} (hK : Sa6Kern Cf T Γ C₁ Kern) (cN : ℝ) {t : ℝ}
    (htT : t ≤ T) (τ : Ω → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hXp : IsProgressive ℱ (ofNNRealTime X))
    (hτ : IsProgressive ℱ (fun r ζ => if r ≤ τ ζ ∨ T < r then (1 : ℝ) else 0))
    (ia : Fin N × Fin d) :
    IsProgressive ℱ (fun r ζ => mrmZ Kern cN t τ X r ζ ia) := by
  intro i
  refine @mrm_measurable_of_pairings d (Γ : ℝ) (Set.Iic i × Ω)
    (Subtype.instMeasurableSpace.prod (ℱ i)) (fun p => mrmZ Kern cN t τ X p.1 p.2 ia) ?_
  intro φ hφ
  have h : (fun p : Set.Iic i × Ω => HNeg.pairing φ (mrmZ Kern cN t τ X p.1 p.2 ia)) =
      fun p => mrmPhi Cf cN t τ X φ p.1 p.2 ia := by
    funext p
    exact sa6_Z_pair hK cN htT τ X hφ _ _ ia
  rw [h]
  exact mrmPhi_progressive cN htT τ X hXp hτ φ ia i

end Integrand

end Kern

/-! ### Riesz representatives of measures and of the initial term -/

section Riesz

variable {Γ : ℕ}

theorem sa6_riesz_meas {K : ℝ}
    (hK : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ x, |φ x| ≤ K * HRS.Whole.sobolevNorm (Γ : ℝ) φ)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    ∃ k : HNeg d (Γ : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
      HNeg.pairing φ k = ∫ x, φ x ∂μ := by
  have hi : ∀ ψ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) ψ → Integrable ψ μ := fun ψ hψ =>
    Integrable.of_bound hψ.1.continuous.aestronglyMeasurable (K * HRS.Whole.sobolevNorm (Γ : ℝ) ψ)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hK ψ hψ x)
  refine rpk_exists_rep (fun φ => ∫ x, φ x ∂μ) K ?_ ?_
  · intro φ φ' c hφ hφ'
    show ∫ x, (c • φ + φ') x ∂μ = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add ((hi φ hφ).const_mul c) (hi φ' hφ'), integral_const_mul]
  · intro φ hφ
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := φ) (C := K * HRS.Whole.sobolevNorm (Γ : ℝ) φ)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hK φ hφ x)
    simpa [Real.norm_eq_abs] using this

variable {Cf : WholeCoeff d} {T Kad : ℝ}

theorem sa6_riesz_U (hT : 0 ≤ T) (hadj : AdjointInputOneD (Γ : ℝ) (mStar d) Cf T Kad)
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (μ₁ μ₂ : Measure (Euc d)) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (c : ℝ) :
    ∃ k : HNeg d (Γ : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
      HNeg.pairing φ k = c * ((∫ x, propagatorW Cf 0 t φ x ∂μ₁) - ∫ x, propagatorW Cf 0 t φ x ∂μ₂) := by
  have hi : ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (ψ : Euc d → ℝ),
      IsSobolevTest (Γ : ℝ) ψ → Integrable (propagatorW Cf 0 t ψ) μ := fun μ _ ψ hψ =>
    Integrable.of_bound
      (((hadj 0 t le_rfl ht htT ψ hψ).2.1).continuous.aestronglyMeasurable)
      (Kad * HRS.Whole.sobolevNorm (Γ : ℝ) ψ)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using sa6_prop_bound hadj le_rfl ht htT hψ x)
  have hlinP : ∀ φ φ' : Euc d → ℝ, ∀ c : ℝ, IsSobolevTest (Γ : ℝ) φ → IsSobolevTest (Γ : ℝ) φ' →
      propagatorW Cf 0 t (c • φ + φ') = c • propagatorW Cf 0 t φ + propagatorW Cf 0 t φ' := by
    intro φ φ' c hφ hφ'
    have h := (hadj 0 t le_rfl ht htT φ' hφ').2.2.1 φ hφ c
    rw [add_comm (c • φ) φ', h, add_comm]
  refine rpk_exists_rep (fun φ => c * ((∫ x, propagatorW Cf 0 t φ x ∂μ₁) -
    ∫ x, propagatorW Cf 0 t φ x ∂μ₂)) (|c| * (2 * |Kad|)) ?_ ?_
  · intro φ φ' c' hφ hφ'
    show c * ((∫ x, propagatorW Cf 0 t (c' • φ + φ') x ∂μ₁) -
      ∫ x, propagatorW Cf 0 t (c' • φ + φ') x ∂μ₂) = _
    rw [hlinP φ φ' c' hφ hφ']
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add ((hi μ₁ φ hφ).const_mul c') (hi μ₁ φ' hφ'),
      integral_add ((hi μ₂ φ hφ).const_mul c') (hi μ₂ φ' hφ'), integral_const_mul, integral_const_mul]
    ring
  · intro φ hφ
    have hb : ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ],
        |∫ x, propagatorW Cf 0 t φ x ∂μ| ≤ |Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) φ := fun μ _ => by
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := propagatorW Cf 0 t φ)
        (C := |Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) φ)
        (ae_of_all _ fun x => by
          simpa [Real.norm_eq_abs] using (sa6_prop_bound hadj le_rfl ht htT hφ x).trans
            (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)))
      simpa [Real.norm_eq_abs] using this
    rw [abs_mul]
    have h1 := abs_le.1 (hb μ₁)
    have h2 := abs_le.1 (hb μ₂)
    have hn := Real.sqrt_nonneg (HRS.PDE.ToolboxRd.sobolevNormSq (Γ : ℝ) φ)
    calc |c| * |(∫ x, propagatorW Cf 0 t φ x ∂μ₁) - ∫ x, propagatorW Cf 0 t φ x ∂μ₂|
        ≤ |c| * (2 * (|Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) φ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      _ = |c| * (2 * |Kad|) * HRS.Whole.sobolevNorm (Γ : ℝ) φ := by ring

end Riesz

end HRS.MS.MainRdField
