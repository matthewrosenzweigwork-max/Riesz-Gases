import HRS.MS.MainRdPathAux12

/-!
# S.A.9, packet P3g: the Itô isometry for the tails of the thermal stochastic convolution

`sa9_Mq_tail_eq`: for `t ∈ [0,T]`
`E ∑_{ℓ ≥ Lc} ⟨φ_ℓ, Mq_N^t⟩² = E ∫_0^t ∑_{i,j} c_N² ∑_{ℓ ≥ Lc} (∂_jU^{r,t}φ_ℓ (x_i^r))² dr`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField

variable {d : ℕ}

/-- The gradient component of the adjoint propagator, cut off to `r ∈ [0,t]`. -/
def sa9_Gr (Cf : WholeCoeff d) (t : ℝ) (j : Fin d) (φ : Euc d → ℝ) (p : ℝ × Euc d) : ℝ :=
  if p.1 ∈ Set.Icc (0 : ℝ) t then gradient (propagatorW Cf p.1 t φ) p.2 j else 0

theorem sa9_Gr_meas (Cf : WholeCoeff d) (t : ℝ) (j : Fin d) (φ : Euc d → ℝ) :
    Measurable (sa9_Gr Cf t j φ) := mrm_meas_grad Cf t φ j

/-- The tail function of the gradient components. -/
def sa9_Tm (h : ℕ → mhn_Hc d) (Cf : WholeCoeff d) (t : ℝ) (j : Fin d) (Lc : ℕ) (p : ℝ × Euc d) : ℝ≥0∞ :=
  ∑' l, ENNReal.ofReal ((sa9_Gr Cf t j (mhn_phi (h (l + Lc))) p) ^ 2)

theorem sa9_Tm_meas (h : ℕ → mhn_Hc d) (Cf : WholeCoeff d) (t : ℝ) (j : Fin d) (Lc : ℕ) :
    Measurable (sa9_Tm h Cf t j Lc) :=
  Measurable.ennreal_tsum fun l => ENNReal.measurable_ofReal.comp ((sa9_Gr_meas _ _ _ _).pow_const 2)

section Itô

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_Mq_tail_eq (B : Sa9Bundle S R Γ) (h : ℕ → mhn_Hc d) {N : ℕ} (hN : 1 ≤ N)
    {Kadj : ℝ} {m₀ : ℕ} (hadj : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (S.coeff N) S.T Kadj)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (Lc : ℕ) :
    ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Mq N t ζ)) ^ 2) ∂(R N).P =
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑ ia : Fin N × Fin d,
        ENNReal.ofReal ((S.sigma N * Real.sqrt (2 * S.invβ N) / N) ^ 2) *
          sa9_Tm h (S.coeff N) t ia.2 Lc (r, (R N).X (Real.toNNReal (mrrClamp S.T r)) ζ ia.1)) ∂(R N).P := by
  classical
  have hT : 0 ≤ S.T := S.hT.le
  set cN : ℝ := S.sigma N * Real.sqrt (2 * S.invβ N) / N with hcN
  have hF := B.hfilt N hN
  have hXm := mrr_prog_meas (B.ℱ N) (R N).X hF.progressive hT
  set φl : ℕ → Euc d → ℝ := fun l => mhn_phi (h (l + Lc)) with hφl
  have hφt : ∀ l, IsSobolevTest ((Γ + 2 : ℕ) : ℝ) (φl l) := fun l => mhn_isSobolevTest_phi _ _
  set Φ : ℕ → ℝ → (R N).Ω → Fin N × Fin d → ℝ := fun l =>
    mrmPhi (S.coeff N) cN t (fun _ => S.T) (R N).X (φl l) with hΦ
  have hΦL2 : ∀ l, IsProgressiveL2 (R N).P (B.ℱ N) (Φ l) := by
    intro l
    refine IsProgressiveL2.of_bounded (R N).P (isProgressive_pi fun ia =>
      mrmPhi_progressive cN ht.2 (fun _ => S.T) (R N).X hF.progressive (sa6_tau_prog (B.ℱ N) S.T) _ ia)
      (|cN| * (|Kadj| * HRS.Whole.sobolevNorm ((Γ + 2 : ℕ) : ℝ) (φl l))) fun r ζ ia => ?_
    simp only [hΦ, mrmPhi]
    split_ifs with hr
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [rpk_gradient_partial]
      exact ((hadj r t hr.1.1 hr.1.2 ht.2 _ (hφt l)).2.2.2 1 (by omega) (fun _ => ia.2) _).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
    · simp only [abs_zero]
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  -- the integrand of the isometry
  set Q : ℕ → ℝ × (R N).Ω → ℝ≥0∞ := fun l p => ∑ ia : Fin N × Fin d, ENNReal.ofReal (cN ^ 2) *
    ENNReal.ofReal ((sa9_Gr (S.coeff N) t ia.2 (φl l) (p.1, (R N).X (Real.toNNReal (mrrClamp S.T p.1)) p.2 ia.1)) ^ 2)
    with hQ
  have hQm : ∀ l, Measurable (Q l) := fun l => by
    refine Finset.measurable_sum _ fun ia _ => Measurable.const_mul ?_ _
    exact ENNReal.measurable_ofReal.comp (((sa9_Gr_meas _ _ _ _).comp (measurable_fst.prodMk
      ((measurable_pi_apply ia.1).comp hXm))).pow_const 2)
  have hmeas : ∀ l, Measurable fun ζ => ENNReal.ofReal ((HNeg.pairing (φl l) (B.Mq N t ζ)) ^ 2) := fun l =>
    ENNReal.measurable_ofReal.comp
      (((mhn_continuous_pairing (hφt l)).measurable.comp ((B.hMq N hN).1 t)).pow_const 2)
  -- one coordinate
  have hcoord : ∀ l, ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (φl l) (B.Mq N t ζ)) ^ 2) ∂(R N).P =
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, Q l (r, ζ)) ∂(R N).P := by
    intro l
    have h1 : ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (φl l) (B.Mq N t ζ)) ^ 2) ∂(R N).P =
        sqIntegralOn (R N).P (Φ l) t := by
      rw [← lintegral_itoIntegral_sq hF.brownian (hΦL2 l) t]
      refine lintegral_congr_ae (((B.hMq N hN).2 t ht _ (hφt l)).mono fun ζ hζ => ?_)
      beta_reduce
      rw [hζ, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      rfl
    rw [h1]
    unfold sqIntegralOn
    refine lintegral_congr fun ζ => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1, hr.2.trans ht.2⟩
    have key : ∀ a b : ℝ, ‖a * b‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (b ^ 2) := fun a b => by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, mul_pow,
        ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [hQ, hΦ, mrmPhi, sa9_Gr, if_pos hr, mrrClamp_of_mem hrT]
    refine Finset.sum_congr rfl fun ia _ => ?_
    rw [if_pos ⟨hr, hrT.2⟩, key]
  have hinner : ∀ l ζ, Measurable fun r => Q l (r, ζ) := fun l ζ => (hQm l).comp measurable_prodMk_right
  have houter : ∀ l, Measurable fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) t, Q l (r, ζ) := fun l =>
    ((hQm l).comp measurable_swap).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
  calc ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (B.Mq N t ζ)) ^ 2) ∂(R N).P
      = ∑' l, ∫⁻ ζ, ENNReal.ofReal ((HNeg.pairing (φl l) (B.Mq N t ζ)) ^ 2) ∂(R N).P :=
        lintegral_tsum fun l => (hmeas l).aemeasurable
    _ = ∑' l, ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, Q l (r, ζ)) ∂(R N).P := tsum_congr hcoord
    _ = ∫⁻ ζ, ∑' l, (∫⁻ r in Set.Icc (0 : ℝ) t, Q l (r, ζ)) ∂(R N).P :=
        (lintegral_tsum fun l => (houter l).aemeasurable).symm
    _ = ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) t, ∑' l, Q l (r, ζ)) ∂(R N).P := by
        refine lintegral_congr fun ζ => (lintegral_tsum fun l => (hinner l ζ).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun ζ => lintegral_congr fun r => ?_
        simp only [hQ]
        rw [Summable.tsum_finsetSum fun ia _ => ENNReal.summable]
        refine Finset.sum_congr rfl fun ia _ => ?_
        rw [ENNReal.tsum_mul_left]
        rfl

end Itô

end HRS.MS.MainRdPath
