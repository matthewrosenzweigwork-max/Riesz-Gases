import HRS.MS.S81qOldBlock
import HRS.MS.S81w2GradB
import HRS.MS.FinNoiseAux2
import HRS.MS.FinNoiseAux5
import HRS.MH.DualityRdA3

/-!
# S8.1 (worker S81Q): physical identification of the old current

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

Analytic ingredients: the first-marginal bound along the enlargement (`s81q_marginal_le`), the tail of the weighted orbit series
(`s81q_tail_tendsto`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
open HRS HRS.Whole HRS.MS.SuppU11 HRS.MS.Spec HRS.Whole.S81P HRS.Whole.S81W2 HRS.MS.S88Breakdown

namespace HRS.Whole.S81Q

section Marginal

variable {d : ℕ}

/-- Along a measure preserving enlargement the law of each particle is the canonical first marginal, whose density with respect to `μ` is bounded. -/
theorem s81q_marginal_le {a β : ℝ} {N : ℕ} (hN : 2 ≤ N) {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} {π : Ω' → Ω}
    (hπ : MeasurePreserving π P' P) {X : ℝ≥0 → Ω → EucConfig d N}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    (hreal : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X)
    {Cs : ℝ} (hSN : S45.S45Static d ((d : ℝ) / 2) a β Cs N) (r : ℝ) (hr : 0 ≤ r) (i : Fin N)
    (g : Euc d → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ w, g (X (Real.toNNReal r) (π w) i) ∂P' ≤
      ENNReal.ofReal Cs * ∫⁻ x, g x ∂(thermalMeasure d ((d : ℝ) / 2) a β) := by
  have hN0 : 0 < N := by omega
  have hXm : Measurable fun z => X (Real.toNNReal r) z i :=
    (measurable_pi_apply i).comp ((hreal.solution r).adapted (Real.toNNReal r))
  have e1 : ∫⁻ w, g (X (Real.toNNReal r) (π w) i) ∂P' = ∫⁻ z, g (X (Real.toNNReal r) z i) ∂P :=
    hπ.lintegral_comp (hg.comp hXm)
  rw [e1, ← lintegral_map hg hXm]
  have hmap : P.map (fun z => X (Real.toNNReal r) z i) =
      HRS.Whole.firstMarginal (HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2))
        (confinement a) N β) := by
    have h1 : P.map (fun z => X (Real.toNNReal r) z i) =
        (P.map (X (Real.toNNReal r))).map (fun Y => Y i) := by
      rw [Measure.map_map (measurable_pi_apply i) ((hreal.solution r).adapted (Real.toNNReal r))]
      rfl
    rw [h1, HRS.Whole.S79.s79_law_X_eq hreal (Real.toNNReal r)]
    exact s8p_map_eval hN0 hSN.exch i
  rw [hmap]
  obtain ⟨φ, hφm, hφ, hφb, -, -⟩ := hSN.marg
  rw [hφ, lintegral_withDensity_eq_lintegral_mul _ hφm.ennreal_ofReal hg]
  rw [← lintegral_const_mul _ hg]
  refine lintegral_mono fun x => ?_
  show ENNReal.ofReal (φ x) * g x ≤ ENNReal.ofReal Cs * g x
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hφb x).2) le_rfl

end Marginal

section Tail

/-- The tail of a summable series tends to zero, in `ℝ≥0∞`. -/
theorem s81q_tail_tendsto {g : ℕ → ℝ} (hg0 : ∀ l, 0 ≤ g l) (hg : Summable g) :
    Tendsto (fun L : ℕ => ∑' l, ENNReal.ofReal (g (l + L))) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add g
  have e : ∀ L : ℕ, ∑' l, ENNReal.ofReal (g (l + L)) = ENNReal.ofReal (∑' l, g (l + L)) := fun L =>
    (ENNReal.ofReal_tsum_of_nonneg (fun l => hg0 _) (hg.comp_injective (add_left_injective L))).symm
  simp_rw [e]
  simpa using (ENNReal.tendsto_ofReal h)

end Tail

section Pointwise

variable {d : ℕ}

/-- The spectral empirical noise integrand at a configuration. -/
def s81q_PhiAt {N : ℕ} (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (Y : EucConfig d N)
    (ia : Fin N × Fin d) : SeqL2 :=
  Real.sqrt (2 / (N * β)) • SeqL2.ofSeq (fun l =>
    Real.exp (-(τ * om l) / 2) * gradient (e l) (Y ia.1) ia.2)

/-- The set of points where the spectral gradient vector is square summable. -/
def s81q_good (τ : ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) : Set (Euc d) :=
  {x | ∀ i : Fin d, Summable fun l => (Real.exp (-(τ * om l) / 2) * gradient (e l) x i) ^ 2}

theorem s81q_good_meas (τ : ℝ) {e : ℕ → Euc d → ℝ} (he : ∀ l, ContDiff ℝ ∞ (e l)) (om : ℕ → ℝ) :
    MeasurableSet (s81q_good τ e om) := by
  have : s81q_good τ e om = ⋂ i : Fin d, {x | Summable fun l =>
      (Real.exp (-(τ * om l) / 2) * gradient (e l) x i) ^ 2} := by
    ext x; simp [s81q_good]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  refine HRS.Q41.q41_measurableSet_summable (fun (l : ℕ) (x : Euc d) =>
    (Real.exp (-(τ * om l) / 2) * gradient (e l) x i) ^ 2) (fun l => ?_) (fun l x => sq_nonneg _)
  have h1 : Continuous fun x => gradient (e l) x := s81w2_gradient_continuous (he l)
  exact (measurable_const.mul ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable.comp
    h1.measurable)).pow_const 2

theorem s81q_PhiAt_coord {N : ℕ} (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (Y : EucConfig d N)
    (ia : Fin N × Fin d) (hY : Y ia.1 ∈ s81q_good τ e om) (l : ℕ) :
    inner ℝ (s81q_PhiAt β τ e om Y ia) (S45.s45_seqBasis l) =
      Real.sqrt (2 / (N * β)) * (Real.exp (-(τ * om l) / 2) * gradient (e l) (Y ia.1) ia.2) := by
  rw [s8p_inner_basis]
  unfold s81q_PhiAt
  rw [s8p_coord_smul]
  rw [u11_coord_ofSeq (memℓp_two_iff.2 (hY ia.2))]

end Pointwise

section Slice

variable {d : ℕ}

/-- The remainder of the gradient expansion of the orbit `U_s φ_α`. -/
def s81q_Gs (C : WholeCoeff d) (m : ℝ) (α : MultiIndex d) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ)
    (coef : ℕ → ℝ) (s : ℝ) (L : ℕ) (x : Euc d) : Euc d :=
  gradient (s88Orbit C m s α) x - ∑ l ∈ Finset.range L, (Real.exp (-s * om l) * coef l) • gradient (e l) x

/-- The tail of the gradient closure. -/
def s81q_tail (om : ℕ → ℝ) (coef : ℕ → ℝ) (s : ℝ) (L : ℕ) : ℝ :=
  ∑' l, om (l + L) * (Real.exp (-s * om (l + L)) * coef (l + L)) ^ 2

theorem s81q_norm_sq_euc (x : Euc d) : ‖x‖ ^ 2 = ∑ a : Fin d, (x a) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun a _ => by rw [Real.norm_eq_abs, sq_abs]

/-- The `L²` bound of a slice: the gradient error of the finite spectral sum at the particles. -/
theorem s81q_slice {N : ℕ} (hN : 1 ≤ N) {β : ℝ} (hβ : 0 < β) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] {Cs : ℝ} (μ : Measure (Euc d))
    (Y : Ω' → EucConfig d N) (hYm : ∀ i, Measurable fun w => Y w i)
    (hmarg : ∀ (i : Fin N) (g : Euc d → ℝ≥0∞), Measurable g →
      ∫⁻ w, g (Y w i) ∂P' ≤ ENNReal.ofReal Cs * ∫⁻ x, g x ∂μ)
    (G : Euc d → Euc d) (hG : Measurable G) :
    ∫⁻ w, ∑ ia : Fin N × Fin d, ENNReal.ofReal (2 / (N * β) * (G (Y w ia.1) ia.2) ^ 2) ∂P' ≤
      ENNReal.ofReal (2 * Cs / β) * ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ := by
  have hK : 0 ≤ 2 / ((N : ℝ) * β) := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ∀ w, ∑ ia : Fin N × Fin d, ENNReal.ofReal (2 / (N * β) * (G (Y w ia.1) ia.2) ^ 2) =
      ENNReal.ofReal (2 / (N * β)) * ∑ i : Fin N, ENNReal.ofReal (‖G (Y w i)‖ ^ 2) := by
    intro w
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s81q_norm_sq_euc, ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _), Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [ENNReal.ofReal_mul hK]
  simp_rw [e1]
  have hm : ∀ i : Fin N, Measurable fun w => ENNReal.ofReal (‖G (Y w i)‖ ^ 2) := fun i =>
    ENNReal.measurable_ofReal.comp (((hG.comp (hYm i)).norm).pow_const 2)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ fun i _ => hm i]
  have hgm : Measurable fun x => ENNReal.ofReal (‖G x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hG.norm).pow_const 2)
  calc ENNReal.ofReal (2 / (N * β)) * ∑ i : Fin N, ∫⁻ w, ENNReal.ofReal (‖G (Y w i)‖ ^ 2) ∂P'
      ≤ ENNReal.ofReal (2 / (N * β)) * ∑ i : Fin N,
          (ENNReal.ofReal Cs * ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hmarg i _ hgm)
    _ = ENNReal.ofReal (2 * Cs / β) * ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        by_cases hCs : 0 ≤ Cs
        · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hK,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
        · have : ENNReal.ofReal Cs = 0 := ENNReal.ofReal_of_nonpos (not_le.1 hCs).le
          have h2 : ENNReal.ofReal (2 * Cs / β) = 0 := by
            apply ENNReal.ofReal_of_nonpos
            have : 2 * Cs / β ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.1 hCs]) hβ.le
            exact this
          simp [this, h2]

end Slice

section Pointwise2

variable {d : ℕ}

/-- The finite spectral sum of the weighted coordinate integrands, at a configuration. -/
def s81q_xiL {N : ℕ} (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (coef : ℕ → ℝ) (b t h : ℝ)
    (L : ℕ) (r : ℝ) (Y : EucConfig d N) (ia : Fin N × Fin d) : ℝ :=
  ∑ l ∈ Finset.range L, (coef l * Real.exp (-(b + t - τ / 2) * om l)) *
    (s81q_fcl om h l r * inner ℝ (s81q_PhiAt β τ e om Y ia) (S45.s45_seqBasis l))

/-- At good configurations the finite spectral sum is the finite gradient expansion. -/
theorem s81q_xiL_eq {N : ℕ} (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (coef : ℕ → ℝ) (b t h : ℝ)
    (L : ℕ) {r : ℝ} (hr : r ≤ h) (Y : EucConfig d N) (ia : Fin N × Fin d)
    (hY : Y ia.1 ∈ s81q_good τ e om) :
    s81q_xiL β τ e om coef b t h L r Y ia = Real.sqrt (2 / (N * β)) *
      ∑ l ∈ Finset.range L, (Real.exp (-(b + h + t - r) * om l) * coef l) * gradient (e l) (Y ia.1) ia.2 := by
  unfold s81q_xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [s81q_PhiAt_coord β τ e om Y ia hY l]
  unfold s81q_fcl
  rw [min_eq_left hr]
  have : Real.exp (-(b + t - τ / 2) * om l) * Real.exp (-(h - r) * om l) *
      Real.exp (-(τ * om l) / 2) = Real.exp (-(b + h + t - r) * om l) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc coef l * Real.exp (-(b + t - τ / 2) * om l) *
        (Real.exp (-(h - r) * om l) * (Real.sqrt (2 / (N * β)) *
          (Real.exp (-(τ * om l) / 2) * gradient (e l) (Y ia.1) ia.2)))
      = Real.sqrt (2 / (N * β)) * (coef l * (Real.exp (-(b + t - τ / 2) * om l) *
          Real.exp (-(h - r) * om l) * Real.exp (-(τ * om l) / 2)) * gradient (e l) (Y ia.1) ia.2) := by
        ring
    _ = _ := by rw [this]; ring

end Pointwise2

section Slice2

variable {d : ℕ}

theorem s81q_slice_r {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] {Cs : ℝ} (μ : Measure (Euc d))
    (Y : Ω' → EucConfig d N) (hYm : ∀ i, Measurable fun w => Y w i)
    (hmarg : ∀ (i : Fin N) (g : Euc d → ℝ≥0∞), Measurable g →
      ∫⁻ w, g (Y w i) ∂P' ≤ ENNReal.ofReal Cs * ∫⁻ x, g x ∂μ)
    (G : Euc d → Euc d) (hG : Measurable G) (u v : Ω' → Fin N × Fin d → ℝ)
    (huv : ∀ᵐ w ∂P', ∀ ia, u w ia - v w ia = -(Real.sqrt (2 / (N * β)) * G (Y w ia.1) ia.2)) :
    ∫⁻ w, ∑ ia : Fin N × Fin d, ‖u w ia - v w ia‖ₑ ^ 2 ∂P' ≤
      ENNReal.ofReal (2 * Cs / β) * ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ := by
  refine le_trans (le_of_eq ?_) (s81q_slice (by omega) hβ P' μ Y hYm hmarg G hG)
  refine lintegral_congr_ae ?_
  filter_upwards [huv] with w hw
  refine Finset.sum_congr rfl fun ia _ => ?_
  rw [hw ia, s8p_enorm_sq_eq, neg_sq, mul_pow, Real.sq_sqrt (by positivity)]

end Slice2

section Total

variable {d : ℕ}

/-- Exchange the order of the `ω` and the time integral and bound slice by slice. -/
theorem s81q_total_swap {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {h : ℝ} (F : ℝ → Ω' → ℝ≥0∞) (hF : Measurable fun q : Ω' × ℝ => F q.2 q.1) (ub : ℝ → ℝ≥0∞)
    (hslice : ∀ r ∈ Set.Ioc (0 : ℝ) h, ∫⁻ w, F r w ∂P' ≤ ub r) :
    ∫⁻ w, (∫⁻ r in Set.Icc 0 h, F r w) ∂P' ≤ ∫⁻ r in Set.Icc 0 h, ub r := by
  rw [lintegral_lintegral_swap hF.aemeasurable]
  rw [← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := h) (μ := volume)),
    ← setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := h) (μ := volume))]
  exact setLIntegral_mono' measurableSet_Ioc hslice

end Total

section Prog

variable {d : ℕ}

theorem s81q_xiL_prog {N : ℕ} {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {ℱ' : Filtration ℝ mΩ'}
    (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om coef : ℕ → ℝ) (b t h : ℝ) (L : ℕ)
    (Yp : ℝ → Ω' → EucConfig d N) (ia : Fin N × Fin d)
    (hΦprog : ∀ l : ℕ, IsProgressive ℱ' (fun r w =>
      inner ℝ (s81q_PhiAt β τ e om (Yp r w) ia) (S45.s45_seqBasis l))) :
    IsProgressive ℱ' (fun r w => s81q_xiL β τ e om coef b t h L r (Yp r w) ia) := by
  intro i
  unfold s81q_xiL
  refine Finset.measurable_sum _ fun l _ => ?_
  refine measurable_const.mul (Measurable.mul ?_ (hΦprog l i))
  exact (s81q_fcl_cont om h l).measurable.comp (measurable_subtype_coe.comp measurable_fst)

end Prog

section Fx

variable {d : ℕ}

/-- The difference of the finite spectral sum and the physical old integrand. -/
def s81q_Fx {N : ℕ} {Ω' : Type} (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om coef : ℕ → ℝ) (b t h : ℝ) (L : ℕ)
    (v : ℝ) (f : ℝ → Euc d → ℝ) (Xp : ℝ≥0 → Ω' → EucConfig d N) :
    ℝ → Ω' → Fin N × Fin d → ℝ := fun r w ia =>
  s81q_xiL β τ e om coef b t h L r (Xp (Real.toNNReal r) w) ia -
    Real.sqrt (2 / (N * β)) * HRS.MH.DualityRd.truncGradIntegrand v f Xp r w ia

theorem s81q_Fx_meas {N : ℕ} {Ω' : Type} {mΩ' : MeasurableSpace Ω'} {ℱ' : Filtration ℝ mΩ'}
    (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om coef : ℕ → ℝ) (b t h : ℝ) (L : ℕ) (v : ℝ)
    (f : ℝ → Euc d → ℝ) (Xp : ℝ≥0 → Ω' → EucConfig d N)
    (hΦprog : ∀ (l : ℕ) (ia : Fin N × Fin d), IsProgressive ℱ' (fun r w =>
      inner ℝ (s81q_PhiAt β τ e om (Xp (Real.toNNReal r) w) ia) (S45.s45_seqBasis l)))
    (hphprog : ∀ ia : Fin N × Fin d, IsProgressive ℱ' (fun r w =>
      HRS.MH.DualityRd.truncGradIntegrand v f Xp r w ia)) :
    ∀ ia : Fin N × Fin d, Measurable fun q : Ω' × ℝ =>
      ‖s81q_Fx β τ e om coef b t h L v f Xp q.2 q.1 ia‖ₑ ^ 2 := by
  intro ia
  have hprog : IsProgressive ℱ' (fun r w => s81q_Fx β τ e om coef b t h L v f Xp r w ia) := fun i =>
    ((s81q_xiL_prog β τ e om coef b t h L (fun r w => Xp (Real.toNNReal r) w) ia
      (fun l => hΦprog l ia)) i).sub (measurable_const.mul (hphprog ia i))
  exact (((HRS.MRep.isProgressive_measurable_uncurry hprog).comp measurable_swap).enorm).pow_const 2

/-- Pointwise: at good configurations the difference is minus the gradient remainder. -/
theorem s81q_Fx_pt {N : ℕ} {Ω' : Type} (β τ : ℝ) (e : ℕ → Euc d → ℝ) (om coef : ℕ → ℝ)
    (b t h : ℝ) (L : ℕ) (C : WholeCoeff d) (m : ℝ) (α : MultiIndex d)
    (Xp : ℝ≥0 → Ω' → EucConfig d N) {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ h) (ht : 0 ≤ t) (hb0 : 0 ≤ b)
    (hshift : propagatorW C r (b + h + t) (oscTestFun m α) =
      propagatorW C 0 (b + h + t - r) (oscTestFun m α)) (w : Ω')
    (hw : ∀ i, Xp (Real.toNNReal r) w i ∈ s81q_good τ e om) (ia : Fin N × Fin d) :
    s81q_Fx β τ e om coef b t h L (b + h + t) (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α))
        Xp r w ia =
      -(Real.sqrt (2 / (N * β)) *
        (s81q_Gs C m α e om coef (b + h + t - r) L (Xp (Real.toNNReal r) w ia.1)) ia.2) := by
  unfold s81q_Fx
  rw [s81q_xiL_eq β τ e om coef b t h L hrh _ ia (hw ia.1)]
  unfold HRS.MH.DualityRd.truncGradIntegrand s81q_Gs
  rw [if_pos ⟨hr0, by linarith⟩]
  show _ - _ * gradient (propagatorW C r (b + h + t) (oscTestFun m α)) _ ia.2 = _
  rw [hshift]
  show _ - _ * gradient (propagatorW C 0 (b + h + t - r) (oscTestFun m α)) _ ia.2 = _
  show _ - _ * gradient (s88Orbit C m (b + h + t - r) α) _ ia.2 = _
  simp only [PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end Fx

section Tot2

theorem s81q_sum_swap {ι : Type} [Fintype ι] {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (h : ℝ) (g : ι → ℝ → Ω' → ℝ≥0∞) (hg : ∀ i, Measurable fun q : Ω' × ℝ => g i q.2 q.1) :
    ∑ i, ∫⁻ w, (∫⁻ r in Set.Icc 0 h, g i r w) ∂P' =
      ∫⁻ w, (∫⁻ r in Set.Icc 0 h, ∑ i, g i r w) ∂P' := by
  have hA : ∀ i, Measurable fun w => ∫⁻ r in Set.Icc 0 h, g i r w := fun i =>
    (hg i).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 h))
  have hR : ∀ (w : Ω') (i : ι), Measurable fun r => g i r w := fun w i =>
    (hg i).comp (measurable_prodMk_left (x := w))
  rw [← lintegral_finsetSum _ fun i _ => hA i]
  refine lintegral_congr fun w => ?_
  rw [lintegral_finsetSum _ fun i _ => hR w i]

end Tot2

section L2

variable {d : ℕ}

/-- a.e. goodness of the particles along the enlargement. -/
theorem s81q_ae_good {N : ℕ} {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') {Cs : ℝ}
    (μ : Measure (Euc d)) (Y : Ω' → EucConfig d N) (hYm : ∀ i, Measurable fun w => Y w i)
    (hmarg : ∀ (i : Fin N) (g : Euc d → ℝ≥0∞), Measurable g →
      ∫⁻ w, g (Y w i) ∂P' ≤ ENNReal.ofReal Cs * ∫⁻ x, g x ∂μ)
    (S : Set (Euc d)) (hS : MeasurableSet S) (hμ : μ Sᶜ = 0) : ∀ᵐ w ∂P', ∀ i, Y w i ∈ S := by
  refine ae_all_iff.2 fun i => ?_
  have h1 := hmarg i (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hS.compl)
  rw [lintegral_indicator_const hS.compl, hμ, mul_zero, mul_zero] at h1
  have h2 : ∫⁻ w, (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (Y w i) ∂P' = 0 := le_antisymm (by simpa using h1) bot_le
  have hm2 : Measurable fun w => (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (Y w i) :=
    (measurable_const.indicator hS.compl).comp (hYm i)
  have h3 := (lintegral_eq_zero_iff hm2).1 h2
  filter_upwards [h3] with w hw
  by_contra hc
  have : (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (Y w i) = 1 := Set.indicator_of_mem hc _
  simp [this] at hw

set_option maxHeartbeats 800000 in
/-- **The `L²` error of the finite spectral approximation of the physical old integrand.** -/
theorem s81q_phys_L2 {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) {Ω' : Type}
    {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') [IsProbabilityMeasure P'] {ℱ' : Filtration ℝ mΩ'}
    {Cs : ℝ} (μ : Measure (Euc d)) (Xp : ℝ≥0 → Ω' → EucConfig d N)
    (hXm : ∀ s i, Measurable fun w => Xp s w i)
    (hmarg : ∀ r : ℝ, 0 ≤ r → ∀ (i : Fin N) (g : Euc d → ℝ≥0∞), Measurable g →
      ∫⁻ w, g (Xp (Real.toNNReal r) w i) ∂P' ≤ ENNReal.ofReal Cs * ∫⁻ x, g x ∂μ)
    {τ : ℝ} {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ} (hgoodm : MeasurableSet (s81q_good τ e om))
    (hgoodμ : μ (s81q_good τ e om)ᶜ = 0) (C : WholeCoeff d) (m : ℝ) (α : MultiIndex d)
    (coef : ℕ → ℝ) {b h t : ℝ} (hb0 : 0 < b) (hh : 0 ≤ h) (ht : 0 ≤ t)
    (hGm : ∀ s : ℝ, 0 < s → ∀ L, Measurable (s81q_Gs C m α e om coef s L))
    (hcl : ∀ s : ℝ, 0 < s → ∀ L : ℕ, ∫⁻ x, ENNReal.ofReal (‖s81q_Gs C m α e om coef s L x‖ ^ 2) ∂μ =
      ENNReal.ofReal (s81q_tail om coef s L))
    (hshift : ∀ r ∈ Set.Icc (0 : ℝ) (b + h + t), propagatorW C r (b + h + t) (oscTestFun m α) =
      propagatorW C 0 (b + h + t - r) (oscTestFun m α))
    (hΦprog : ∀ (l : ℕ) (ia : Fin N × Fin d), IsProgressive ℱ' (fun r w =>
      inner ℝ (s81q_PhiAt β τ e om (Xp (Real.toNNReal r) w) ia) (S45.s45_seqBasis l)))
    (hphprog : ∀ ia : Fin N × Fin d, IsProgressive ℱ' (fun r w =>
      HRS.MH.DualityRd.truncGradIntegrand (b + h + t)
        (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp r w ia))
    (L : ℕ) :
    ∑ ia : Fin N × Fin d, ∫⁻ w, (∫⁻ r in Set.Icc 0 h,
      ‖s81q_Fx β τ e om coef b t h L (b + h + t)
        (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp r w ia‖ₑ ^ 2) ∂P' ≤
      ENNReal.ofReal (2 * Cs / β) * ∫⁻ r in Set.Icc 0 h,
        ENNReal.ofReal (s81q_tail om coef (b + h + t - r) L) := by
  have hjm := s81q_Fx_meas β τ e om coef b t h L (b + h + t)
    (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp hΦprog hphprog
  -- exchange the finite sum
  rw [s81q_sum_swap P' h (fun ia r w => ‖s81q_Fx β τ e om coef b t h L (b + h + t)
    (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp r w ia‖ₑ ^ 2) hjm]
  have hFm : Measurable fun q : Ω' × ℝ => ∑ ia : Fin N × Fin d,
      ‖s81q_Fx β τ e om coef b t h L (b + h + t)
        (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp q.2 q.1 ia‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun ia _ => hjm ia
  refine le_trans (s81q_total_swap P' (h := h) (fun r w => ∑ ia : Fin N × Fin d,
    ‖s81q_Fx β τ e om coef b t h L (b + h + t)
      (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp r w ia‖ₑ ^ 2) hFm
    (fun r => ENNReal.ofReal (2 * Cs / β) * ENNReal.ofReal (s81q_tail om coef (b + h + t - r) L))
    ?_) (le_of_eq ?_)
  · intro r hr
    have hr0 : 0 ≤ r := hr.1.le
    have hgoodae := s81q_ae_good P' μ (fun w => Xp (Real.toNNReal r) w) (fun i => hXm _ i)
      (fun i g hg => hmarg r hr0 i g hg) _ hgoodm hgoodμ
    have hslice := s81q_slice_r hN hβ P' μ (fun w => Xp (Real.toNNReal r) w) (fun i => hXm _ i)
      (fun i g hg => hmarg r hr0 i g hg) (s81q_Gs C m α e om coef (b + h + t - r) L) (hGm _ (by linarith [hr.1, hr.2]) _)
      (fun w ia => s81q_xiL β τ e om coef b t h L r (Xp (Real.toNNReal r) w) ia)
      (fun w ia => Real.sqrt (2 / (N * β)) *
        HRS.MH.DualityRd.truncGradIntegrand (b + h + t)
          (fun r' => propagatorW C r' (b + h + t) (oscTestFun m α)) Xp r w ia)
      (by
        filter_upwards [hgoodae] with w hw ia
        exact s81q_Fx_pt β τ e om coef b t h L C m α Xp hr0 hr.2 ht hb0.le
          (hshift r ⟨hr0, by linarith [hr.2]⟩) w hw ia)
    refine hslice.trans ?_
    rw [hcl _ (by linarith [hr.2]) L]
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end L2

section TailInt

/-- The time integral of the closure tails tends to zero. -/
theorem s81q_tail_int_tendsto {om coef : ℕ → ℝ} (hom : ∀ l, 0 < om l)
    (hcs : Summable fun l => coef l ^ 2)
    (hsumω : ∀ s : ℝ, 0 < s → Summable fun l => om l * (Real.exp (-s * om l) * coef l) ^ 2)
    {b h t : ℝ} (hb0 : 0 < b) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    Tendsto (fun L : ℕ => ∫⁻ r in Set.Icc 0 h,
      ENNReal.ofReal (s81q_tail om coef (b + h + t - r) L)) atTop (𝓝 0) := by
  set g : ℕ → ℝ := fun k => coef k ^ 2 * Real.exp (-2 * (b + t) * om k) / 2 with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun k => ?_) (hcs.mul_right (1 / 2 : ℝ))
    have h1 : Real.exp (-2 * (b + t) * om k) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := hom k; nlinarith
    have := sq_nonneg (coef k)
    show coef k ^ 2 * Real.exp (-2 * (b + t) * om k) / 2 ≤ coef k ^ 2 * (1 / 2)
    nlinarith
  have hterm : ∀ (L : ℕ) (r : ℝ), r ∈ Set.Icc 0 h →
      ENNReal.ofReal (s81q_tail om coef (b + h + t - r) L) =
        ∑' l, ENNReal.ofReal (om (l + L) * (Real.exp (-(b + h + t - r) * om (l + L)) *
          coef (l + L)) ^ 2) := by
    intro L r hr
    unfold s81q_tail
    have hs : Summable fun l => om (l + L) *
        (Real.exp (-(b + h + t - r) * om (l + L)) * coef (l + L)) ^ 2 :=
      (hsumω (b + h + t - r) (by linarith [hr.2])).comp_injective (add_left_injective L)
    rw [ENNReal.ofReal_tsum_of_nonneg (fun l => mul_nonneg (hom _).le (sq_nonneg _)) hs]
  have hint : ∀ L : ℕ, ∫⁻ r in Set.Icc 0 h, ENNReal.ofReal (s81q_tail om coef (b + h + t - r) L) ≤
      ∑' l, ENNReal.ofReal (g (l + L)) := by
    intro L
    calc ∫⁻ r in Set.Icc 0 h, ENNReal.ofReal (s81q_tail om coef (b + h + t - r) L)
        = ∫⁻ r in Set.Icc 0 h, ∑' l, ENNReal.ofReal (om (l + L) *
            (Real.exp (-(b + h + t - r) * om (l + L)) * coef (l + L)) ^ 2) :=
          setLIntegral_congr_fun measurableSet_Icc fun r hr => hterm L r hr
      _ = ∑' l, ∫⁻ r in Set.Icc 0 h, ENNReal.ofReal (om (l + L) *
            (Real.exp (-(b + h + t - r) * om (l + L)) * coef (l + L)) ^ 2) := by
          refine lintegral_tsum fun l => ?_
          refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
          fun_prop
      _ ≤ ∑' l, ENNReal.ofReal (g (l + L)) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          have hw := hom (l + L)
          have e : ∀ r ∈ Set.Icc (0 : ℝ) h, ENNReal.ofReal (om (l + L) *
              (Real.exp (-(b + h + t - r) * om (l + L)) * coef (l + L)) ^ 2) =
              ENNReal.ofReal (om (l + L) * coef (l + L) ^ 2 * Real.exp (-2 * (b + t) * om (l + L))) *
                ENNReal.ofReal (Real.exp (-((2 * om (l + L)) * (h - r)))) := by
            intro r hr
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have : Real.exp (-(b + h + t - r) * om (l + L)) ^ 2 =
                Real.exp (-2 * (b + t) * om (l + L)) * Real.exp (-((2 * om (l + L)) * (h - r))) := by
              rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
            rw [mul_pow, this]; ring
          rw [setLIntegral_congr_fun measurableSet_Icc e,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine (mul_le_mul' le_rfl (s8p_lintegral_exp_le (c := 2 * om (l + L)) (by positivity) hh)).trans ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
          simp only [hg]
          field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (s81q_tail_tendsto hg0 hgs)
    (fun L => bot_le) hint

end TailInt

section Ident

variable {d : ℕ}

set_option maxHeartbeats 800000 in
/-- **Identification of an `L²`-limit of weighted coordinate integrals.**  If `Y_l = JW_l(h)` are the weighted coordinate integrals of the
spectral noise, the finite sums `∑_{l<L} a_l JW_l(h)` are the Itô integrals of `ξL`; if `ξL → ξph` in `L²(dt ⊗ dP)` then `∑' a_l Y_l` is the Itô
integral of `ξph`. -/
theorem s81q_phys_ident {N : ℕ} {Ω' : Type} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω')
    [IsProbabilityMeasure P'] {ℱ' : Filtration ℝ mΩ'} {Wtil : ℝ≥0 → Ω' → Fin N × Fin d → ℝ}
    (hWb : IsCylindricalBrownian P' ℱ' Wtil) {h : ℝ} (hh : 0 ≤ h) (a : ℕ → ℝ)
    (hasq : Summable fun l => a l ^ 2) (ξ : ℕ → ℝ → Ω' → Fin N × Fin d → ℝ)
    (hξ : ∀ l, IsCtbl P' ℱ' (ξ l)) (JW : ℕ → ℝ → Ω' → ℝ)
    (hJW : ∀ l, IsItoC P' ℱ' Wtil (ξ l) (JW l)) (ξph : ℝ → Ω' → Fin N × Fin d → ℝ)
    (hξph : IsCtbl P' ℱ' ξph) (Yn : Ω' → SeqL2) (hYn2 : ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P' ≠ ⊤)
    (hY : ∀ l, (fun w => SeqL2.coord (Yn w) l) =ᵐ[P'] JW l h) (Ωt : Ω' → ℝ)
    (hΩm : Measurable Ωt) (hΩ : ∀ w, Ωt w = ∑' l, a l * SeqL2.coord (Yn w) l)
    (Bnd : ℕ → ℝ≥0∞) (hBnd : Tendsto Bnd atTop (𝓝 0))
    (hbound : ∀ L : ℕ, ∑ ia : Fin N × Fin d, ∫⁻ w, (∫⁻ r in Set.Icc 0 h,
      ‖(∑ l ∈ Finset.range L, a l * ξ l r w ia) - ξph r w ia‖ₑ ^ 2) ∂P' ≤ Bnd L) :
    ∃ JO : ℝ → Ω' → ℝ, IsItoC P' ℱ' Wtil ξph JO ∧ Ωt =ᵐ[P'] JO h := by
  classical
  obtain ⟨JO, hJO⟩ := exists_isItoC hWb hξph
  refine ⟨JO, hJO, ?_⟩
  -- the finite sums
  have hfs : ∀ L : ℕ, IsCtbl P' ℱ' (fun r w ia => ∑ l ∈ Finset.range L, a l * ξ l r w ia) ∧
      IsItoC P' ℱ' Wtil (fun r w ia => ∑ l ∈ Finset.range L, a l * ξ l r w ia)
        (fun τ w => ∑ l ∈ Finset.range L, a l * JW l τ w) := by
    intro L
    have h1 := fun l (_ : l ∈ Finset.range L) => (hξ l).mul_bdd (w := fun _ (_ : Ω') => a l)
      (pc_isProgressive_det measurable_const) (C := |a l|) (fun _ _ => le_rfl)
    have h2 := fun l (_ : l ∈ Finset.range L) => IsItoC.smul hWb (hξ l) (a l) (hJW l)
    exact IsItoC.finset_sum hWb (Finset.range L) (fun l r w ia => a l * ξ l r w ia)
      (fun l τ w => a l * JW l τ w) h1 h2
  have hL2 : ∀ L : ℕ, ∫⁻ w, ‖(∑ l ∈ Finset.range L, a l * JW l h w) - JO h w‖ₑ ^ 2 ∂P' ≤ Bnd L := by
    intro L
    obtain ⟨hc, hi⟩ := hfs L
    have hdiff := IsItoC.sub hWb hc hξph hi hJO
    have hdc := s81q_isCtbl_sub hc hξph
    refine (IsItoC.lintegral_sq_le hdc hWb hdiff hh).trans ?_
    refine le_trans (le_of_eq ?_) (hbound L)
    rw [tsum_fintype]
    rfl
  -- the tail estimate
  set A : ℕ → ℝ := fun L => ∑' l, a (l + L) ^ 2 with hA
  have hA0 : Tendsto A atTop (𝓝 0) := tendsto_sum_nat_add (fun l => a l ^ 2)
  have hcs : ∀ w, ∀ L : ℕ, ‖Ωt w - ∑ l ∈ Finset.range L, a l * SeqL2.coord (Yn w) l‖ₑ ^ 2 ≤
      ENNReal.ofReal (A L) * ‖Yn w‖ₑ ^ 2 := by
    intro w L
    set y : ℕ → ℝ := fun l => SeqL2.coord (Yn w) l with hy
    have hys : Summable fun l => y l ^ 2 := u11_coord_summable (Yn w)
    have hsum : Summable fun l => a l * y l := (s8p_series_cs _ _ hasq hys).1
    have e1 : Ωt w - ∑ l ∈ Finset.range L, a l * y l = ∑' l, a (l + L) * y (l + L) := by
      rw [hΩ w, ← Summable.sum_add_tsum_nat_add L hsum]; ring
    have h2 := (s8p_series_cs (fun l => a (l + L)) (fun l => y (l + L))
      (hasq.comp_injective (add_left_injective L)) (hys.comp_injective (add_left_injective L))).2
    rw [e1, s8p_enorm_sq_eq, s8p_seq_enorm_sq]
    refine le_trans (ENNReal.ofReal_le_ofReal h2) ?_
    rw [ENNReal.ofReal_mul (tsum_nonneg fun l => sq_nonneg _)]
    refine mul_le_mul' le_rfl ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) hys]
    refine ENNReal.ofReal_le_ofReal ?_
    have htot := Summable.sum_add_tsum_nat_add L hys
    have := Finset.sum_nonneg (s := Finset.range L) (f := fun l => y l ^ 2) fun l _ => sq_nonneg _
    linarith
  have hJmeas : ∀ n : ℕ, Measurable fun w => ∑ l ∈ Finset.range n, a l * JW l h w := fun n =>
    Finset.measurable_sum _ fun l _ => measurable_const.mul
      (((hJW l).adapted h).mono (ℱ'.le h) le_rfl)
  refine s81q_ae_eq_of_L2 (a := fun n w => ∑ l ∈ Finset.range n, a l * JW l h w) hΩm.aemeasurable
    ((hJO.aemeasurable h)) (fun n => (hJmeas n).aemeasurable) ?_ ?_
  · -- convergence to `Ωt`
    have hle : ∀ n : ℕ, ∫⁻ w, ‖(∑ l ∈ Finset.range n, a l * JW l h w) - Ωt w‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (A n) * ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P' := by
      intro n
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hae : ∀ᵐ w ∂P', ∀ l, SeqL2.coord (Yn w) l = JW l h w := ae_all_iff.2 hY
      refine lintegral_mono_ae ?_
      filter_upwards [hae] with w hw
      have e : (∑ l ∈ Finset.range n, a l * JW l h w) =
          ∑ l ∈ Finset.range n, a l * SeqL2.coord (Yn w) l :=
        Finset.sum_congr rfl fun l _ => by rw [hw l]
      rw [e, enorm_sub_rev]
      exact hcs w n
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (A n) * ∫⁻ w, ‖Yn w‖ₑ ^ 2 ∂P') atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hA0) (Or.inr hYn2)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le) hle
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hBnd (fun n => bot_le) hL2

end Ident

end HRS.Whole.S81Q
